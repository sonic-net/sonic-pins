#include "tests/lib/switch_test_setup_helpers.h"

#include <cstdlib>
#include <memory>
#include <optional>
#include <queue>
#include <string>
#include <vector>

#include "absl/memory/memory.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "gmock/gmock.h"
#include "grpcpp/test/mock_stream.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "gutil/testing.h"
#include "lib/gnmi/gnmi_helper.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4/v1/p4runtime_mock.grpc.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/pd.h"
#include "p4_pdpi/testing/test_p4info.h"
#include "proto/gnmi/gnmi_mock.grpc.pb.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "thinkit/mock_switch.h"

namespace pins_test {
namespace {

using ::testing::_;
using ::testing::AnyNumber;
using ::testing::EqualsProto;
using ::testing::InSequence;
using ::testing::NiceMock;
using ::testing::Not;
using ::testing::Return;
using ::testing::ReturnRef;
using ::testing::StrictMock;
using ::testing::status::IsOk;

// One of the tables and actions from
// http://google3/blaze-out/genfiles/third_party/pins_infra/p4_pdpi/testing/test_p4info_embed.cc?l=13
// These need to correspond to the values in our p4info because it is checked
// when sequencing updates to clear tables on the switch.
constexpr uint32_t kTableId = 33554433;
constexpr uint32_t kActionId = 16777217;

// Any constant is fine here.
constexpr uint32_t kDeviceId = 100;

// This is the only action that will work everywhere.
constexpr p4::v1::SetForwardingPipelineConfigRequest::Action
    kForwardingPipelineAction =
        p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT;

p4::v1::Uint128 ConstructElectionId(
    const pdpi::P4RuntimeSessionOptionalArgs& metadata) {
  p4::v1::Uint128 election_id;
  election_id.set_high(absl::Uint128High64(metadata.election_id));
  election_id.set_low(absl::Uint128Low64(metadata.election_id));
  return election_id;
}

p4::v1::MasterArbitrationUpdate ConstructMasterArbitrationUpdate(
    const pdpi::P4RuntimeSessionOptionalArgs& metadata) {
  p4::v1::MasterArbitrationUpdate master_arbitration_update;
  *master_arbitration_update.mutable_election_id() =
      ConstructElectionId(metadata);
  master_arbitration_update.set_device_id(kDeviceId);
  master_arbitration_update.mutable_role()->set_name(metadata.role);
  return master_arbitration_update;
}

// Configures the given `MockP4RuntimeStub` such that the given sequence of
// table entries will be returned for the next P4RT Read request.
void SetNextReadResponse(p4::v1::MockP4RuntimeStub& mock_p4rt_stub,
                         std::vector<p4::v1::TableEntry> read_entries) {
  EXPECT_CALL(mock_p4rt_stub, ReadRaw)
      .WillOnce([read_entries = std::move(read_entries)](auto*, auto&) {
        auto* reader =
            new grpc::testing::MockClientReader<p4::v1::ReadResponse>();
        InSequence s;
        for (const auto& entry : read_entries) {
          EXPECT_CALL(*reader, Read)
              .WillOnce([=](p4::v1::ReadResponse* response) -> bool {
                *response->add_entities()->mutable_table_entry() = entry;
                return true;
              });
        }
        EXPECT_CALL(*reader, Read).WillOnce(Return(false));
        EXPECT_CALL(*reader, Finish).WillOnce(Return(grpc::Status::OK));
        return reader;
      });
}

// Mocks a P4RuntimeSession::Create call with a stub by constructing a
// ReaderWriter mock stream and mocking an arbitration handshake. This function
// does not perform any of these operations, it only sets up expectations.
void MockP4RuntimeSessionCreate(
    p4::v1::MockP4RuntimeStub& stub,
    const pdpi::P4RuntimeSessionOptionalArgs& metadata) {
  // The ReaderWriter stream constructed from the stub. This needs to be
  // malloced as it is automatically freed when the unique pointer that it will
  // be wrapped in is freed. The stream is wrapped in StreamChannel, which is
  // the method of the stub that calls StreamChannelRaw, but is not itself
  // mocked.
  auto* stream = new NiceMock<grpc::testing::MockClientReaderWriter<
      p4::v1::StreamMessageRequest, p4::v1::StreamMessageResponse>>();
  EXPECT_CALL(stub, StreamChannelRaw).WillOnce(Return(stream));

  // A valid MasterArbitrationUpdate sent as request and response.
  auto master_arbitration_update = ConstructMasterArbitrationUpdate(metadata);

  // Ensures that we write some sort of arbitration request...
  p4::v1::StreamMessageRequest arbitration_request;
  *arbitration_request.mutable_arbitration() = master_arbitration_update;
  EXPECT_CALL(*stream, Write(EqualsProto(arbitration_request), _))
      .WillOnce(Return(true));

  // ... and return a valid response.
  EXPECT_CALL(*stream, Read)
      .WillOnce([=](p4::v1::StreamMessageResponse* arbitration_response) {
        *arbitration_response->mutable_arbitration() =
            master_arbitration_update;
        return true;
      });
}

// Constructs a table entry using the predefined table id, kTableId, and action
// id, kActionId.
p4::v1::TableEntry ConstructTableEntry() {
  p4::v1::TableEntry table_entry;
  table_entry.set_table_id(kTableId);
  table_entry.mutable_action()->mutable_action()->set_action_id(kActionId);
  return table_entry;
}

// Sets up a write request to delete the given table entry.
p4::v1::WriteRequest ConstructDeleteRequest(
    const pdpi::P4RuntimeSessionOptionalArgs& metadata,
    const p4::v1::TableEntry& table_entry) {
  p4::v1::Update delete_update;
  delete_update.set_type(p4::v1::Update::DELETE);
  *delete_update.mutable_entity()->mutable_table_entry() = table_entry;

  p4::v1::WriteRequest delete_request;
  *delete_request.add_updates() = delete_update;
  delete_request.set_device_id(kDeviceId);
  delete_request.set_role(metadata.role);
  *delete_request.mutable_election_id() = ConstructElectionId(metadata);
  return delete_request;
}

// Mocks a `CheckNoEntries` call using the stub in a previously
// mocked P4RuntimeSession.
// Ensures that there are no table entries remaining.
void MockCheckNoEntries(p4::v1::MockP4RuntimeStub& stub) {
  // We need to return a p4info to get to the stage where we read tables.
  EXPECT_CALL(stub, GetForwardingPipelineConfig)
      .WillOnce([=](auto, auto,
                    p4::v1::GetForwardingPipelineConfigResponse*
                        get_pipeline_response) {
        get_pipeline_response->mutable_config()->mutable_p4info();
        return grpc::Status::OK;
      });

  SetNextReadResponse(stub, {});
}

// Mocks a `ClearTableEntries` call using the stub and p4info in a previously
// mocked P4RuntimeSession.
// Pulls the p4info from the switch, then reads a table entry, deletes it, and
// reads again ensuring that there are no table entries remaining.
void MockClearTableEntries(p4::v1::MockP4RuntimeStub& stub,
                           const p4::config::v1::P4Info& p4info,
                           const pdpi::P4RuntimeSessionOptionalArgs& metadata) {
  // We need to return a valid p4info to get to the stage where we read tables.
  EXPECT_CALL(stub, GetForwardingPipelineConfig)
      .WillOnce([=](auto, auto,
                    p4::v1::GetForwardingPipelineConfigResponse*
                        get_pipeline_response) {
        *get_pipeline_response->mutable_config()->mutable_p4info() = p4info;
        return grpc::Status::OK;
      });

  {
    InSequence s;
    p4::v1::TableEntry table_entry = ConstructTableEntry();

    // We return a table entry so that the function exercises the deletion
    // portion of clearing table entries.
    SetNextReadResponse(stub, {table_entry});

    // Mocks the call to delete table entry that we have created.
    EXPECT_CALL(
        stub,
        Write(_, EqualsProto(ConstructDeleteRequest(metadata, table_entry)), _))
        .Times(1);

    // Mocks a `CheckNoEntries` call, ensuring that the tables are really
    // cleared.
    MockCheckNoEntries(stub);
  }
}

// Sets up expectation that `ClearTableEntries(mock_switch, metadata)` is
// called.
void ExpectCallToClearTableEntries(
    thinkit::MockSwitch& mock_switch, const p4::config::v1::P4Info& p4info,
    const pdpi::P4RuntimeSessionOptionalArgs& metadata) {
  EXPECT_CALL(mock_switch, CreateP4RuntimeStub()).WillOnce([=] {
    InSequence s;
    auto stub = std::make_unique<::p4::v1::MockP4RuntimeStub>();
    MockP4RuntimeSessionCreate(*stub, metadata);
    MockClearTableEntries(*stub, p4info, metadata);
    return stub;
  });
}

// Mocks a successful `PushGnmiConfig` call.
void MockGnmiPush(gnmi::MockgNMIStub& mock_gnmi_stub) {
  EXPECT_CALL(mock_gnmi_stub, Set).WillOnce(Return(grpc::Status::OK));
}

// Sets up expectation that `pins_test::PushGnmiConfig(mock_switch, _)` is
// called.
void ExpectCallToPushGnmiConfig(thinkit::MockSwitch& mock_switch) {
  EXPECT_CALL(mock_switch, CreateGnmiStub).WillOnce([] {
    auto mock_gnmi_stub = absl::make_unique<gnmi::MockgNMIStub>();
    MockGnmiPush(*mock_gnmi_stub);
    return mock_gnmi_stub;
  });
}

// Mocks a successful `WaitForGnmiPortIdConvergence` call where the ports given
// by `interfaces` have converged.
void MockGnmiConvergence(
    gnmi::MockgNMIStub& mock_gnmi_stub,
    const std::vector<OpenConfigInterfaceDescription>& interfaces) {
  EXPECT_CALL(mock_gnmi_stub, Get)
      .WillOnce([=](auto, auto, gnmi::GetResponse* response) {
        *response->add_notification()
             ->add_update()
             ->mutable_val()
             ->mutable_json_ietf_val() =
            OpenConfigWithInterfaces(GnmiFieldType::kState, interfaces);
        return grpc::Status::OK;
      });
}

// Sets up expectation that
// `pins_test::WaitForGnmiPortIdConvergence(mock_switch, _, _)` is
// called, mocking response that the given`interfaces` have converged.
void ExpectCallToWaitForGnmiPortIdConvergence(
    thinkit::MockSwitch& mock_switch,
    const std::vector<OpenConfigInterfaceDescription>& interfaces) {
  EXPECT_CALL(mock_switch, CreateGnmiStub).WillOnce([=] {
    auto mock_gnmi_stub = absl::make_unique<gnmi::MockgNMIStub>();
    MockGnmiConvergence(*mock_gnmi_stub, interfaces);
    return mock_gnmi_stub;
  });
}

// Sets up expectation that
// `pins_test::ExpectCallToPushGnmiAndWaitForConvergence(mock_switch, _, _)` is
// called, mocking response that the given`interfaces` have converged.
void ExpectCallToPushGnmiAndWaitForConvergence(
    thinkit::MockSwitch& mock_switch,
    const std::vector<OpenConfigInterfaceDescription>& interfaces) {
  InSequence s;
  ExpectCallToPushGnmiConfig(mock_switch);
  ExpectCallToWaitForGnmiPortIdConvergence(mock_switch, interfaces);
}

// Constructs a valid forwarding pipeline config request with the given p4info
// and metadata.
p4::v1::SetForwardingPipelineConfigRequest
ConstructForwardingPipelineConfigRequest(
    const pdpi::P4RuntimeSessionOptionalArgs& metadata,
    const p4::config::v1::P4Info& p4info,
    absl::optional<absl::string_view> p4_device_config = absl::nullopt) {
  p4::v1::SetForwardingPipelineConfigRequest request;
  request.set_device_id(kDeviceId);
  request.set_role(metadata.role);
  *request.mutable_election_id() = ConstructElectionId(metadata);
  request.set_action(kForwardingPipelineAction);
  *request.mutable_config()->mutable_p4info() = p4info;
  if (p4_device_config.has_value()) {
    *request.mutable_config()->mutable_p4_device_config() = *p4_device_config;
  }
  return request;
}

void ExpectCallToCreateP4RuntimeSessionAndOptionallyPushP4Info(
    thinkit::MockSwitch& mock_switch,
    const std::optional<p4::config::v1::P4Info>& p4info,
    const pdpi::P4RuntimeSessionOptionalArgs& metadata) {
  EXPECT_CALL(mock_switch, CreateP4RuntimeStub).WillOnce([=] {
    InSequence s;
    auto stub = absl::make_unique<StrictMock<p4::v1::MockP4RuntimeStub>>();
    MockP4RuntimeSessionCreate(*stub, metadata);
    if (p4info.has_value()) {
      // TODO: Test the path where `GetForwardingPipelineConfig`
      // returns a non-empty P4Info.
      EXPECT_CALL(*stub, GetForwardingPipelineConfig).Times(1);
      EXPECT_CALL(*stub, SetForwardingPipelineConfig).Times(1);
    }
    MockCheckNoEntries(*stub);

    return stub;
  });
}

// Tests that ConfigureSwitchAndReturnP4RuntimeSession creates a
// P4RuntimeSession, clears all table entries currently on the switch (mocked
// to be one), pushes a gNMI config and converges (if config is given),
// and pushes a new P4Info (if P4Info is given).
void MockConfigureSwitchAndReturnP4RuntimeSession(
    thinkit::MockSwitch& mock_switch,
    // Using optional& against style-guide advice to avoid memory leak; these
    // arguments are used in setting up expectations, and need to outlive the
    // function call.
    const std::optional<std::string>& gnmi_config,
    const std::optional<p4::config::v1::P4Info>& p4info,
    const pdpi::P4RuntimeSessionOptionalArgs& metadata,
    const std::vector<OpenConfigInterfaceDescription>& interfaces) {
  // DeviceId and ChassisName may get called multiple times. The only important
  // point is that they always return the same response.
  ON_CALL(mock_switch, DeviceId).WillByDefault(Return(kDeviceId));
  EXPECT_CALL(mock_switch, DeviceId).Times(AnyNumber());

  // Required so that the reference below is not to a local variable.
  static const std::string* const kChassisNameString =
      new std::string("some_chassis_name");
  ON_CALL(mock_switch, ChassisName)
      .WillByDefault(ReturnRef(*kChassisNameString));
  EXPECT_CALL(mock_switch, ChassisName).Times(AnyNumber());

  // Actual test.
  {
    InSequence s;
    ExpectCallToClearTableEntries(mock_switch, pdpi::GetTestP4Info(), metadata);
    if (gnmi_config.has_value()) {
      ExpectCallToPushGnmiAndWaitForConvergence(mock_switch, interfaces);
    }
    ExpectCallToCreateP4RuntimeSessionAndOptionallyPushP4Info(mock_switch,
                                                              p4info, metadata);
  }
}

// Tests that ConfigureSwitchAndReturnP4RuntimeSession works when given a
// P4Info.
TEST(TestHelperLibTest,
     ConfigureSwitchAndReturnP4RuntimeSessionWithP4InfoPush) {
  const p4::config::v1::P4Info& p4info = pdpi::GetTestP4Info();
  const pdpi::P4RuntimeSessionOptionalArgs metadata;
  thinkit::MockSwitch mock_switch;
  OpenConfigInterfaceDescription interface {
    .port_name = "Ethernet0", .port_id = 1,
  };
  const std::string gnmi_config = OpenConfigWithInterfaces(
      GnmiFieldType::kConfig, /*interfaces=*/{interface});

  for (bool push_gnmi_config : {true, false}) {
    for (bool push_p4info : {true, false}) {
      SCOPED_TRACE(absl::StrCat("push_gnmi_config: ", push_gnmi_config));
      SCOPED_TRACE(absl::StrCat("push_p4info: ", push_p4info));
      std::optional<std::string> optional_gnmi_config =
          push_gnmi_config ? std::make_optional(gnmi_config) : std::nullopt;
      std::optional<p4::config::v1::P4Info> optional_p4info =
          push_p4info ? std::make_optional(p4info) : std::nullopt;

      MockConfigureSwitchAndReturnP4RuntimeSession(
          mock_switch, optional_gnmi_config, optional_p4info, metadata,
          /*interfaces=*/{interface});
      ASSERT_OK_AND_ASSIGN(
          auto session,
          ConfigureSwitchAndReturnP4RuntimeSession(
              mock_switch, optional_gnmi_config, optional_p4info, metadata));
      testing::Mock::VerifyAndClearExpectations(&mock_switch);
    }
  }
}

TEST(TestHelperLibTest, ConfigureSwitchPairAndReturnP4RuntimeSessionPair) {
  const p4::config::v1::P4Info& p4info = pdpi::GetTestP4Info();
  const pdpi::P4RuntimeSessionOptionalArgs metadata;
  thinkit::MockSwitch mock_switch1;
  thinkit::MockSwitch mock_switch2;
  OpenConfigInterfaceDescription interface {
    .port_name = "Ethernet0", .port_id = 1,
  };
  const std::string gnmi_config = OpenConfigWithInterfaces(
      GnmiFieldType::kConfig, /*interfaces=*/{interface});

  for (bool push_gnmi_config : {true, false}) {
    for (bool push_p4info : {true, false}) {
      SCOPED_TRACE(absl::StrCat("push_gnmi_config: ", push_gnmi_config));
      SCOPED_TRACE(absl::StrCat("push_p4info: ", push_gnmi_config));
      std::optional<std::string> optional_gnmi_config =
          push_gnmi_config ? std::make_optional(gnmi_config) : std::nullopt;
      std::optional<p4::config::v1::P4Info> optional_p4info =
          push_p4info ? std::make_optional(p4info) : std::nullopt;

      // Mock two configurings.
      MockConfigureSwitchAndReturnP4RuntimeSession(
          mock_switch1, optional_gnmi_config, optional_p4info, metadata,
          /*interfaces=*/{interface});
      MockConfigureSwitchAndReturnP4RuntimeSession(
          mock_switch2, optional_gnmi_config, optional_p4info, metadata,
          /*interfaces=*/{interface});
      ASSERT_OK_AND_ASSIGN((auto [session1, session2]),
                           ConfigureSwitchPairAndReturnP4RuntimeSessionPair(
                               mock_switch1, mock_switch2, optional_gnmi_config,
                               optional_p4info, metadata));
      testing::Mock::VerifyAndClearExpectations(&mock_switch1);
      testing::Mock::VerifyAndClearExpectations(&mock_switch2);
    }
  }
}

/*** REWRITE PORT TESTS ******************************************************/

TEST(RewritePortsForTableEntriesTest, NoPortsInConfigFails) {
  const pdpi::IrP4Info fbr_info =
      sai::GetIrP4Info(sai::Instantiation::kFabricBorderRouter);
  const std::string gnmi_config = EmptyOpenConfig();
  std::vector<pdpi::IrTableEntry> entries;
  EXPECT_THAT(RewritePortsInTableEntries(fbr_info, gnmi_config, entries),
              Not(IsOk()));
}

TEST(RewritePortsForTableEntriesTest, EmptyEntriesSucceeds) {
  const pdpi::IrP4Info fbr_info =
      sai::GetIrP4Info(sai::Instantiation::kFabricBorderRouter);
  std::vector<pdpi::IrTableEntry> entries;
  EXPECT_OK(RewritePortsInTableEntries(
      fbr_info, /*ports=*/std::vector<std::string>{"1"}, entries));
}

TEST(RewritePortsForTableEntriesTest, GnmiConfigWorks) {
  const pdpi::IrP4Info fbr_info =
      sai::GetIrP4Info(sai::Instantiation::kFabricBorderRouter);
  const std::string gnmi_config = OpenConfigWithInterfaces(
      GnmiFieldType::kConfig, {OpenConfigInterfaceDescription{
                                  .port_name = "Ethernet0",
                                  .port_id = 1,
                              }});
  pdpi::IrTableEntry original_entry =
      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
        table_name: "router_interface_table"
        matches {
          name: "router_interface_id"
          exact { str: "router-interface-1" }
        }
        action {
          name: "set_port_and_src_mac"
          params {
            name: "port"
            value { str: "2" }
          }
          params {
            name: "src_mac"
            value { mac: "00:02:03:04:05:06" }
          }
        }
      )pb");

  std::vector<pdpi::IrTableEntry> entries = {original_entry};
  ASSERT_OK(RewritePortsInTableEntries(fbr_info, gnmi_config, entries));

  ASSERT_EQ(entries[0].action().params(0).value().str(), "1");
}

}  // namespace
}  // namespace pins_test
