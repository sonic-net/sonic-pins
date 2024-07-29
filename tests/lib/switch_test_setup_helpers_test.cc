#include "tests/lib/switch_test_setup_helpers.h"

#include <string>

#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "grpcpp/test/mock_stream.h"
#include "gtest/gtest.h"
#include "lib/gnmi/gnmi_helper.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4/v1/p4runtime_mock.grpc.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/testing/test_p4info.h"
#include "proto/gnmi/gnmi_mock.grpc.pb.h"
#include "thinkit/mock_switch.h"

namespace pins_test {
namespace {

using ::testing::_;
using ::testing::ByMove;
using ::testing::EqualsProto;
using ::testing::InSequence;
using ::testing::Return;
using ::testing::ReturnRef;

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
  auto* stream = new grpc::testing::MockClientReaderWriter<
      p4::v1::StreamMessageRequest, p4::v1::StreamMessageResponse>();
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
void MockCheckNoEntries(p4::v1::MockP4RuntimeStub& stub,
                        const p4::config::v1::P4Info& p4info) {
  // We need to return a valid p4info to get to the stage where we read tables.
  EXPECT_CALL(stub, GetForwardingPipelineConfig)
      .WillOnce([&](auto, auto,
                    p4::v1::GetForwardingPipelineConfigResponse*
                        get_pipeline_response) {
        *get_pipeline_response->mutable_config()->mutable_p4info() = p4info;
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
      .WillOnce([&](auto, auto,
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
    MockCheckNoEntries(stub, p4info);
  }
}

// Mocks a successful `PushGnmiConfig` call.
void MockGnmiPush(gnmi::MockgNMIStub& mock_gnmi_stub) {
  EXPECT_CALL(mock_gnmi_stub, Set).WillOnce(Return(grpc::Status::OK));
}

// Generates an OpenConfig JSON string with the interface and p4rt port ID.
std::string OpenConfigInterface(absl::string_view field_type,
                                absl::string_view port_name,
                                absl::string_view port_id) {
  return absl::Substitute(R"(
    {
      "openconfig-interfaces:interfaces":{
        "interface" : [
          {
            "name" : "$0",
            "$1" : {
              "openconfig-p4rt:id" : $2
            }
          }
        ]
      }
    })",
                          port_name, field_type, port_id);
}

// Mocks a successful `WaitForGnmiPortIdConvergence` call where the port given
// by `port_name` and `port_id` has converged.
void MockGnmiConvergence(gnmi::MockgNMIStub& mock_gnmi_stub,
                         absl::string_view port_name, absl::string_view port_id,
                         const absl::Duration& gnmi_timeout) {
  EXPECT_CALL(mock_gnmi_stub, Get)
      .WillOnce([=](auto, auto, gnmi::GetResponse* response) {
        *response->add_notification()
             ->add_update()
             ->mutable_val()
             ->mutable_json_ietf_val() =
            OpenConfigInterface("state", port_name, port_id);
        return grpc::Status::OK;
      });
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

// Tests that ConfigureSwitchAndReturnP4RuntimeSession creates a
// P4RuntimeSession, clears all table entries currently on the switch (mocked
// to be one), pushes a gNMI config, converges, and pushes a new p4info, if one
// is given.
void MockConfigureSwitchAndReturnP4RuntimeSession(
    thinkit::MockSwitch& mock_switch, absl::string_view port_name,
    absl::string_view port_id,
    const p4::config::v1::P4Info& p4info_returned_by_get_forwarding_pipeline,
    const p4::config::v1::P4Info* p4info_used_to_set_forwarding_pipeline,
    const pdpi::P4RuntimeSessionOptionalArgs& metadata) {
  // The stub that will be returned when CreateP4RuntimeStub is called on
  // mock_switch.
  auto stub = absl::make_unique<p4::v1::MockP4RuntimeStub>();
  ASSERT_NE(stub, nullptr);

  // The stubs that will be returned when CreateGnmiStub is called on
  // mock_switch.
  auto mock_gnmi_stub_push = absl::make_unique<gnmi::MockgNMIStub>();
  auto mock_gnmi_stub_converge = absl::make_unique<gnmi::MockgNMIStub>();
  ASSERT_NE(mock_gnmi_stub_push, nullptr);
  ASSERT_NE(mock_gnmi_stub_converge, nullptr);

  {
    InSequence s;
    // Mocks a P4RuntimeSession `Create` call.
    // Constructs a ReaderWriter mock stream and completes an arbitration
    // handshake.
    MockP4RuntimeSessionCreate(*stub, metadata);

    // Mocks a `ClearTableEntries` call.
    // Pulls the p4info from the switch, then reads a table entry, deletes it,
    // and reads again ensuring that there are no table entries remaining.
    MockClearTableEntries(*stub, p4info_returned_by_get_forwarding_pipeline,
                          metadata);

    // Mocks a `CheckNoEntries` call.
    MockCheckNoEntries(*stub, p4info_returned_by_get_forwarding_pipeline);

    // Mocks a `PushGnmiConfig` call.
    MockGnmiPush(*mock_gnmi_stub_push);

    // Mocks a `WaitForGnmiPortIdConvergence` call.
    MockGnmiConvergence(*mock_gnmi_stub_converge, port_name, port_id,
                        /*gnmi_timeout=*/absl::Minutes(3));

    // When there is a P4Info to set, we mock a `SetForwardingPipelineConfig`
    // call and a `CheckNoEntries` call.
    if (p4info_used_to_set_forwarding_pipeline != nullptr) {
      // Mocks a `SetForwardingPipelineConfig` call.
      EXPECT_CALL(*stub,
                  SetForwardingPipelineConfig(
                      _,
                      EqualsProto(ConstructForwardingPipelineConfigRequest(
                          metadata, *p4info_used_to_set_forwarding_pipeline)),
                      _))
          .Times(1);

      // Mocks a `CheckNoEntries` call.
      MockCheckNoEntries(*stub, *p4info_used_to_set_forwarding_pipeline);
    }
  }

  {
    InSequence s;
    // Mocks the first part of a P4RuntimeSession `Create` call.
    EXPECT_CALL(mock_switch, CreateP4RuntimeStub())
        .WillOnce(Return(ByMove(std::move(stub))));
    EXPECT_CALL(mock_switch, DeviceId).WillOnce(Return(kDeviceId));

    // Mocks the first part of a `PushGnmiConfig` call.
    EXPECT_CALL(mock_switch, CreateGnmiStub)
        .WillOnce(Return(ByMove(std::move(mock_gnmi_stub_push))));

    // Required so that the reference below is not to a local variable.
    static const std::string* const kChassisNameString =
        new std::string("some_chassis_name");
    EXPECT_CALL(mock_switch, ChassisName)
        .WillOnce(ReturnRef(*kChassisNameString));

    // Mocks the first part of a `WaitForGnmiPortIdConvergence`
    EXPECT_CALL(mock_switch, CreateGnmiStub)
        .WillOnce(Return(ByMove(std::move(mock_gnmi_stub_converge))));
  }
}

// Tests that ConfigureSwitchAndReturnP4RuntimeSession works when given a
// P4Info.
TEST(TestHelperLibTest,
     ConfigureSwitchAndReturnP4RuntimeSessionWithP4InfoPush) {
  const p4::config::v1::P4Info& p4info = pdpi::GetTestP4Info();
  const pdpi::P4RuntimeSessionOptionalArgs metadata;
  thinkit::MockSwitch mock_switch;
  const std::string port_name = "Ethernet0";
  const std::string port_id = "1";

  const std::string gnmi_config =
      OpenConfigInterface("config", port_name, port_id);

  EXPECT_CALL(mock_switch, DeviceId).WillOnce(Return(123456));
  MockConfigureSwitchAndReturnP4RuntimeSession(
      mock_switch, port_name, port_id,
      /*p4info_returned_by_get_forwarding_pipeline=*/p4info,
      /*p4info_used_to_set_forwarding_pipeline=*/&p4info, metadata);

  ASSERT_OK_AND_ASSIGN(auto session,
                       ConfigureSwitchAndReturnP4RuntimeSession(
                           mock_switch, gnmi_config, p4info, metadata));
}

// Tests that ConfigureSwitchAndReturnP4RuntimeSession works without a P4Info.
TEST(TestHelperLibTest,
     ConfigureSwitchAndReturnP4RuntimeSessionWithoutP4InfoPush) {
  const p4::config::v1::P4Info& p4info = pdpi::GetTestP4Info();
  const pdpi::P4RuntimeSessionOptionalArgs metadata;
  thinkit::MockSwitch mock_switch;
  const std::string port_name = "Ethernet0";
  const std::string port_id = "1";

  const std::string gnmi_config =
      OpenConfigInterface("config", port_name, port_id);

  EXPECT_CALL(mock_switch, DeviceId).WillOnce(Return(123456));
  MockConfigureSwitchAndReturnP4RuntimeSession(
      mock_switch, port_name, port_id,
      /*p4info_returned_by_get_forwarding_pipeline=*/p4info,
      /*p4info_used_to_set_forwarding_pipeline=*/nullptr, metadata);

  ASSERT_OK_AND_ASSIGN(
      auto session, ConfigureSwitchAndReturnP4RuntimeSessionWithoutP4InfoPush(
                        mock_switch, gnmi_config, metadata));
}

TEST(TestHelperLibTest, ConfigureSwitchPairAndReturnP4RuntimeSessionPair) {
  const p4::config::v1::P4Info& p4info = pdpi::GetTestP4Info();
  const pdpi::P4RuntimeSessionOptionalArgs metadata;
  thinkit::MockSwitch mock_switch1;
  thinkit::MockSwitch mock_switch2;
  const std::string port_name = "Ethernet0";
  const std::string port_id = "1";

  const std::string gnmi_config =
      OpenConfigInterface("config", port_name, port_id);

  // Mock two configurings, skipping the final call.
  EXPECT_CALL(mock_switch1, DeviceId).WillOnce(Return(10005));
  MockConfigureSwitchAndReturnP4RuntimeSession(
      mock_switch1, port_name, port_id,
      /*p4info_returned_by_get_forwarding_pipeline=*/p4info,
      /*p4info_used_to_set_forwarding_pipeline=*/&p4info, metadata);
  EXPECT_CALL(mock_switch2, DeviceId).WillOnce(Return(10006));
  MockConfigureSwitchAndReturnP4RuntimeSession(
      mock_switch2, port_name, port_id,
      /*p4info_returned_by_get_forwarding_pipeline=*/p4info,
      /*p4info_used_to_set_forwarding_pipeline=*/&p4info, metadata);

  // Mock the final call.
  ASSERT_OK_AND_ASSIGN(
      (auto [session1, session2]),
      ConfigureSwitchPairAndReturnP4RuntimeSessionPair(
          mock_switch1, mock_switch2, gnmi_config, p4info, metadata));
}

}  // namespace
}  // namespace pins_test
