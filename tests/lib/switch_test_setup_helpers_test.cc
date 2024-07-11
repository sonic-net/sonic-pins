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
#include "absl/strings/string_view.h"
#include "absl/types/span.h"
#include "gmock/gmock.h"
#include "grpcpp/test/mock_stream.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "gutil/testing.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/p4rt/p4rt_port.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/p4_runtime_session_mocking.h"
#include "p4_pdpi/testing/test_p4info.h"
#include "proto/gnmi/gnmi_mock.grpc.pb.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "thinkit/mock_switch.h"

namespace pins_test {
namespace {

using ::testing::AnyNumber;
using ::testing::InSequence;
using ::testing::Not;
using ::testing::Return;
using ::testing::ReturnRef;
using ::testing::StrictMock;
using ::testing::status::IsOk;

// Any constant is fine here.
constexpr uint32_t kDeviceId = 100;

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
// by `interfaces` are retrieved from the config path and have converged in the
// state path.
void MockGnmiConvergence(
    gnmi::MockgNMIStub& mock_gnmi_stub,
    const std::vector<OpenConfigInterfaceDescription>& interfaces) {
  InSequence s;
  EXPECT_CALL(mock_gnmi_stub, Get)
      .WillOnce([=](auto, auto, gnmi::GetResponse* response) {
        *response->add_notification()
             ->add_update()
             ->mutable_val()
             ->mutable_json_ietf_val() =
            OpenConfigWithInterfaces(GnmiFieldType::kConfig, interfaces);
        return grpc::Status::OK;
      });
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
    pdpi::MockCheckNoEntries(*stub, p4info);

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
      ExpectCallToPushGnmiConfig(mock_switch);
    }
    ExpectCallToCreateP4RuntimeSessionAndOptionallyPushP4Info(mock_switch,
                                                              p4info, metadata);
    ExpectCallToWaitForGnmiPortIdConvergence(mock_switch, interfaces);
  }
}

// Tests that ConfigureSwitchAndReturnP4RuntimeSession works when given a
// P4Info.
TEST(TestHelperLibTest,
     ConfigureSwitchAndReturnP4RuntimeSessionWithP4InfoPush) {
  const p4::config::v1::P4Info& p4info = pdpi::GetTestP4Info();
  const pdpi::P4RuntimeSessionOptionalArgs metadata;
  thinkit::MockSwitch mock_switch;
  OpenConfigInterfaceDescription interface{
      .port_name = "Ethernet0",
      .port_id = 1,
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
  OpenConfigInterfaceDescription interface{
      .port_name = "Ethernet0",
      .port_id = 1,
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
      fbr_info,
      /*ports=*/P4rtPortId::MakeVectorFromOpenConfigEncodings({1}), entries));
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
