// Copyright 2025 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "tests/lib/switch_test_setup_helpers.h"

#include <memory>
#include <optional>
#include <string>
#include <vector>

#include "absl/container/btree_set.h"
#include "absl/memory/memory.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/types/span.h"
#include "gmock/gmock.h"
#include "grpcpp/test/mock_stream.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/status.h"
#include "gutil/testing.h"
#include "include/nlohmann/json.hpp"
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
#include "third_party/json/include/nlohmann/json_fwd.hpp"

namespace pins_test {
namespace {

using ::gutil::EqualsProto;
using ::testing::AnyNumber;
using ::testing::Eq;
using ::testing::ExplainMatchResult;
using ::testing::InSequence;
using ::testing::Not;
using ::testing::Pointwise;
using ::testing::Return;
using ::testing::ReturnRef;
using ::testing::StrictMock;
using ::testing::UnorderedElementsAre;
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
    const std::optional<absl::string_view>& gnmi_config,
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

TEST(ConfigureSwitchAndReturnP4RuntimeSessionTest,
     WorksWithAllCombinationsOfGivenAndNotGivenGnmiConfigAndP4Info) {
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

TEST(ConfigureSwitchPairAndReturnP4RuntimeSessionPairTest,
     WorksWithAllCombinationsOfGivenAndNotGivenGnmiConfigAndP4Info) {
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

TEST(ConfigureSwitchTest,
     WorksWithAllCombinationsOfGivenAndNotGivenGnmiConfigAndP4Info) {
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
      auto config = PinsConfigView{
          .gnmi_config =
              push_gnmi_config ? std::make_optional(gnmi_config) : std::nullopt,
          .p4info = push_p4info ? std::make_optional(p4info) : std::nullopt,
      };

      MockConfigureSwitchAndReturnP4RuntimeSession(
          mock_switch, config.gnmi_config, config.p4info, metadata,
          /*interfaces=*/{interface});
      ASSERT_OK(ConfigureSwitch(mock_switch, config, metadata));
      testing::Mock::VerifyAndClearExpectations(&mock_switch);
    }
  }
}

TEST(ConfigureSwitchPairTest,
     NewOverloadWorksWithAllCombinationsOfGivenAndNotGivenGnmiConfigAndP4Info) {
  const pdpi::P4RuntimeSessionOptionalArgs metadata;
  thinkit::MockSwitch mock_switch1;
  thinkit::MockSwitch mock_switch2;

  const p4::config::v1::P4Info& p4info1 = pdpi::GetTestP4Info();
  p4::config::v1::P4Info p4info2 = p4info1;
  p4info2.clear_pkg_info();
  ASSERT_THAT(p4info2, Not(EqualsProto(p4info1)));

  OpenConfigInterfaceDescription interface1{
      .port_name = "Ethernet0",
      .port_id = 1,
  };
  OpenConfigInterfaceDescription interface2{
      .port_name = "Ethernet8",
      .port_id = 2,
  };
  const std::string gnmi_config1 = OpenConfigWithInterfaces(
      GnmiFieldType::kConfig, /*interfaces=*/{interface1});
  const std::string gnmi_config2 = OpenConfigWithInterfaces(
      GnmiFieldType::kConfig, /*interfaces=*/{interface2});
  ASSERT_NE(gnmi_config2, gnmi_config1);

  for (bool push_gnmi_config1 : {true, false}) {
    for (bool push_gnmi_config2 : {true, false}) {
      for (bool push_p4info1 : {true, false}) {
        for (bool push_p4info2 : {true, false}) {
          SCOPED_TRACE(absl::StrCat("push_gnmi_config 1: ", push_gnmi_config1));
          SCOPED_TRACE(absl::StrCat("push_p4info 1: ", push_p4info1));
          SCOPED_TRACE(absl::StrCat("push_gnmi_config 2: ", push_gnmi_config2));
          SCOPED_TRACE(absl::StrCat("push_p4info 2: ", push_p4info2));
          auto config1 = PinsConfigView{
              .gnmi_config = push_gnmi_config1
                                 ? std::make_optional(gnmi_config1)
                                 : std::nullopt,
              .p4info =
                  push_p4info1 ? std::make_optional(p4info1) : std::nullopt,
          };
          auto config2 = PinsConfigView{
              .gnmi_config = push_gnmi_config2
                                 ? std::make_optional(gnmi_config2)
                                 : std::nullopt,
              .p4info =
                  push_p4info2 ? std::make_optional(p4info2) : std::nullopt,
          };

          // Mock two configurings.
          MockConfigureSwitchAndReturnP4RuntimeSession(
              mock_switch1, config1.gnmi_config, config1.p4info, metadata,
              /*interfaces=*/{interface1});
          MockConfigureSwitchAndReturnP4RuntimeSession(
              mock_switch2, config2.gnmi_config, config2.p4info, metadata,
              /*interfaces=*/{interface2});
          ASSERT_OK(ConfigureSwitchPair(mock_switch1, config1, mock_switch2,
                                        config2, metadata));
        }
      }
    }
  }
}

TEST(ConfigureSwitchPairTest,
     OldOverloadWorksWithAllCombinationsOfGivenAndNotGivenGnmiConfigAndP4Info) {
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
      ASSERT_OK(ConfigureSwitchPair(mock_switch1, mock_switch2,
                                    optional_gnmi_config, optional_p4info,
                                    metadata));
    }
  }
}

/*** REWRITE PORT TESTS *******************************************************/

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

struct MirroredPortTestInterface {
  std::string port_name;
  int port_id;
  bool up;
};

std::string MirrorPortOpenConfigInterfaces(
    const std::vector<MirroredPortTestInterface> &interfaces) {
  std::vector<nlohmann::json> port_configs;
  for (const auto &interface : interfaces) {
    port_configs.push_back({
        {"name", interface.port_name},
        {
            "state",
            {
                {"openconfig-p4rt:id", interface.port_id},
                {"oper-status", interface.up ? "UP" : "DOWN"},
                {"type", "iana-if-type:ethernetCsmacd"},
            },
        },
    });
  }

  nlohmann::json open_config{
      {"openconfig-interfaces:interfaces", {{"interface", port_configs}}}};
  return open_config.dump();
}

MATCHER(MirroredPortIs, "") {
  const MirroredPort &actual = std::get<0>(arg);
  const MirroredPort &expected = std::get<1>(arg);
  return ExplainMatchResult(Eq(expected.interface), actual.interface,
                            result_listener) &&
         ExplainMatchResult(Eq(expected.sut.GetP4rtEncoding()),
                            actual.sut.GetP4rtEncoding(), result_listener) &&
         ExplainMatchResult(Eq(expected.control_switch.GetP4rtEncoding()),
                            actual.control_switch.GetP4rtEncoding(),
                            result_listener);
}

TEST(MirroredPortsTest, ReturnsMirroredPorts) {
  auto mock_sut_stub = absl::make_unique<gnmi::MockgNMIStub>();
  auto mock_control_switch_stub = absl::make_unique<gnmi::MockgNMIStub>();

  EXPECT_CALL(*mock_sut_stub, Get)
      .WillRepeatedly([=](auto, auto, gnmi::GetResponse *response) {
        *response->add_notification()
             ->add_update()
             ->mutable_val()
             ->mutable_json_ietf_val() = MirrorPortOpenConfigInterfaces({
            {.port_name = "Ethernet1/1/1", .port_id = 1, .up = true},
            {.port_name = "Ethernet1/1/5", .port_id = 2, .up = true},
            {.port_name = "Ethernet1/4/1", .port_id = 7, .up = true},
            {.port_name = "Ethernet1/4/5", .port_id = 8, .up = false},
            {.port_name = "Ethernet1/5/1", .port_id = 9, .up = true},
        });
        return grpc::Status::OK;
      });

  EXPECT_CALL(*mock_control_switch_stub, Get)
      .WillRepeatedly([=](auto, auto, gnmi::GetResponse *response) {
        *response->add_notification()
             ->add_update()
             ->mutable_val()
             ->mutable_json_ietf_val() = MirrorPortOpenConfigInterfaces({
            {.port_name = "Ethernet1/1/1", .port_id = 1, .up = true},
            {.port_name = "Ethernet1/1/5", .port_id = 3, .up = true},
            {.port_name = "Ethernet1/3/1", .port_id = 7, .up = true},
            {.port_name = "Ethernet1/4/5", .port_id = 8, .up = false},
            {.port_name = "Ethernet1/5/1", .port_id = 9, .up = true},
        });
        return grpc::Status::OK;
      });
  ASSERT_OK_AND_ASSIGN(
      auto mirrored_ports,
      MirroredPorts(*mock_sut_stub, *mock_control_switch_stub));
  EXPECT_THAT(
      mirrored_ports,
      Pointwise(
          MirroredPortIs(),
          std::vector<MirroredPort>({
              {
                  .interface = "Ethernet1/1/1",
                  .sut = P4rtPortId::MakeFromOpenConfigEncoding(1),
                  .control_switch = P4rtPortId::MakeFromOpenConfigEncoding(1),
              },
              {
                  .interface = "Ethernet1/1/5",
                  .sut = P4rtPortId::MakeFromOpenConfigEncoding(2),
                  .control_switch = P4rtPortId::MakeFromOpenConfigEncoding(3),
              },
              {
                  .interface = "Ethernet1/5/1",
                  .sut = P4rtPortId::MakeFromOpenConfigEncoding(9),
                  .control_switch = P4rtPortId::MakeFromOpenConfigEncoding(9),
              },
          })));
}

TEST(GetPortsUsedTest, ReturnsPortsUsed) {
  const pdpi::IrP4Info fbr_info =
      sai::GetIrP4Info(sai::Instantiation::kFabricBorderRouter);
  pdpi::IrEntity multicast_entity = gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
    packet_replication_engine_entry {
      multicast_group_entry {
        multicast_group_id: 7
        replicas { port: "1" instance: 1 }
        replicas { port: "2" instance: 1 }
      }
    }
  )pb");
  pdpi::IrEntity clone_entity = gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
    packet_replication_engine_entry {
      clone_session_entry {
        session_id: 7
        replicas { port: "3" instance: 1 }
        replicas { port: "4" instance: 1 }
        class_of_service: 2
        packet_length_bytes: 200
      }
    }
  )pb");
  ASSERT_OK_AND_ASSIGN(
      absl::btree_set<P4rtPortId> ports,
      pins_test::GetPortsUsed(fbr_info, {multicast_entity, clone_entity}));
  ASSERT_THAT(ports,
              UnorderedElementsAre(*P4rtPortId::MakeFromP4rtEncoding("1"),
                                   *P4rtPortId::MakeFromP4rtEncoding("2"),
                                   *P4rtPortId::MakeFromP4rtEncoding("3"),
                                   *P4rtPortId::MakeFromP4rtEncoding("4")));
}

}  // namespace
}  // namespace pins_test
