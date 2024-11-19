#include <cstdio>
#include <memory>
#include <string>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "google/protobuf/text_format.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "include/nlohmann/json.hpp"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "proto/gnmi/gnmi.pb.h"
#include "proto/gnmi/gnmi_mock.grpc.pb.h"
#include "tests/thinkit_gnmi_interface_util.h"
#include "tests/thinkit_util.h"
#include "thinkit/mock_ssh_client.h"
#include "thinkit/mock_switch.h"

namespace pins_test {
using gutil::EqualsProto;
using gutil::StatusIs;
using ::nlohmann::json;
using ::testing::_;
using ::testing::ContainerEq;
using ::testing::DoAll;
using ::testing::HasSubstr;
using ::testing::Return;
using ::testing::ReturnRefOfCopy;
using ::testing::SetArgPointee;

class GNMIThinkitInterfaceUtilityTest : public ::testing::Test {
 protected:
  void SetUp() override {
    ON_CALL(mock_switch_, ChassisName())
        .WillByDefault(ReturnRefOfCopy(std::string("chassis_1")));
  }
  thinkit::MockSSHClient mock_ssh_client_;
  thinkit::MockSwitch mock_switch_;
  gnmi::MockgNMIStub mock_gnmi_stub_;
};

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetSupportedBreakoutModesForPortAnySuccess) {
  const std::string port = "Ethernet0";
  std::vector<std::string> expected_breakout_modes = {
      "1x400G", "2x200G", "2x100G", "2x40G", "4x100G"};

  const std::string interface_info =
      R"pb({ "breakout_modes": "1x400G, 2x200G[100G,40G], 4x100G" }
      )pb";
  EXPECT_THAT(pins_test::GetSupportedBreakoutModesForPort(interface_info, port),
              expected_breakout_modes);
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetSupportedBreakoutModesForPortChannelizedSuccess) {
  const std::string port = "Ethernet0";
  std::vector<std::string> expected_breakout_modes = {"2x200G", "2x100G",
                                                      "2x40G", "4x100G"};

  const std::string interface_info =
      R"pb({ "breakout_modes": "1x400G, 2x200G[100G,40G], 4x100G" }
      )pb";
  EXPECT_THAT(pins_test::GetSupportedBreakoutModesForPort(
                  interface_info, port, pins_test::BreakoutType::kChannelized),
              expected_breakout_modes);
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetSupportedBreakoutModesForPortBreakoutModesNotFoundFailure) {
  const std::string port = "Ethernet0";
  const std::string interface_info =
      R"pb({}
      )pb";
  EXPECT_THAT(
      pins_test::GetSupportedBreakoutModesForPort(interface_info, port),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr(absl::StrCat("Supported breakout modes not found for ",
                                      port, " in platform.json"))));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetSupportedBreakoutModesForPortNumBreakoutsIntConversionFailure) {
  const std::string port = "Ethernet0";
  const std::string interface_info =
      R"pb({ "breakout_modes": "Xx400G, 2x200G[100G,40G], 4x100G" }
      )pb";
  EXPECT_THAT(pins_test::GetSupportedBreakoutModesForPort(
                  interface_info, port, pins_test::BreakoutType::kChannelized),
              StatusIs(absl::StatusCode::kInternal,
                       HasSubstr("Failed to convert string (X) to integer")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetRandomPortWithSupportedBreakoutModesAnySuccess) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  absl::flat_hash_map<std::string, pins_test::RandomPortBreakoutInfo>
      expected_port_info;
  pins_test::RandomPortBreakoutInfo r;
  r.port_name = "Ethernet0";
  r.curr_breakout_mode = "1x400G";
  r.supported_breakout_mode = "2x200G";
  expected_port_info["Ethernet0"] = r;
  r.port_name = "Ethernet8";
  r.curr_breakout_mode = "2x200G";
  r.supported_breakout_mode = "1x400G";
  expected_port_info["Ethernet8"] = r;
  const std::string platform_json_contents =
      R"pb({
             "interfaces": {
               "Ethernet0": {
                 "default_brkout_mode": "1x400G",
                 "breakout_modes": "1x400G, 2x200G[100G,40G]"
               },
               "Ethernet8": {
                 "default_brkout_mode": "2x200G",
                 "breakout_modes": "1x400G, 2x200G[100G,40G]"
               },
               "Ethernet12": { "breakout_modes": "1x200G[100G,40G]" }
             }
           }
      )pb";
  gnmi::GetRequest req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(prefix { origin: "openconfig" }
           path { elem { name: "interfaces" } }
           type: STATE)pb",
      &req));
  gnmi::GetResponse resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1631864194292383538
             prefix { origin: "openconfig" }
             update {
               path { elem { name: "interfaces" } }
               val {
                 json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet0\",\"state\":{\"oper-status\":\"UP\"}},{\"name\":\"Ethernet8\",\"state\":{\"oper-status\":\"UP\"}}]}}"
               }
             }
           }
      )pb",
      &resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(req), _))
      .WillOnce(DoAll(SetArgPointee<2>(resp), Return(grpc::Status::OK)));
  auto random_port_info = pins_test::GetRandomPortWithSupportedBreakoutModes(
      *mock_gnmi_stub_ptr, platform_json_contents);
  ASSERT_OK(random_port_info.status());
  EXPECT_THAT(random_port_info.value().port_name,
              expected_port_info[random_port_info.value().port_name].port_name);
  EXPECT_THAT(random_port_info.value().curr_breakout_mode,
              expected_port_info[random_port_info.value().port_name]
                  .curr_breakout_mode);
  EXPECT_THAT(random_port_info.value().supported_breakout_mode,
              expected_port_info[random_port_info.value().port_name]
                  .supported_breakout_mode);
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetRandomPortWithSupportedBreakoutModesChannelizedSuccess) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  absl::flat_hash_map<std::string, pins_test::RandomPortBreakoutInfo>
      expected_port_info;
  pins_test::RandomPortBreakoutInfo r;
  r.port_name = "Ethernet0";
  r.curr_breakout_mode = "1x400G";
  r.supported_breakout_mode = "2x200G";
  expected_port_info["Ethernet0"] = r;
  const std::string platform_json_contents =
      R"pb({
             "interfaces": {
               "Ethernet0": {
                 "default_brkout_mode": "1x400G",
                 "breakout_modes": "1x400G, 2x200G[100G,40G]"
               },
               "Ethernet8": {
                 "default_brkout_mode": "1x400G",
                 "breakout_modes": "1x400G"
               },
               "Ethernet16": {
                 "default_brkout_mode": "1x400G",
                 "breakout_modes": "1x400G"
               }
             }
           }
      )pb";
  gnmi::GetRequest req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(prefix { origin: "openconfig" }
           path { elem { name: "interfaces" } }
           type: STATE)pb",
      &req));
  gnmi::GetResponse resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1631864194292383538
             prefix { origin: "openconfig" }
             update {
               path { elem { name: "interfaces" } }
               val {
                 json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet0\",\"state\":{\"oper-status\":\"UP\"}},{\"name\":\"Ethernet8\",\"state\":{\"oper-status\":\"UP\"}},{\"name\":\"Ethernet16\",\"state\":{\"oper-status\":\"UP\"}}]}}"
               }
             }
           }
      )pb",
      &resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(req), _))
      .WillOnce(DoAll(SetArgPointee<2>(resp), Return(grpc::Status::OK)));
  auto random_port_info = pins_test::GetRandomPortWithSupportedBreakoutModes(
      *mock_gnmi_stub_ptr, platform_json_contents,
      pins_test::BreakoutType::kChannelized);
  ASSERT_OK(random_port_info.status());
  EXPECT_THAT(random_port_info.value().port_name,
              expected_port_info[random_port_info.value().port_name].port_name);
  EXPECT_THAT(random_port_info.value().curr_breakout_mode,
              expected_port_info[random_port_info.value().port_name]
                  .curr_breakout_mode);
  EXPECT_THAT(random_port_info.value().supported_breakout_mode,
              expected_port_info[random_port_info.value().port_name]
                  .supported_breakout_mode);
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetRandomPortWithSupportedBreakoutModesOperStatusMapGetFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  gnmi::GetRequest req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(prefix { origin: "openconfig" }
           path { elem { name: "interfaces" } }
           type: STATE)pb",
      &req));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(req), _))
      .WillOnce(Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  EXPECT_THAT(
      pins_test::GetRandomPortWithSupportedBreakoutModes(*mock_gnmi_stub_ptr,
                                                         ""),
      StatusIs(absl::StatusCode::kDeadlineExceeded,
               HasSubstr("Failed to get oper-status map for ports on switch")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetRandomPortWithSupportedBreakoutModesIntConversionFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  gnmi::GetRequest req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(prefix { origin: "openconfig" }
           path { elem { name: "interfaces" } }
           type: STATE)pb",
      &req));
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(prefix { origin: "openconfig" }
           path { elem { name: "interfaces" } }
           type: STATE)pb",
      &req));
  gnmi::GetResponse resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1631864194292383538
             prefix { origin: "openconfig" }
             update {
               path { elem { name: "interfaces" } }
               val {
                 json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"EthernetX\",\"state\":{\"oper-status\":\"UP\"}}, {\"name\":\"Ethernet8\",\"state\":{\"oper-status\":\"UP\"}}]}}"
               }
             }
           }
      )pb",
      &resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(req), _))
      .WillOnce(DoAll(SetArgPointee<2>(resp), Return(grpc::Status::OK)));
  EXPECT_THAT(pins_test::GetRandomPortWithSupportedBreakoutModes(
                  *mock_gnmi_stub_ptr, ""),
              StatusIs(absl::StatusCode::kInternal,
                       HasSubstr("Failed to convert string (X) to integer")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetRandomPortWithSupportedBreakoutModesNoOperUpPortsFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string platform_json_contents =
      R"pb({
             "interfaces": {
               "Ethernet0": {
                 "default_brkout_mode": "1x400G",
                 "breakout_modes": "1x400G, 2x200G[100G,40G]"
               },
               "Ethernet8": {
                 "default_brkout_mode": "2x200G",
                 "breakout_modes": "1x400G, 2x200G[100G,40G]"
               },
               "Ethernet12": { "breakout_modes": "1x200G[100G,40G]" }
             }
           }
      )pb";
  gnmi::GetRequest req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(prefix { origin: "openconfig" }
           path { elem { name: "interfaces" } }
           type: STATE)pb",
      &req));
  gnmi::GetResponse resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1631864194292383538
             prefix { origin: "openconfig" }
             update {
               path { elem { name: "interfaces" } }
               val {
                 json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet0\",\"state\":{\"oper-status\":\"DOWN\"}}, {\"name\":\"Ethernet8\",\"state\":{\"oper-status\":\"DOWN\"}}]}}"
               }
             }
           }
      )pb",
      &resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(req), _))
      .WillOnce(DoAll(SetArgPointee<2>(resp), Return(grpc::Status::OK)));
  EXPECT_THAT(
      pins_test::GetRandomPortWithSupportedBreakoutModes(
          *mock_gnmi_stub_ptr, platform_json_contents),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr("No operationally up parent ports found on switch")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetRandomPortWithSupportedBreakoutModesInterfacesNotFoundInFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string platform_json_contents =
      R"pb({}
      )pb";
  gnmi::GetRequest req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(prefix { origin: "openconfig" }
           path { elem { name: "interfaces" } }
           type: STATE)pb",
      &req));
  gnmi::GetResponse resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1631864194292383538
             prefix { origin: "openconfig" }
             update {
               path { elem { name: "interfaces" } }
               val {
                 json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet0\",\"state\":{\"oper-status\":\"UP\"}}]}}"
               }
             }
           }
      )pb",
      &resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(req), _))
      .WillOnce(DoAll(SetArgPointee<2>(resp), Return(grpc::Status::OK)));
  EXPECT_THAT(pins_test::GetRandomPortWithSupportedBreakoutModes(
                  *mock_gnmi_stub_ptr, platform_json_contents),
              StatusIs(absl::StatusCode::kInternal,
                       HasSubstr("Interfaces not found in platform.json")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetRandomPortWithSupportedBreakoutModesInterfaceNotFoundFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string platform_json_contents =
      R"pb({ "interfaces": {} }
      )pb";
  gnmi::GetRequest req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(prefix { origin: "openconfig" }
           path { elem { name: "interfaces" } }
           type: STATE)pb",
      &req));
  gnmi::GetResponse resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1631864194292383538
             prefix { origin: "openconfig" }
             update {
               path { elem { name: "interfaces" } }
               val {
                 json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet0\",\"state\":{\"oper-status\":\"UP\"}}]}}"
               }
             }
           }
      )pb",
      &resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(req), _))
      .WillOnce(DoAll(SetArgPointee<2>(resp), Return(grpc::Status::OK)));
  EXPECT_THAT(
      pins_test::GetRandomPortWithSupportedBreakoutModes(
          *mock_gnmi_stub_ptr, platform_json_contents),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr("Ethernet0 entry not found in platform.json")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetRandomPortWithSupportedBreakoutModesDefaultModeNotFoundFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string platform_json_contents =
      R"pb({
             "interfaces": {
               "Ethernet0": { "breakout_modes": "1x400G, 2x200G[100G,40G]" }
             }
           }
      )pb";
  gnmi::GetRequest req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(prefix { origin: "openconfig" }
           path { elem { name: "interfaces" } }
           type: STATE)pb",
      &req));
  gnmi::GetResponse resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1631864194292383538
             prefix { origin: "openconfig" }
             update {
               path { elem { name: "interfaces" } }
               val {
                 json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet0\",\"state\":{\"oper-status\":\"UP\"}}]}}"
               }
             }
           }
      )pb",
      &resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(req), _))
      .WillOnce(DoAll(SetArgPointee<2>(resp), Return(grpc::Status::OK)));
  EXPECT_THAT(pins_test::GetRandomPortWithSupportedBreakoutModes(
                  *mock_gnmi_stub_ptr, platform_json_contents),
              StatusIs(absl::StatusCode::kInternal,
                       HasSubstr("Default breakout mode not found for "
                                 "Ethernet0 in platform.json")));
}

TEST_F(
    GNMIThinkitInterfaceUtilityTest,
    TestGetRandomPortWithSupportedBreakoutModesSupportedModesNotFoundnFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string platform_json_contents =
      R"pb({
             "interfaces": { "Ethernet0": { "default_brkout_mode": "1x400G" } }
           }
      )pb";
  gnmi::GetRequest req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(prefix { origin: "openconfig" }
           path { elem { name: "interfaces" } }
           type: STATE)pb",
      &req));
  gnmi::GetResponse resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1631864194292383538
             prefix { origin: "openconfig" }
             update {
               path { elem { name: "interfaces" } }
               val {
                 json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet0\",\"state\":{\"oper-status\":\"UP\"}}]}}"
               }
             }
           }
      )pb",
      &resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(req), _))
      .WillOnce(DoAll(SetArgPointee<2>(resp), Return(grpc::Status::OK)));
  EXPECT_THAT(
      pins_test::GetRandomPortWithSupportedBreakoutModes(
          *mock_gnmi_stub_ptr, platform_json_contents),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr(
                   "Breakout modes not found for Ethernet0 in platform.json")));
}

TEST_F(
    GNMIThinkitInterfaceUtilityTest,
    TestGetRandomPortWithSupportedBreakoutModesNoSupportedBreakoutTypeFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string platform_json_contents =
      R"pb({
             "interfaces": {
               "Ethernet0": {
                 "default_brkout_mode": "1x400G",
                 "breakout_modes": "1x400G"
               },
               "Ethernet8": {
                 "default_brkout_mode": "1x400G",
                 "breakout_modes": "1x400G"
               }
             }
           }
      )pb";
  gnmi::GetRequest req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(prefix { origin: "openconfig" }
           path { elem { name: "interfaces" } }
           type: STATE)pb",
      &req));
  gnmi::GetResponse resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1631864194292383538
             prefix { origin: "openconfig" }
             update {
               path { elem { name: "interfaces" } }
               val {
                 json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet0\",\"state\":{\"oper-status\":\"UP\"}},{\"name\":\"Ethernet8\",\"state\":{\"oper-status\":\"UP\"}}]}}"
               }
             }
           }
      )pb",
      &resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(req), _))
      .WillOnce(DoAll(SetArgPointee<2>(resp), Return(grpc::Status::OK)));
  EXPECT_THAT(
      pins_test::GetRandomPortWithSupportedBreakoutModes(
          *mock_gnmi_stub_ptr, platform_json_contents,
          pins_test::BreakoutType::kChannelized),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr(
                   "No random interface with supported breakout modes found")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetExpectedPortInfoForBreakoutModeUnchannelizedBreakoutModeSuccess) {
  const std::string port = "Ethernet0";
  absl::string_view breakout_mode = "1x400G";

  auto breakout_info =
      pins_test::GetExpectedPortInfoForBreakoutMode(port, breakout_mode);
  ASSERT_OK(breakout_info.status());
  EXPECT_EQ(breakout_info.value()["Ethernet0"].physical_channels,
            "[0,1,2,3,4,5,6,7]");
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetExpectedPortInfoForBreakoutModeChannelizedBreakoutModeSuccess) {
  const std::string port = "Ethernet0";
  absl::string_view breakout_mode = "2x200G";

  auto breakout_info =
      pins_test::GetExpectedPortInfoForBreakoutMode(port, breakout_mode);
  ASSERT_OK(breakout_info.status());
  EXPECT_EQ(breakout_info.value()["Ethernet0"].physical_channels, "[0,1,2,3]");
  EXPECT_EQ(breakout_info.value()["Ethernet4"].physical_channels, "[4,5,6,7]");
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetExpectedPortInfoForBreakoutModeMixedBreakoutModeSuccess) {
  const std::string port = "Ethernet0";
  absl::string_view breakout_mode = "1x200G+2x100G";

  auto breakout_info =
      pins_test::GetExpectedPortInfoForBreakoutMode(port, breakout_mode);
  ASSERT_OK(breakout_info.status());
  EXPECT_EQ(breakout_info.value()["Ethernet0"].physical_channels, "[0,1,2,3]");
  EXPECT_EQ(breakout_info.value()["Ethernet4"].physical_channels, "[4,5]");
  EXPECT_EQ(breakout_info.value()["Ethernet6"].physical_channels, "[6,7]");
}

TEST_F(
    GNMIThinkitInterfaceUtilityTest,
    TestGetExpectedPortInfoForBreakoutModeAlternatedMixedBreakoutModeSuccess) {
  const std::string port = "Ethernet0";
  absl::string_view breakout_mode = "2x100G+1x200G";
  auto breakout_info =
      pins_test::GetExpectedPortInfoForBreakoutMode(port, breakout_mode);
  ASSERT_OK(breakout_info.status());
  EXPECT_EQ(breakout_info.value()["Ethernet0"].physical_channels, "[0,1]");
  EXPECT_EQ(breakout_info.value()["Ethernet2"].physical_channels, "[2,3]");
  EXPECT_EQ(breakout_info.value()["Ethernet4"].physical_channels, "[4,5,6,7]");
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetExpectedPortInfoForBreakoutModeWithQuotesSuccess) {
  const std::string port = "Ethernet0";
  absl::string_view breakout_mode = "\"1x400G\"";
  auto breakout_info =
      pins_test::GetExpectedPortInfoForBreakoutMode(port, breakout_mode);
  ASSERT_OK(breakout_info.status());
  EXPECT_EQ(breakout_info.value()["Ethernet0"].physical_channels,
            "[0,1,2,3,4,5,6,7]");
}

}  // namespace pins_test
