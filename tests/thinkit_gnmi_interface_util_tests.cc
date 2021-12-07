#include <cstdio>
#include <memory>
#include <string>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
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

constexpr char get_xcvrd_req_str[] =
    R"pb(prefix { origin: "openconfig" }
         path {
           elem { name: "interfaces" }
           elem {
             name: "interface"
             key { key: "name" value: "Ethernet0" }
           }
           elem { name: "state" }
           elem { name: "transceiver" }
         }
         type: STATE)pb";

constexpr char get_xcvrd_resp_str[] =
    R"pb(notification {
           timestamp: 1631864194292383538
           prefix { origin: "openconfig" }
           update {
             path {
               elem { name: "interfaces" }
               elem {
                 name: "interface"
                 key { key: "name" value: "Ethernet0" }
               }
               elem { name: "state" }
               elem { name: "transceiver" }
             }
             val {
               json_ietf_val: "{\"openconfig-platform-transceiver:transceiver\":\"Ethernet0\"}"
             }
           }
         }
    )pb";

constexpr char cable_len_req_str[] =
    R"pb(prefix { origin: "openconfig" }
         path {
           elem { name: "components" }
           elem {
             name: "component"
             key { key: "name" value: "Ethernet0" }
           }
           elem { name: "transceiver" }
           elem { name: "state" }
           elem { name: "openconfig-platform-ext:cable-length" }
         }
         type: STATE)pb";

constexpr char cable_len_resp_copper_str[] =
    R"pb(notification {
           timestamp: 1631864194292383538
           prefix { origin: "openconfig" }
           update {
             path {
               elem { name: "components" }
               elem {
                 name: "component"
                 key { key: "name" value: "Ethernet0" }
               }
               elem { name: "transceiver" }
               elem { name: "state" }
               elem { name: "openconfig-platform-ext:cable-length" }
             }
             val {
               json_ietf_val: "{\"openconfig-platform-ext:cable-length\":\"10\"}"
             }
           }
         }
    )pb";

constexpr char cable_len_resp_optic_str[] =
    R"pb(notification {
           timestamp: 1631864194292383538
           prefix { origin: "openconfig" }
           update {
             path {
               elem { name: "components" }
               elem {
                 name: "component"
                 key { key: "name" value: "Ethernet0" }
               }
               elem { name: "transceiver" }
               elem { name: "state" }
               elem { name: "cable-length" }
             }
             val {
               json_ietf_val: "{\"openconfig-platform-ext:cable-length\":\"0\"}"
             }
           }
         }
    )pb";

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
                 json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet0\",\"state\":{\"oper-status\":\"UP\",\"openconfig-p4rt:id\": 1}},{\"name\":\"Ethernet8\",\"state\":{\"oper-status\":\"UP\",\"openconfig-p4rt:id\": 2}}]}}"
               }
             }
           }
      )pb",
      &resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(req), _))
      .WillRepeatedly(DoAll(SetArgPointee<2>(resp), Return(grpc::Status::OK)));
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
                 json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet0\",\"state\":{\"oper-status\":\"UP\",\"openconfig-p4rt:id\": 1}},{\"name\":\"Ethernet8\",\"state\":{\"oper-status\":\"UP\"}},{\"name\":\"Ethernet16\",\"state\":{\"oper-status\":\"UP\",\"openconfig-p4rt:id\": 2}}]}}"
               }
             }
           }
      )pb",
      &resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(req), _))
      .WillRepeatedly(DoAll(SetArgPointee<2>(resp), Return(grpc::Status::OK)));
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
       TestGetRandomPortWithSupportedBreakoutModesIntfNameToPortIdGetFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
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
                 json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet0\",\"state\":{\"oper-status\":\"UP\",\"openconfig-p4rt:id\": 1}},{\"name\":\"Ethernet8\",\"state\":{\"oper-status\":\"UP\"}},{\"name\":\"Ethernet16\",\"state\":{\"oper-status\":\"UP\",\"openconfig-p4rt:id\": 2}}]}}"
               }
             }
           }
      )pb",
      &resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(req), _))
      .WillOnce(DoAll(SetArgPointee<2>(resp), Return(grpc::Status::OK)))
      .WillOnce(Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  EXPECT_THAT(
      pins_test::GetRandomPortWithSupportedBreakoutModes(*mock_gnmi_stub_ptr,
                                                         ""),
      StatusIs(absl::StatusCode::kDeadlineExceeded,
               HasSubstr("Failed to get interface name to p4rt id map")));
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
      .WillRepeatedly(DoAll(SetArgPointee<2>(resp), Return(grpc::Status::OK)));
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
                 json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet0\",\"state\":{\"oper-status\":\"DOWN\",\"openconfig-p4rt:id\": 1}}, {\"name\":\"Ethernet8\",\"state\":{\"oper-status\":\"DOWN\",\"openconfig-p4rt:id\": 2}}]}}"
               }
             }
           }
      )pb",
      &resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(req), _))
      .WillRepeatedly(DoAll(SetArgPointee<2>(resp), Return(grpc::Status::OK)));
  EXPECT_THAT(
      pins_test::GetRandomPortWithSupportedBreakoutModes(
          *mock_gnmi_stub_ptr, platform_json_contents),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr("No operationally up parent ports found on switch")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetRandomPortWithSupportedBreakoutModesNoPortsWithP4rtIDFailure) {
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
                 json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet0\",\"state\":{\"oper-status\":\"UP\"}}, {\"name\":\"Ethernet8\",\"state\":{\"oper-status\":\"UP\"}}]}}"
               }
             }
           }
      )pb",
      &resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(req), _))
      .WillRepeatedly(DoAll(SetArgPointee<2>(resp), Return(grpc::Status::OK)));
  EXPECT_THAT(
      pins_test::GetRandomPortWithSupportedBreakoutModes(
          *mock_gnmi_stub_ptr, platform_json_contents),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr(
                   "No random interface with supported breakout modes found")));
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
      .WillRepeatedly(DoAll(SetArgPointee<2>(resp), Return(grpc::Status::OK)));
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
                 json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet0\",\"state\":{\"oper-status\":\"UP\",\"openconfig-p4rt:id\": 1}}]}}"
               }
             }
           }
      )pb",
      &resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(req), _))
      .WillRepeatedly(DoAll(SetArgPointee<2>(resp), Return(grpc::Status::OK)));
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
                 json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet0\",\"state\":{\"oper-status\":\"UP\",\"openconfig-p4rt:id\": 1}}]}}"
               }
             }
           }
      )pb",
      &resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(req), _))
      .WillRepeatedly(DoAll(SetArgPointee<2>(resp), Return(grpc::Status::OK)));
  EXPECT_THAT(pins_test::GetRandomPortWithSupportedBreakoutModes(
                  *mock_gnmi_stub_ptr, platform_json_contents),
              StatusIs(absl::StatusCode::kInternal,
                       HasSubstr("Default breakout mode not found for "
                                 "Ethernet0 in platform.json")));
}

TEST_F(
    GNMIThinkitInterfaceUtilityTest,
    TestGetRandomPortWithSupportedBreakoutModesSupportedModesNotFoundFailure) {
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
                 json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet0\",\"state\":{\"oper-status\":\"UP\",\"openconfig-p4rt:id\": 1}}]}}"
               }
             }
           }
      )pb",
      &resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(req), _))
      .WillRepeatedly(DoAll(SetArgPointee<2>(resp), Return(grpc::Status::OK)));
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
                 json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet0\",\"state\":{\"oper-status\":\"UP\",\"openconfig-p4rt:id\": 1}},{\"name\":\"Ethernet8\",\"state\":{\"oper-status\":\"UP\",\"openconfig-p4rt:id\": 2}}]}}"
               }
             }
           }
      )pb",
      &resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(req), _))
      .WillRepeatedly(DoAll(SetArgPointee<2>(resp), Return(grpc::Status::OK)));
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
  absl::string_view breakout_mode = "1x200G(4)+2x100G(4)";

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
  absl::string_view breakout_mode = "2x100G(4)+1x200G(4)";
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

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetExpectedPortInfoForBreakoutModeEmptyBreakoutModeFailure) {
  const std::string port = "Ethernet0";
  absl::string_view breakout_mode = "";

  EXPECT_THAT(
      pins_test::GetExpectedPortInfoForBreakoutMode(port, breakout_mode),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr("Found empty breakout mode")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetExpectedPortInfoForBreakoutModePortNumberIntConversionFailure) {
  const std::string port = "EthernetX";
  absl::string_view breakout_mode = "1x400G";

  EXPECT_THAT(
      pins_test::GetExpectedPortInfoForBreakoutMode(port, breakout_mode),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr("Failed to convert string (X) to integer")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetExpectedPortInfoForBreakoutModeNonParentPortFailure) {
  const std::string port = "Ethernet4";
  absl::string_view breakout_mode = "1x400G";

  EXPECT_THAT(
      pins_test::GetExpectedPortInfoForBreakoutMode(port, breakout_mode),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr("Requested port (Ethernet4) is not a parent port")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetExpectedPortInfoForBreakoutModeNumBreakoutsIntConversionFailure) {
  const std::string port = "Ethernet0";
  absl::string_view breakout_mode = "InvalidNumBreakoutsx400G";

  EXPECT_THAT(
      pins_test::GetExpectedPortInfoForBreakoutMode(port, breakout_mode),
      StatusIs(
          absl::StatusCode::kInternal,
          HasSubstr(
              "Failed to convert string (InvalidNumBreakouts) to integer")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetExpectedPortInfoForBreakoutModeInvalidBreakoutModeFailure) {
  const std::string port = "Ethernet0";
  absl::string_view breakout_mode = "3x200G(4)+2x100G(4)";

  EXPECT_THAT(
      pins_test::GetExpectedPortInfoForBreakoutMode(port, breakout_mode),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr(absl::StrCat("Invalid breakout mode (", breakout_mode,
                                      ") found"))));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetBreakoutStateInfoForPortSuccess) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string port = "Ethernet0";
  const std::string breakout_mode = "1x400G";
  gnmi::GetRequest physical_channels_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(prefix { origin: "openconfig" }
           path {
             elem { name: "interfaces" }
             elem {
               name: "interface"
               key { key: "name" value: "Ethernet0" }
             }
             elem { name: "state" }
             elem { name: "physical-channel" }
           }
           type: STATE)pb",
      &physical_channels_req));
  gnmi::GetResponse physical_channels_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1632102697805380043
             prefix { origin: "openconfig" }
             update {
               path {
                 elem { name: "interfaces" }
                 elem {
                   name: "interface"
                   key { key: "name" value: "Ethernet0" }
                 }
                 elem { name: "state" }
                 elem { name: "physical-channel" }
               }
               val {
                 json_ietf_val: "{\"openconfig-platform-transceiver:physical-channel\":[0,1,2,3,4,5,6,7]}"
               }
             }
           })pb",
      &physical_channels_resp));
  gnmi::GetRequest oper_status_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(prefix { origin: "openconfig" }
           path {
             elem { name: "interfaces" }
             elem {
               name: "interface"
               key { key: "name" value: "Ethernet0" }
             }
             elem { name: "state" }
             elem { name: "oper-status" }
           }
           type: STATE)pb",
      &oper_status_req));
  gnmi::GetResponse oper_status_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1632102697699213032
             prefix { origin: "openconfig" }
             update {
               path {
                 elem { name: "interfaces" }
                 elem {
                   name: "interface"
                   key { key: "name" value: "Ethernet0" }
                 }
                 elem { name: "state" }
                 elem { name: "oper-status" }
               }
               val {
                 json_ietf_val: "{\"openconfig-interfaces:oper-status\":\"UP\"}"
               }
             }
           })pb",
      &oper_status_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr,
              Get(_, EqualsProto(physical_channels_req), _))
      .WillOnce(DoAll(SetArgPointee<2>(physical_channels_resp),
                      Return(grpc::Status::OK)));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(oper_status_req), _))
      .WillOnce(
          DoAll(SetArgPointee<2>(oper_status_resp), Return(grpc::Status::OK)));
  auto breakout_state_info = pins_test::GetBreakoutStateInfoForPort(
      mock_gnmi_stub_ptr.get(), port, breakout_mode);
  ASSERT_OK(breakout_state_info.status());
  EXPECT_EQ(breakout_state_info.value()["Ethernet0"].physical_channels,
            "[0,1,2,3,4,5,6,7]");
  EXPECT_EQ(breakout_state_info.value()["Ethernet0"].oper_status, "\"UP\"");
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetBreakoutStateInfoForPortExpectedBreakoutInfoFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string port = "Ethernet0";
  const std::string breakout_mode = "";
  EXPECT_THAT(pins_test::GetBreakoutStateInfoForPort(mock_gnmi_stub_ptr.get(),
                                                     port, breakout_mode),
              StatusIs(absl::StatusCode::kInternal,
                       HasSubstr(("Found empty breakout mode"))));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetBreakoutStateInfoForPortPhysicalChannelsGetFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string port = "Ethernet0";
  const std::string breakout_mode = "1x400G";
  gnmi::GetRequest physical_channels_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(prefix { origin: "openconfig" }
           path {
             elem { name: "interfaces" }
             elem {
               name: "interface"
               key { key: "name" value: "Ethernet0" }
             }
             elem { name: "state" }
             elem { name: "physical-channel" }
           }
           type: STATE)pb",
      &physical_channels_req));
  gnmi::GetRequest oper_status_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(prefix { origin: "openconfig" }
           path {
             elem { name: "interfaces" }
             elem {
               name: "interface"
               key { key: "name" value: "Ethernet0" }
             }
             elem { name: "state" }
             elem { name: "oper-status" }
           }
           type: STATE)pb",
      &oper_status_req));
  gnmi::GetResponse oper_status_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1632102697699213032
             prefix { origin: "openconfig" }
             update {
               path {
                 elem { name: "interfaces" }
                 elem {
                   name: "interface"
                   key { key: "name" value: "Ethernet0" }
                 }
                 elem { name: "state" }
                 elem { name: "oper-status" }
               }
               val {
                 json_ietf_val: "{\"openconfig-interfaces:oper-status\":\"UP\"}"
               }
             }
           })pb",
      &oper_status_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(oper_status_req), _))
      .WillOnce(
          DoAll(SetArgPointee<2>(oper_status_resp), Return(grpc::Status::OK)));
  EXPECT_CALL(*mock_gnmi_stub_ptr,
              Get(_, EqualsProto(physical_channels_req), _))
      .WillOnce(Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  EXPECT_THAT(pins_test::GetBreakoutStateInfoForPort(mock_gnmi_stub_ptr.get(),
                                                     port, breakout_mode),
              StatusIs(absl::StatusCode::kDeadlineExceeded,
                       HasSubstr("Failed to get GNMI state path value for "
                                 "physical-channels for port Ethernet0")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetBreakoutStateInfoForPortOperStatusGetFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string port = "Ethernet0";
  const std::string breakout_mode = "1x400G";
  gnmi::GetRequest oper_status_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(prefix { origin: "openconfig" }
           path {
             elem { name: "interfaces" }
             elem {
               name: "interface"
               key { key: "name" value: "Ethernet0" }
             }
             elem { name: "state" }
             elem { name: "oper-status" }
           }
           type: STATE)pb",
      &oper_status_req));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(oper_status_req), _))
      .WillOnce(Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  EXPECT_THAT(pins_test::GetBreakoutStateInfoForPort(mock_gnmi_stub_ptr.get(),
                                                     port, breakout_mode),
              StatusIs(absl::StatusCode::kDeadlineExceeded,
                       HasSubstr("Failed to get GNMI state path value for "
                                 "oper-status for port Ethernet0")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetBreakoutModeConfigFromStringUnchannelizedBreakoutModeSuccess) {
  const std::string port_index = "1";
  const std::string intf_name = "Ethernet0";
  const std::string breakout_mode = "1x400G";
  gnmi::SetRequest req, expected_breakout_config;
  const std::string expected_breakout_config_str =
      R"pb(
    prefix { origin: "openconfig" }
    replace {
      path {}
      val {
        json_ietf_val: "{\n             \"openconfig-interfaces:interfaces\": { \"interface\": [ {\n             \"config\": {\n               \"enabled\": true,\n               \"loopback-mode\": false,\n               \"mtu\": 9216,\n               \"name\": \"Ethernet0\",\n               \"type\": \"iana-if-type:ethernetCsmacd\"\n             },\n             \"name\": \"Ethernet0\",\n             \"openconfig-if-ethernet:ethernet\": {\n               \"config\": { \"port-speed\": \"openconfig-if-ethernet:SPEED_400GB\" }\n             },\n             \"subinterfaces\": {\n               \"subinterface\":\n               [ {\n                 \"config\": { \"index\": 0 },\n                 \"index\": 0,\n                 \"openconfig-if-ip:ipv6\": {\n                   \"unnumbered\": { \"config\": { \"enabled\": true } }\n                 }\n               }]\n             }\n           }\n       ] },\n             \"openconfig-platform:components\": {\n               \"component\":\n               [ {\n                 \"name\": \"1/1\",\n                 \"config\": { \"name\": \"1/1\" },\n                 \"port\": {\n                   \"config\": { \"port-id\": 1 },\n                   \"breakout-mode\": { \"groups\": { \"group\": [ {\n             \"config\": {\n               \"breakout-speed\": \"openconfig-if-ethernet:SPEED_400GB\",\n               \"index\": 0,\n               \"num-breakouts\": 1,\n               \"num-physical-channels\": 8\n             },\n             \"index\": 0\n           } ] } }\n                 }\n               }]\n             }\n           }"
      }
    })pb";
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      expected_breakout_config_str, &expected_breakout_config));
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  gnmi::GetRequest get_xcvrd_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(get_xcvrd_req_str,
                                                            &get_xcvrd_req));
  gnmi::GetResponse get_xcvrd_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(get_xcvrd_resp_str,
                                                            &get_xcvrd_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(get_xcvrd_req), _))
      .WillOnce(
          DoAll(SetArgPointee<2>(get_xcvrd_resp), Return(grpc::Status::OK)));
  gnmi::GetRequest cable_len_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(cable_len_req_str,
                                                            &cable_len_req));
  gnmi::GetResponse cable_len_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      cable_len_resp_optic_str, &cable_len_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(cable_len_req), _))
      .WillOnce(
          DoAll(SetArgPointee<2>(cable_len_resp), Return(grpc::Status::OK)));
  ASSERT_OK(pins_test::GetBreakoutModeConfigFromString(
      req, mock_gnmi_stub_ptr.get(), port_index, intf_name, breakout_mode));
  EXPECT_THAT(req, EqualsProto(expected_breakout_config));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetBreakoutModeConfigFromStringChannelizedBreakoutModeSuccess) {
  const std::string port_index = "1";
  const std::string intf_name = "Ethernet0";
  const std::string breakout_mode = "2x200G";
  gnmi::SetRequest req, expected_breakout_config;
  const std::string expected_breakout_config_str = R"pb(
    prefix { origin: "openconfig" }
    replace {
      path {}
      val {
        json_ietf_val: "{\n             \"openconfig-interfaces:interfaces\": { \"interface\": [ {\n             \"config\": {\n               \"enabled\": true,\n               \"loopback-mode\": false,\n               \"mtu\": 9216,\n               \"name\": \"Ethernet0\",\n               \"type\": \"iana-if-type:ethernetCsmacd\"\n             },\n             \"name\": \"Ethernet0\",\n             \"openconfig-if-ethernet:ethernet\": {\n               \"config\": { \"port-speed\": \"openconfig-if-ethernet:SPEED_200GB\" }\n             },\n             \"subinterfaces\": {\n               \"subinterface\":\n               [ {\n                 \"config\": { \"index\": 0 },\n                 \"index\": 0,\n                 \"openconfig-if-ip:ipv6\": {\n                   \"unnumbered\": { \"config\": { \"enabled\": true } }\n                 }\n               }]\n             }\n           }\n      ,{\n             \"config\": {\n               \"enabled\": true,\n               \"loopback-mode\": false,\n               \"mtu\": 9216,\n               \"name\": \"Ethernet4\",\n               \"type\": \"iana-if-type:ethernetCsmacd\"\n             },\n             \"name\": \"Ethernet4\",\n             \"openconfig-if-ethernet:ethernet\": {\n               \"config\": { \"port-speed\": \"openconfig-if-ethernet:SPEED_200GB\" }\n             },\n             \"subinterfaces\": {\n               \"subinterface\":\n               [ {\n                 \"config\": { \"index\": 0 },\n                 \"index\": 0,\n                 \"openconfig-if-ip:ipv6\": {\n                   \"unnumbered\": { \"config\": { \"enabled\": true } }\n                 }\n               }]\n             }\n           }\n       ] },\n             \"openconfig-platform:components\": {\n               \"component\":\n               [ {\n                 \"name\": \"1/1\",\n                 \"config\": { \"name\": \"1/1\" },\n                 \"port\": {\n                   \"config\": { \"port-id\": 1 },\n                   \"breakout-mode\": { \"groups\": { \"group\": [ {\n             \"config\": {\n               \"breakout-speed\": \"openconfig-if-ethernet:SPEED_200GB\",\n               \"index\": 0,\n               \"num-breakouts\": 2,\n               \"num-physical-channels\": 4\n             },\n             \"index\": 0\n           } ] } }\n                 }\n               }]\n             }\n           }"
      }
    }
  )pb";
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      expected_breakout_config_str, &expected_breakout_config));
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  gnmi::GetRequest get_xcvrd_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(get_xcvrd_req_str,
                                                            &get_xcvrd_req));
  gnmi::GetResponse get_xcvrd_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(get_xcvrd_resp_str,
                                                            &get_xcvrd_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(get_xcvrd_req), _))
      .WillOnce(
          DoAll(SetArgPointee<2>(get_xcvrd_resp), Return(grpc::Status::OK)));
  gnmi::GetRequest cable_len_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(cable_len_req_str,
                                                            &cable_len_req));
  gnmi::GetResponse cable_len_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      cable_len_resp_optic_str, &cable_len_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(cable_len_req), _))
      .WillOnce(
          DoAll(SetArgPointee<2>(cable_len_resp), Return(grpc::Status::OK)));
  ASSERT_OK(pins_test::GetBreakoutModeConfigFromString(
      req, mock_gnmi_stub_ptr.get(), port_index, intf_name, breakout_mode));
  EXPECT_THAT(req, EqualsProto(expected_breakout_config));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetBreakoutModeConfigFromStringMixedBreakoutModeSuccess) {
  const std::string port_index = "1";
  const std::string intf_name = "Ethernet0";
  const std::string breakout_mode = "1x200G(4)+2x100G(4)";
  gnmi::SetRequest req, expected_breakout_config;
  const std::string expected_breakout_config_str = R"pb(
    prefix { origin: "openconfig" }
    replace {
      path {}
      val {
        json_ietf_val: "{\n             \"openconfig-interfaces:interfaces\": { \"interface\": [ {\n             \"config\": {\n               \"enabled\": true,\n               \"loopback-mode\": false,\n               \"mtu\": 9216,\n               \"name\": \"Ethernet0\",\n               \"type\": \"iana-if-type:ethernetCsmacd\"\n             },\n             \"name\": \"Ethernet0\",\n             \"openconfig-if-ethernet:ethernet\": {\n               \"config\": { \"port-speed\": \"openconfig-if-ethernet:SPEED_200GB\" }\n             },\n             \"subinterfaces\": {\n               \"subinterface\":\n               [ {\n                 \"config\": { \"index\": 0 },\n                 \"index\": 0,\n                 \"openconfig-if-ip:ipv6\": {\n                   \"unnumbered\": { \"config\": { \"enabled\": true } }\n                 }\n               }]\n             }\n           }\n      ,{\n             \"config\": {\n               \"enabled\": true,\n               \"loopback-mode\": false,\n               \"mtu\": 9216,\n               \"name\": \"Ethernet4\",\n               \"type\": \"iana-if-type:ethernetCsmacd\"\n             },\n             \"name\": \"Ethernet4\",\n             \"openconfig-if-ethernet:ethernet\": {\n               \"config\": { \"port-speed\": \"openconfig-if-ethernet:SPEED_100GB\" }\n             },\n             \"subinterfaces\": {\n               \"subinterface\":\n               [ {\n                 \"config\": { \"index\": 0 },\n                 \"index\": 0,\n                 \"openconfig-if-ip:ipv6\": {\n                   \"unnumbered\": { \"config\": { \"enabled\": true } }\n                 }\n               }]\n             }\n           }\n      ,{\n             \"config\": {\n               \"enabled\": true,\n               \"loopback-mode\": false,\n               \"mtu\": 9216,\n               \"name\": \"Ethernet6\",\n               \"type\": \"iana-if-type:ethernetCsmacd\"\n             },\n             \"name\": \"Ethernet6\",\n             \"openconfig-if-ethernet:ethernet\": {\n               \"config\": { \"port-speed\": \"openconfig-if-ethernet:SPEED_100GB\" }\n             },\n             \"subinterfaces\": {\n               \"subinterface\":\n               [ {\n                 \"config\": { \"index\": 0 },\n                 \"index\": 0,\n                 \"openconfig-if-ip:ipv6\": {\n                   \"unnumbered\": { \"config\": { \"enabled\": true } }\n                 }\n               }]\n             }\n           }\n       ] },\n             \"openconfig-platform:components\": {\n               \"component\":\n               [ {\n                 \"name\": \"1/1\",\n                 \"config\": { \"name\": \"1/1\" },\n                 \"port\": {\n                   \"config\": { \"port-id\": 1 },\n                   \"breakout-mode\": { \"groups\": { \"group\": [ {\n             \"config\": {\n               \"breakout-speed\": \"openconfig-if-ethernet:SPEED_200GB\",\n               \"index\": 0,\n               \"num-breakouts\": 1,\n               \"num-physical-channels\": 4\n             },\n             \"index\": 0\n           },{\n             \"config\": {\n               \"breakout-speed\": \"openconfig-if-ethernet:SPEED_100GB\",\n               \"index\": 1,\n               \"num-breakouts\": 2,\n               \"num-physical-channels\": 2\n             },\n             \"index\": 1\n           } ] } }\n                 }\n               }]\n             }\n           }"
      }
    }
  )pb";
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      expected_breakout_config_str, &expected_breakout_config));
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  gnmi::GetRequest get_xcvrd_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(get_xcvrd_req_str,
                                                            &get_xcvrd_req));
  gnmi::GetResponse get_xcvrd_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(get_xcvrd_resp_str,
                                                            &get_xcvrd_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(get_xcvrd_req), _))
      .WillOnce(
          DoAll(SetArgPointee<2>(get_xcvrd_resp), Return(grpc::Status::OK)));
  gnmi::GetRequest cable_len_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(cable_len_req_str,
                                                            &cable_len_req));
  gnmi::GetResponse cable_len_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      cable_len_resp_optic_str, &cable_len_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(cable_len_req), _))
      .WillOnce(
          DoAll(SetArgPointee<2>(cable_len_resp), Return(grpc::Status::OK)));
  ASSERT_OK(pins_test::GetBreakoutModeConfigFromString(
      req, mock_gnmi_stub_ptr.get(), port_index, intf_name, breakout_mode));
  EXPECT_THAT(req, EqualsProto(expected_breakout_config));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetBreakoutModeConfigFromStringCopperPortSuccess) {
  const std::string port_index = "1";
  const std::string intf_name = "Ethernet0";
  const std::string breakout_mode = "1x200G(4)+2x100G(4)";
  gnmi::SetRequest req, expected_breakout_config;
  const std::string expected_breakout_config_str = R"pb(
    prefix { origin: "openconfig" }
    replace {
      path {}
      val {
        json_ietf_val: "{\n             \"openconfig-interfaces:interfaces\": { \"interface\": [ {\n               \"config\": {\n                 \"enabled\": true,\n                 \"loopback-mode\": false,\n                 \"mtu\": 9216,\n                 \"name\": \"Ethernet0\",\n                 \"type\": \"iana-if-type:ethernetCsmacd\"\n               },\n               \"name\": \"Ethernet0\",\n               \"openconfig-if-ethernet:ethernet\": {\n                 \"config\": {\n                   \"port-speed\": \"openconfig-if-ethernet:SPEED_200GB\",\n                   \"standalone-link-training\": true\n                 }\n               },\n               \"subinterfaces\": {\n                 \"subinterface\":\n                 [ {\n                   \"config\": { \"index\": 0 },\n                   \"index\": 0,\n                   \"openconfig-if-ip:ipv6\": {\n                     \"unnumbered\": { \"config\": { \"enabled\": true } }\n                   }\n                 }]\n               }\n             }\n        ,{\n               \"config\": {\n                 \"enabled\": true,\n                 \"loopback-mode\": false,\n                 \"mtu\": 9216,\n                 \"name\": \"Ethernet4\",\n                 \"type\": \"iana-if-type:ethernetCsmacd\"\n               },\n               \"name\": \"Ethernet4\",\n               \"openconfig-if-ethernet:ethernet\": {\n                 \"config\": {\n                   \"port-speed\": \"openconfig-if-ethernet:SPEED_100GB\",\n                   \"standalone-link-training\": true\n                 }\n               },\n               \"subinterfaces\": {\n                 \"subinterface\":\n                 [ {\n                   \"config\": { \"index\": 0 },\n                   \"index\": 0,\n                   \"openconfig-if-ip:ipv6\": {\n                     \"unnumbered\": { \"config\": { \"enabled\": true } }\n                   }\n                 }]\n               }\n             }\n        ,{\n               \"config\": {\n                 \"enabled\": true,\n                 \"loopback-mode\": false,\n                 \"mtu\": 9216,\n                 \"name\": \"Ethernet6\",\n                 \"type\": \"iana-if-type:ethernetCsmacd\"\n               },\n               \"name\": \"Ethernet6\",\n               \"openconfig-if-ethernet:ethernet\": {\n                 \"config\": {\n                   \"port-speed\": \"openconfig-if-ethernet:SPEED_100GB\",\n                   \"standalone-link-training\": true\n                 }\n               },\n               \"subinterfaces\": {\n                 \"subinterface\":\n                 [ {\n                   \"config\": { \"index\": 0 },\n                   \"index\": 0,\n                   \"openconfig-if-ip:ipv6\": {\n                     \"unnumbered\": { \"config\": { \"enabled\": true } }\n                   }\n                 }]\n               }\n             }\n         ] },\n             \"openconfig-platform:components\": {\n               \"component\":\n               [ {\n                 \"name\": \"1/1\",\n                 \"config\": { \"name\": \"1/1\" },\n                 \"port\": {\n                   \"config\": { \"port-id\": 1 },\n                   \"breakout-mode\": { \"groups\": { \"group\": [ {\n             \"config\": {\n               \"breakout-speed\": \"openconfig-if-ethernet:SPEED_200GB\",\n               \"index\": 0,\n               \"num-breakouts\": 1,\n               \"num-physical-channels\": 4\n             },\n             \"index\": 0\n           },{\n             \"config\": {\n               \"breakout-speed\": \"openconfig-if-ethernet:SPEED_100GB\",\n               \"index\": 1,\n               \"num-breakouts\": 2,\n               \"num-physical-channels\": 2\n             },\n             \"index\": 1\n           } ] } }\n                 }\n               }]\n             }\n           }"
      }
    }
  )pb";
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      expected_breakout_config_str, &expected_breakout_config));
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  gnmi::GetRequest get_xcvrd_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(get_xcvrd_req_str,
                                                            &get_xcvrd_req));
  gnmi::GetResponse get_xcvrd_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(get_xcvrd_resp_str,
                                                            &get_xcvrd_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(get_xcvrd_req), _))
      .WillOnce(
          DoAll(SetArgPointee<2>(get_xcvrd_resp), Return(grpc::Status::OK)));
  gnmi::GetRequest cable_len_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(cable_len_req_str,
                                                            &cable_len_req));
  gnmi::GetResponse cable_len_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      cable_len_resp_copper_str, &cable_len_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(cable_len_req), _))
      .WillOnce(
          DoAll(SetArgPointee<2>(cable_len_resp), Return(grpc::Status::OK)));
  ASSERT_OK(pins_test::GetBreakoutModeConfigFromString(
      req, mock_gnmi_stub_ptr.get(), port_index, intf_name, breakout_mode));
  EXPECT_THAT(req, EqualsProto(expected_breakout_config));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetBreakoutModeConfigFromStringIntConversionFailure) {
  const std::string port_index = "1";
  const std::string intf_name = "Ethernet0";
  const std::string breakout_mode = "Xx400G";
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  gnmi::GetRequest get_xcvrd_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(get_xcvrd_req_str,
                                                            &get_xcvrd_req));
  gnmi::GetResponse get_xcvrd_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(get_xcvrd_resp_str,
                                                            &get_xcvrd_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(get_xcvrd_req), _))
      .WillOnce(
          DoAll(SetArgPointee<2>(get_xcvrd_resp), Return(grpc::Status::OK)));
  gnmi::GetRequest cable_len_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(cable_len_req_str,
                                                            &cable_len_req));
  gnmi::GetResponse cable_len_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      cable_len_resp_optic_str, &cable_len_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(cable_len_req), _))
      .WillOnce(
          DoAll(SetArgPointee<2>(cable_len_resp), Return(grpc::Status::OK)));
  gnmi::SetRequest req;
  EXPECT_THAT(
      pins_test::GetBreakoutModeConfigFromString(
          req, mock_gnmi_stub_ptr.get(), port_index, intf_name, breakout_mode),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr("Failed to convert string (X) to integer")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetBreakoutModeConfigFromStringIsCopperPortFailure) {
  const std::string port_index = "1";
  const std::string intf_name = "Ethernet0";
  const std::string breakout_mode = "Xx400G";
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  gnmi::GetRequest get_xcvrd_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(prefix { origin: "openconfig" }
           path {
             elem { name: "interfaces" }
             elem {
               name: "interface"
               key { key: "name" value: "Ethernet0" }
             }
             elem { name: "state" }
             elem { name: "transceiver" }
           }
           type: STATE)pb",
      &get_xcvrd_req));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(get_xcvrd_req), _))
      .WillOnce(Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  gnmi::SetRequest req;
  EXPECT_THAT(
      pins_test::GetBreakoutModeConfigFromString(
          req, mock_gnmi_stub_ptr.get(), port_index, intf_name, breakout_mode),
      StatusIs(absl::StatusCode::kDeadlineExceeded,
               HasSubstr("Failed to get GNMI state path value for port "
                         "transceiver for port Ethernet0")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetNonExistingPortsAfterBreakoutForBreakoutAppliedSuccess) {
  absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>
      orig_breakout_info;
  orig_breakout_info["Ethernet0"] =
      pins_test::PortBreakoutInfo{"[0,1,2,3,4,5,6,7]", pins_test::kStateUp};
  absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>
      new_breakout_info;
  new_breakout_info["Ethernet0"] =
      pins_test::PortBreakoutInfo{"[0,1,2,3]", pins_test::kStateUp};
  new_breakout_info["Ethernet4"] =
      pins_test::PortBreakoutInfo{"[4,5,6,7]", pins_test::kStateUp};

  std::vector<std::string> expected_non_existing_ports;
  EXPECT_THAT(GetNonExistingPortsAfterBreakout(orig_breakout_info,
                                               new_breakout_info, true),
              ContainerEq(expected_non_existing_ports));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetNonExistingPortsAfterBreakoutForBreakoutAppliedAlternateSuccess) {
  absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>
      orig_breakout_info;
  orig_breakout_info["Ethernet0"] =
      pins_test::PortBreakoutInfo{"[0,1,2,3]", pins_test::kStateUp};
  orig_breakout_info["Ethernet4"] =
      pins_test::PortBreakoutInfo{"[4,5,6,7]", pins_test::kStateUp};
  absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>
      new_breakout_info;
  new_breakout_info["Ethernet0"] =
      pins_test::PortBreakoutInfo{"[0,1,2,3,4,5,6,7]", pins_test::kStateUp};

  std::vector<std::string> expected_non_existing_ports{"Ethernet4"};
  EXPECT_THAT(GetNonExistingPortsAfterBreakout(orig_breakout_info,
                                               new_breakout_info, true),
              ContainerEq(expected_non_existing_ports));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetNonExistingPortsAfterBreakoutForBreakoutNotAppliedSuccess) {
  absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>
      orig_breakout_info;
  orig_breakout_info["Ethernet0"] =
      pins_test::PortBreakoutInfo{"[0,1,2,3,4,5,6,7]", pins_test::kStateUp};
  absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>
      new_breakout_info;
  new_breakout_info["Ethernet0"] =
      pins_test::PortBreakoutInfo{"[0,1,2,3]", pins_test::kStateDown};
  new_breakout_info["Ethernet4"] =
      pins_test::PortBreakoutInfo{"[4,5,6,7]", pins_test::kStateDown};

  std::vector<std::string> expected_non_existing_ports{"Ethernet4"};
  EXPECT_THAT(GetNonExistingPortsAfterBreakout(orig_breakout_info,
                                               new_breakout_info, false),
              ContainerEq(expected_non_existing_ports));
}

TEST_F(
    GNMIThinkitInterfaceUtilityTest,
    TestGetNonExistingPortsAfterBreakoutForBreakoutNotAppliedAlternateSuccess) {
  absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>
      orig_breakout_info;
  orig_breakout_info["Ethernet0"] =
      pins_test::PortBreakoutInfo{"[0,1,2,3]", pins_test::kStateUp};
  orig_breakout_info["Ethernet4"] =
      pins_test::PortBreakoutInfo{"[4,5,6,7]", pins_test::kStateUp};
  absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>
      new_breakout_info;
  new_breakout_info["Ethernet0"] =
      pins_test::PortBreakoutInfo{"[0,1,2,3,4,5,6,7]", pins_test::kStateDown};

  std::vector<std::string> expected_non_existing_ports{};
  EXPECT_THAT(GetNonExistingPortsAfterBreakout(orig_breakout_info,
                                               new_breakout_info, false),
              ContainerEq(expected_non_existing_ports));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestValidateBreakoutStateEmptyExpectedInfoFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>
      expected_port_info;
  std::vector<std::string> non_existing_port_list;
  EXPECT_THAT(
      pins_test::ValidateBreakoutState(
          mock_gnmi_stub_ptr.get(), expected_port_info, non_existing_port_list),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr("Expected port info map is empty")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestValidateBreakoutStateOperStatusMatchFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>
      expected_port_info;
  expected_port_info["Ethernet0"] =
      pins_test::PortBreakoutInfo{"[0,1,2,3,4,5,6,7]", pins_test::kStateUp};
  std::vector<std::string> non_existing_port_list;
  gnmi::GetRequest oper_status_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(prefix { origin: "openconfig" }
           path {
             elem { name: "interfaces" }
             elem {
               name: "interface"
               key { key: "name" value: "Ethernet0" }
             }
             elem { name: "state" }
             elem { name: "oper-status" }
           }
           type: STATE)pb",
      &oper_status_req));
  gnmi::GetResponse oper_status_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1632102697699213032
             prefix { origin: "openconfig" }
             update {
               path {
                 elem { name: "interfaces" }
                 elem {
                   name: "interface"
                   key { key: "name" value: "Ethernet0" }
                 }
                 elem { name: "state" }
                 elem { name: "oper-status" }
               }
               val {
                 json_ietf_val: "{\"openconfig-interfaces:oper-status\":\"DOWN\"}"
               }
             }
           })pb",
      &oper_status_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(oper_status_req), _))
      .WillOnce(
          DoAll(SetArgPointee<2>(oper_status_resp), Return(grpc::Status::OK)));
  EXPECT_THAT(
      pins_test::ValidateBreakoutState(
          mock_gnmi_stub_ptr.get(), expected_port_info, non_existing_port_list),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr(absl::StrCat(
                   "Port oper-status match failed for port Ethernet0. got: \"",
                   pins_test::kStateDown,
                   "\", want:", expected_port_info["Ethernet0"].oper_status))));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestValidateBreakoutStatePhysicalChannelsMatchFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>
      expected_port_info;
  expected_port_info["Ethernet0"] =
      pins_test::PortBreakoutInfo{"[0,1,2,3]", pins_test::kStateUp};
  std::vector<std::string> non_existing_port_list;
  gnmi::GetRequest oper_status_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(prefix { origin: "openconfig" }
           path {
             elem { name: "interfaces" }
             elem {
               name: "interface"
               key { key: "name" value: "Ethernet0" }
             }
             elem { name: "state" }
             elem { name: "oper-status" }
           }
           type: STATE)pb",
      &oper_status_req));
  gnmi::GetResponse oper_status_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1632102697699213032
             prefix { origin: "openconfig" }
             update {
               path {
                 elem { name: "interfaces" }
                 elem {
                   name: "interface"
                   key { key: "name" value: "Ethernet0" }
                 }
                 elem { name: "state" }
                 elem { name: "oper-status" }
               }
               val {
                 json_ietf_val: "{\"openconfig-interfaces:oper-status\":\"UP\"}"
               }
             }
           })pb",
      &oper_status_resp));
  gnmi::GetRequest physical_channels_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(prefix { origin: "openconfig" }
           path {
             elem { name: "interfaces" }
             elem {
               name: "interface"
               key { key: "name" value: "Ethernet0" }
             }
             elem { name: "state" }
             elem { name: "physical-channel" }
           }
           type: STATE)pb",
      &physical_channels_req));
  gnmi::GetResponse physical_channels_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1632102697805380043
             prefix { origin: "openconfig" }
             update {
               path {
                 elem { name: "interfaces" }
                 elem {
                   name: "interface"
                   key { key: "name" value: "Ethernet0" }
                 }
                 elem { name: "state" }
                 elem { name: "physical-channel" }
               }
               val {
                 json_ietf_val: "{\"openconfig-platform-transceiver:physical-channel\":[0,1,2,3,4,5,6,7]}"
               }
             }
           })pb",
      &physical_channels_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(oper_status_req), _))
      .WillOnce(
          DoAll(SetArgPointee<2>(oper_status_resp), Return(grpc::Status::OK)));
  EXPECT_CALL(*mock_gnmi_stub_ptr,
              Get(_, EqualsProto(physical_channels_req), _))
      .WillOnce(DoAll(SetArgPointee<2>(physical_channels_resp),
                      Return(grpc::Status::OK)));
  EXPECT_THAT(
      pins_test::ValidateBreakoutState(
          mock_gnmi_stub_ptr.get(), expected_port_info, non_existing_port_list),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr(absl::StrCat(
                   "Physical channel match failed for port Ethernet0. got: "
                   "[0,1,2,3,4,5,6,7], want: ",
                   expected_port_info["Ethernet0"].physical_channels))));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestValidateBreakoutStateNonExistingPortListMatchFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>
      expected_port_info;
  expected_port_info["Ethernet0"] =
      pins_test::PortBreakoutInfo{"[0,1,2,3,4,5,6,7]", pins_test::kStateUp};
  std::vector<std::string> non_existing_port_list{"Ethernet0"};
  gnmi::GetRequest oper_status_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(prefix { origin: "openconfig" }
           path {
             elem { name: "interfaces" }
             elem {
               name: "interface"
               key { key: "name" value: "Ethernet0" }
             }
             elem { name: "state" }
             elem { name: "oper-status" }
           }
           type: STATE)pb",
      &oper_status_req));
  gnmi::GetResponse oper_status_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1632102697699213032
             prefix { origin: "openconfig" }
             update {
               path {
                 elem { name: "interfaces" }
                 elem {
                   name: "interface"
                   key { key: "name" value: "Ethernet0" }
                 }
                 elem { name: "state" }
                 elem { name: "oper-status" }
               }
               val {
                 json_ietf_val: "{\"openconfig-interfaces:oper-status\":\"UP\"}"
               }
             }
           })pb",
      &oper_status_resp));
  gnmi::GetRequest physical_channels_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(prefix { origin: "openconfig" }
           path {
             elem { name: "interfaces" }
             elem {
               name: "interface"
               key { key: "name" value: "Ethernet0" }
             }
             elem { name: "state" }
             elem { name: "physical-channel" }
           }
           type: STATE)pb",
      &physical_channels_req));
  gnmi::GetResponse physical_channels_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1632102697805380043
             prefix { origin: "openconfig" }
             update {
               path {
                 elem { name: "interfaces" }
                 elem {
                   name: "interface"
                   key { key: "name" value: "Ethernet0" }
                 }
                 elem { name: "state" }
                 elem { name: "physical-channel" }
               }
               val {
                 json_ietf_val: "{\"openconfig-platform-transceiver:physical-channel\":[0,1,2,3,4,5,6,7]}"
               }
             }
           })pb",
      &physical_channels_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(oper_status_req), _))
      .Times(2)
      .WillRepeatedly(
          DoAll(SetArgPointee<2>(oper_status_resp), Return(grpc::Status::OK)));
  EXPECT_CALL(*mock_gnmi_stub_ptr,
              Get(_, EqualsProto(physical_channels_req), _))
      .WillOnce(DoAll(SetArgPointee<2>(physical_channels_resp),
                      Return(grpc::Status::OK)));
  EXPECT_THAT(
      pins_test::ValidateBreakoutState(
          mock_gnmi_stub_ptr.get(), expected_port_info, non_existing_port_list),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr("Unexpected port (Ethernet0) found after "
                         "application of breakout mode")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest, TestValidateBreakoutStateSuccess) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>
      expected_port_info;
  expected_port_info["Ethernet0"] =
      pins_test::PortBreakoutInfo{"[0,1,2,3,4,5,6,7]", pins_test::kStateUp};
  std::vector<std::string> non_existing_port_list{};
  gnmi::GetRequest oper_status_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(prefix { origin: "openconfig" }
           path {
             elem { name: "interfaces" }
             elem {
               name: "interface"
               key { key: "name" value: "Ethernet0" }
             }
             elem { name: "state" }
             elem { name: "oper-status" }
           }
           type: STATE)pb",
      &oper_status_req));
  gnmi::GetResponse oper_status_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1632102697699213032
             prefix { origin: "openconfig" }
             update {
               path {
                 elem { name: "interfaces" }
                 elem {
                   name: "interface"
                   key { key: "name" value: "Ethernet0" }
                 }
                 elem { name: "state" }
                 elem { name: "oper-status" }
               }
               val {
                 json_ietf_val: "{\"openconfig-interfaces:oper-status\":\"UP\"}"
               }
             }
           })pb",
      &oper_status_resp));
  gnmi::GetRequest physical_channels_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(prefix { origin: "openconfig" }
           path {
             elem { name: "interfaces" }
             elem {
               name: "interface"
               key { key: "name" value: "Ethernet0" }
             }
             elem { name: "state" }
             elem { name: "physical-channel" }
           }
           type: STATE)pb",
      &physical_channels_req));
  gnmi::GetResponse physical_channels_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1632102697805380043
             prefix { origin: "openconfig" }
             update {
               path {
                 elem { name: "interfaces" }
                 elem {
                   name: "interface"
                   key { key: "name" value: "Ethernet0" }
                 }
                 elem { name: "state" }
                 elem { name: "physical-channel" }
               }
               val {
                 json_ietf_val: "{\"openconfig-platform-transceiver:physical-channel\":[0,1,2,3,4,5,6,7]}"
               }
             }
           })pb",
      &physical_channels_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(oper_status_req), _))
      .WillOnce(
          DoAll(SetArgPointee<2>(oper_status_resp), Return(grpc::Status::OK)));
  EXPECT_CALL(*mock_gnmi_stub_ptr,
              Get(_, EqualsProto(physical_channels_req), _))
      .WillOnce(DoAll(SetArgPointee<2>(physical_channels_resp),
                      Return(grpc::Status::OK)));
  EXPECT_EQ(
      pins_test::ValidateBreakoutState(
          mock_gnmi_stub_ptr.get(), expected_port_info, non_existing_port_list),
      absl::OkStatus());
}

TEST_F(GNMIThinkitInterfaceUtilityTest, TestGetPortIndexSuccess) {
  const std::string platform_json_contents =
      R"pb({ "interfaces": { "Ethernet0": { "index": "1,1,1,1,1,1,1,1" } } }
      )pb";
  const std::string port = "Ethernet0";
  const std::string expected_port_index = "1";
  EXPECT_THAT(pins_test::GetPortIndex(platform_json_contents, port),
              expected_port_index);
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetPortIndexInterfacesNotFoundFailure) {
  const std::string platform_json_contents =
      R"pb({}
      )pb";
  const std::string port = "Ethernet0";
  const std::string expected_port_index = "";
  EXPECT_THAT(pins_test::GetPortIndex(platform_json_contents, port),
              StatusIs(absl::StatusCode::kInternal,
                       HasSubstr("Interfaces not found in platform.json")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetPortIndexInterfaceNotFoundFailure) {
  const std::string platform_json_contents =
      R"pb({ "interfaces": {} }
      )pb";
  const std::string port = "Ethernet0";
  const std::string expected_port_index = "";
  EXPECT_THAT(pins_test::GetPortIndex(platform_json_contents, port),
              StatusIs(absl::StatusCode::kInternal,
                       HasSubstr(absl::StrCat(
                           port, " entry not found in platform.json"))));
}

TEST_F(GNMIThinkitInterfaceUtilityTest, TestGetPortIndexIndexNotFoundFailure) {
  const std::string platform_json_contents =
      R"pb({ "interfaces": { "Ethernet0": {} } }
      )pb";
  const std::string port = "Ethernet0";
  const std::string expected_port_index = "";
  EXPECT_THAT(pins_test::GetPortIndex(platform_json_contents, port),
              StatusIs(absl::StatusCode::kInternal,
                       HasSubstr(absl::StrCat("Index not found for ", port,
                                              " in platform.json"))));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestConstructSupportedBreakoutModeSuccess) {
  std::string num_breakouts = " 1";
  std::string breakout_speed = "400G ";
  const std::string expected_breakout_mode = "1x400G";
  EXPECT_THAT(
      pins_test::ConstructSupportedBreakoutMode(num_breakouts, breakout_speed),
      expected_breakout_mode);
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestBreakoutResultsInSpeedChangeOnlySuccess) {
  EXPECT_THAT(pins_test::BreakoutResultsInSpeedChangeOnly("Ethernet0", "1x400G",
                                                          "1x100G"),
              true);
  EXPECT_THAT(pins_test::BreakoutResultsInSpeedChangeOnly(
                  "Ethernet0", "1x200G(4)+2x100G(4)", "1x100G(4)+2x40G(4)"),
              true);
  EXPECT_THAT(pins_test::BreakoutResultsInSpeedChangeOnly("Ethernet0", "1x400G",
                                                          "2x200G"),
              false);
  EXPECT_THAT(pins_test::BreakoutResultsInSpeedChangeOnly(
                  "Ethernet0", "1x200G(4)+2x40G(4)", "1x200G(4)+1x40G(4)"),
              false);
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestBreakoutResultsInSpeedChangeOnlyInvalidPortFailure) {
  EXPECT_THAT(pins_test::BreakoutResultsInSpeedChangeOnly("EthernetX", "1x400G",
                                                          "1x100G"),
              StatusIs(absl::StatusCode::kInternal,
                       HasSubstr("Failed to convert string (X) to integer")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest, TestIsCopperPortSuccessOpticPort) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  gnmi::GetRequest req;
  ASSERT_TRUE(
      google::protobuf::TextFormat::ParseFromString(get_xcvrd_req_str, &req));
  gnmi::GetResponse resp;
  ASSERT_TRUE(
      google::protobuf::TextFormat::ParseFromString(get_xcvrd_resp_str, &resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(req), _))
      .WillOnce(DoAll(SetArgPointee<2>(resp), Return(grpc::Status::OK)));
  gnmi::GetRequest cable_len_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(cable_len_req_str,
                                                            &cable_len_req));
  gnmi::GetResponse cable_len_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      cable_len_resp_optic_str, &cable_len_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(cable_len_req), _))
      .WillOnce(
          DoAll(SetArgPointee<2>(cable_len_resp), Return(grpc::Status::OK)));
  EXPECT_THAT(pins_test::IsCopperPort(mock_gnmi_stub_ptr.get(), "Ethernet0"),
              false);
}

TEST_F(GNMIThinkitInterfaceUtilityTest, TestIsCopperPortSuccessCopperPort) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  gnmi::GetRequest req;
  ASSERT_TRUE(
      google::protobuf::TextFormat::ParseFromString(get_xcvrd_req_str, &req));
  gnmi::GetResponse resp;
  ASSERT_TRUE(
      google::protobuf::TextFormat::ParseFromString(get_xcvrd_resp_str, &resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(req), _))
      .WillOnce(DoAll(SetArgPointee<2>(resp), Return(grpc::Status::OK)));
  gnmi::GetRequest cable_len_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(cable_len_req_str,
                                                            &cable_len_req));
  gnmi::GetResponse cable_len_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      cable_len_resp_copper_str, &cable_len_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(cable_len_req), _))
      .WillOnce(
          DoAll(SetArgPointee<2>(cable_len_resp), Return(grpc::Status::OK)));
  EXPECT_THAT(pins_test::IsCopperPort(mock_gnmi_stub_ptr.get(), "Ethernet0"),
              true);
}

TEST_F(GNMIThinkitInterfaceUtilityTest, TestIsCopperPortTransceiverGetFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  gnmi::GetRequest req;
  ASSERT_TRUE(
      google::protobuf::TextFormat::ParseFromString(get_xcvrd_req_str, &req));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(req), _))
      .WillOnce(Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  EXPECT_THAT(pins_test::IsCopperPort(mock_gnmi_stub_ptr.get(), "Ethernet0"),
              StatusIs(absl::StatusCode::kDeadlineExceeded,
                       HasSubstr("Failed to get GNMI state path value for "
                                 "port transceiver for port Ethernet0")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest, TestIsCopperPortCableLengthGetFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  gnmi::GetRequest req;
  ASSERT_TRUE(
      google::protobuf::TextFormat::ParseFromString(get_xcvrd_req_str, &req));
  gnmi::GetResponse resp;
  ASSERT_TRUE(
      google::protobuf::TextFormat::ParseFromString(get_xcvrd_resp_str, &resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(req), _))
      .WillOnce(DoAll(SetArgPointee<2>(resp), Return(grpc::Status::OK)));
  gnmi::GetRequest cable_len_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(cable_len_req_str,
                                                            &cable_len_req));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(cable_len_req), _))
      .WillOnce(Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  EXPECT_THAT(pins_test::IsCopperPort(mock_gnmi_stub_ptr.get(), "Ethernet0"),
              StatusIs(absl::StatusCode::kDeadlineExceeded,
                       HasSubstr("Failed to get GNMI state path value for "
                                 "cable-length for port Ethernet0")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestIsCopperPortFloatConversionFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  gnmi::GetRequest req;
  ASSERT_TRUE(
      google::protobuf::TextFormat::ParseFromString(get_xcvrd_req_str, &req));
  gnmi::GetResponse resp;
  ASSERT_TRUE(
      google::protobuf::TextFormat::ParseFromString(get_xcvrd_resp_str, &resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(req), _))
      .WillOnce(DoAll(SetArgPointee<2>(resp), Return(grpc::Status::OK)));
  gnmi::GetRequest cable_len_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(cable_len_req_str,
                                                            &cable_len_req));
  gnmi::GetResponse cable_len_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1631864194292383538
             prefix { origin: "openconfig" }
             update {
               path {
                 elem { name: "components" }
                 elem {
                   name: "component"
                   key { key: "name" value: "Ethernet0" }
                 }
                 elem { name: "transceiver" }
                 elem { name: "state" }
                 elem { name: "openconfig-platform-ext:cable-length" }
               }
               val {
                 json_ietf_val: "{\"openconfig-platform-ext:cable-length\":\"XYZ\"}"
               }
             }
           }
      )pb",
      &cable_len_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(cable_len_req), _))
      .WillOnce(
          DoAll(SetArgPointee<2>(cable_len_resp), Return(grpc::Status::OK)));
  EXPECT_THAT(pins_test::IsCopperPort(mock_gnmi_stub_ptr.get(), "Ethernet0"),
              StatusIs(absl::StatusCode::kInternal,
                       HasSubstr("Failed to convert string (XYZ) to float")));
}
}  // namespace pins_test
