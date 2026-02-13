// Copyright 2025 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include <cstdio>
#include <memory>
#include <string>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "gmock/gmock.h"
#include "google/protobuf/text_format.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "include/nlohmann/json.hpp"
#include "lib/gnmi/gnmi_helper.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "proto/gnmi/gnmi.pb.h"
#include "proto/gnmi/gnmi_mock.grpc.pb.h"
#include "tests/thinkit_gnmi_interface_util.h"
#include "tests/thinkit_util.h"
#include "thinkit/mock_ssh_client.h"
#include "thinkit/mock_switch.h"

namespace pins_test {
using gutil::EqualsProto;
using gutil::IsOkAndHolds;
using gutil::StatusIs;
using ::nlohmann::json;
using ::testing::_;
using ::testing::ContainerEq;
using ::testing::DoAll;
using ::testing::FieldsAre;
using ::testing::HasSubstr;
using ::testing::Return;
using ::testing::ReturnRefOfCopy;
using ::testing::SetArgPointee;

constexpr char get_xcvrd_req_str[] =
    R"pb(prefix { origin: "openconfig" target: "chassis" }
         path {
           elem { name: "interfaces" }
           elem {
             name: "interface"
             key { key: "name" value: "Ethernet1/1/1" }
           }
           elem { name: "state" }
           elem { name: "transceiver" }
         }
         type: STATE
         encoding: JSON_IETF)pb";

constexpr char get_xcvrd_resp_str[] =
    R"pb(notification {
           timestamp: 1631864194292383538
           prefix { origin: "openconfig" target: "chassis" }
           update {
             path {
               elem { name: "interfaces" }
               elem {
                 name: "interface"
                 key { key: "name" value: "Ethernet1/1/1" }
               }
               elem { name: "state" }
               elem { name: "transceiver" }
             }
             val {
               json_ietf_val: "{\"openconfig-platform-transceiver:transceiver\":\"Ethernet1/1/1\"}"
             }
           }
         }
    )pb";

constexpr char ethernet_pmd_req_str[] =
    R"pb(prefix { origin: "openconfig" target: "chassis" }
         path {
           elem { name: "components" }
           elem {
             name: "component"
             key { key: "name" value: "Ethernet1/1/1" }
           }
           elem { name: "transceiver" }
           elem { name: "state" }
           elem { name: "ethernet-pmd" }
         }
         type: STATE
         encoding: JSON_IETF)pb";

constexpr char ethernet_pmd_resp_copper_str[] =
    R"pb(notification {
           timestamp: 1631864194292383538
           prefix { origin: "openconfig" target: "chassis" }
           update {
             path {
               elem { name: "components" }
               elem {
                 name: "component"
                 key { key: "name" value: "Ethernet1/1/1" }
               }
               elem { name: "transceiver" }
               elem { name: "state" }
               elem { name: "ethernet-pmd" }
             }
             val {
               json_ietf_val: "{\"openconfig-platform-transceiver:ethernet-pmd\":\"google-pins-transceivers:ETH_2X400GBASE_CR4\"}"
             }
           }
         }
    )pb";

constexpr char ethernet_pmd_resp_optic_str[] =
    R"pb(notification {
           timestamp: 1631864194292383538
           prefix { origin: "openconfig" target: "chassis" }
           update {
             path {
               elem { name: "components" }
               elem {
                 name: "component"
                 key { key: "name" value: "Ethernet1/1/1" }
               }
               elem { name: "transceiver" }
               elem { name: "state" }
               elem { name: "ethernet-pmd" }
             }
             val {
               json_ietf_val: "{\"openconfig-platform-transceiver:ethernet-pmd\":\"google-pins-transceivers:ETH_2X400GBASE_CDGR4_PLUS\"}"
             }
           }
         }
    )pb";

constexpr char all_interfaces_req[] =
    R"pb(prefix { origin: "openconfig" target: "chassis" }
         path { elem { name: "interfaces" } }
         type: STATE
         encoding: JSON_IETF)pb";

constexpr char all_interfaces_resp[] =
    R"pb(notification {
           timestamp: 1631864194292383538
           prefix { origin: "openconfig" target: "chassis" }
           update {
             path { elem { name: "interfaces" } }
             val {
               json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet1/1/1\",\"state\":{\"oper-status\":\"UP\",\"openconfig-p4rt:id\":1,\"openconfig-platform-transceiver:transceiver\":\"Ethernet1\"}},{\"name\":\"Ethernet1/2/1\",\"state\":{\"oper-status\":\"UP\",\"openconfig-p4rt:id\":2,\"openconfig-platform-transceiver:transceiver\":\"Ethernet2\"}}]}}"
             }
           }
         }
    )pb";

constexpr char invalid_interfaces_resp[] =
    R"pb(notification {
           timestamp: 1631864194292383538
           prefix { origin: "openconfig" target: "chassis" }
           update {
             path { elem { name: "interfaces" } }
             val {
               json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet1/1/1\",\"state\":{\"oper-status\":\"UP\",\"openconfig-p4rt:id\":1,\"openconfig-platform-transceiver:transceiver\":\"Ethernet1\"}},{\"name\":\"Ethernet1/2/1\",\"state\":{\"oper-status\":\"UP\",\"openconfig-p4rt:id\":2,\"openconfig-platform-transceiver:transceiver\":\"EthernetABC\"}}]}}"
             }
           }
         }
    )pb";

constexpr char all_components_req[] =
    R"pb(prefix { origin: "openconfig" target: "chassis" }
         path { elem { name: "components" } }
         type: STATE
         encoding: JSON_IETF)pb";

constexpr char all_components_resp[] =
    R"pb(notification {
           timestamp: 1631864194292383538
           prefix { origin: "openconfig" target: "chassis" }
           update {
             path { elem { name: "components" } }
             val {
               json_ietf_val: "{\"openconfig-platform:components\":{\"component\":[{\"name\":\"Ethernet1\",\"state\":{\"empty\":false},\"openconfig-platform-transceiver:transceiver\":{\"state\":{\"ethernet-pmd\":\"ETH_2X400GBASE_CR4\"}}},{\"name\":\"Ethernet2\",\"state\":{\"empty\":false},\"openconfig-platform-transceiver:transceiver\":{\"state\":{\"ethernet-pmd\":\"ETH_2X400GBASE_CR4\"}}}]}}"
             }
           }
         }
    )pb";

constexpr char multi_form_factor_components_resp[] =
    R"pb(notification {
           timestamp: 1631864194292383538
           prefix { origin: "openconfig" target: "chassis" }
           update {
             path { elem { name: "components" } }
             val {
               json_ietf_val: "{\"openconfig-platform:components\":{\"component\":[{\"name\":\"Ethernet1\",\"state\":{\"empty\":false},\"openconfig-platform-transceiver:transceiver\":{\"state\":{\"ethernet-pmd\":\"ETH_2X400GBASE_CDGR4_PLUS\",\"form-factor\":\"OSFP\"}}},{\"name\":\"Ethernet2\",\"state\":{\"empty\":false},\"openconfig-platform-transceiver:transceiver\":{\"state\":{\"ethernet-pmd\":\"ETH_10GBASE_LR\",\"form-factor\":\"SFP_PLUS\"}}}]}}"
             }
           }
         }
    )pb";

constexpr char invalid_components_resp[] =
    R"pb(notification {
           timestamp: 1631864194292383538
           prefix { origin: "openconfig" target: "chassis" }
           update {
             path { elem { name: "components" } }
             val {
               json_ietf_val: "{\"openconfig-platform:components\":{\"component\":[{\"name\":\"Ethernet1\",\"state\":{\"empty\":false},\"openconfig-platform-transceiver:transceiver\":{\"state\":{\"ethernet-pmd\":\"ETH_2X400GBASE_CDGR4_PLUS\",\"form-factor\":\"OSFP\"}}},{\"name\":\"EthernetABC\",\"state\":{\"empty\":false},\"openconfig-platform-transceiver:transceiver\":{\"state\":{\"ethernet-pmd\":\"ETH_2X400GBASE_DR4\",\"form-factor\":\"OSFP\"}}}]}}"
             }
           }
         }
    )pb";

constexpr char all_sfpp_components_resp[] =
    R"pb(notification {
           timestamp: 1631864194292383538
           prefix { origin: "openconfig" target: "chassis" }
           update {
             path { elem { name: "components" } }
             val {
               json_ietf_val: "{\"openconfig-platform:components\":{\"component\":[{\"name\":\"Ethernet1\",\"state\":{\"empty\":false},\"openconfig-platform-transceiver:transceiver\":{\"state\":{\"ethernet-pmd\":\"ETH_10GBASE_LR\"}}},{\"name\":\"Ethernet2\",\"state\":{\"empty\":false},\"openconfig-platform-transceiver:transceiver\":{\"state\":{\"ethernet-pmd\":\"ETH_10GBASE_LR\"}}}]}}"
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
  absl::StatusOr<gnmi::GetRequest> currentBreakoutModeGetReq(
      const std::string port) {
    gnmi::GetRequest req;
    if (!google::protobuf::TextFormat::ParseFromString(
            absl::Substitute(
                R"pb(prefix { origin: "openconfig" target: "chassis" }
                     path {
                       elem { name: "components" }
                       elem {
                         name: "component"
                         key { key: "name" value: "$0" }
                       }
                       elem { name: "port" }
                       elem { name: "breakout-mode" }
                       elem { name: "groups" }
                     }
                     type: STATE
                     encoding: JSON_IETF)pb",
                port),
            &req)) {
      return gutil::InternalErrorBuilder().LogError()
             << "Failed to parse request into proto.";
    }
    return req;
  }

  absl::StatusOr<gnmi::GetResponse> currentBreakoutModeGetUnchannelizedResp(
      const std::string port) {
    gnmi::GetResponse resp;
    if (!google::protobuf::TextFormat::ParseFromString(
            absl::Substitute(
                R"pb(notification {
                       timestamp: 1631864194292383538
                       prefix { origin: "openconfig" target: "chassis" }
                       update {
                         path {
                           elem { name: "openconfig-platform:components" }
                           elem {
                             name: "component"
                             key: { key: "name" value: "$0" }
                           }
                           elem { name: "port" }
                           elem { name: "breakout-mode" }
                           elem { name: "groups" }
                         }
                         val {
                           json_ietf_val: "{\"openconfig-platform-port:groups\":{\"group\":[{\"config\":{\"breakout-speed\":\"openconfig-if-ethernet:SPEED_400GB\",\"index\":0,\"num-breakouts\":1,\"num-physical-channels\":8},\"index\":0,\"state\":{\"breakout-speed\":\"openconfig-if-ethernet:SPEED_400GB\",\"index\":0,\"num-breakouts\":1,\"num-physical-channels\":8}}]}}"
                         }
                       }
                     })pb",
                port),
            &resp)) {
      return gutil::InternalErrorBuilder().LogError()
             << "Failed to parse response into proto.";
    }
    return resp;
  }

  absl::StatusOr<gnmi::GetResponse> currentBreakoutModeGetChannelizedResp(
      const std::string port) {
    gnmi::GetResponse resp;
    if (!google::protobuf::TextFormat::ParseFromString(
            absl::Substitute(
                R"pb(notification {
                       timestamp: 1631864194292383538
                       prefix { origin: "openconfig" target: "chassis" }
                       update {
                         path {
                           elem { name: "openconfig-platform:components" }
                           elem {
                             name: "component"
                             key: { key: "name" value: "$0" }
                           }
                           elem { name: "port" }
                           elem { name: "breakout-mode" }
                           elem { name: "groups" }
                         }
                         val {
                           json_ietf_val: "{\"openconfig-platform-port:groups\":{\"group\":[{\"config\":{\"breakout-speed\":\"openconfig-if-ethernet:SPEED_200GB\",\"index\":0,\"num-breakouts\":2,\"num-physical-channels\":4},\"index\":0,\"state\":{\"breakout-speed\":\"openconfig-if-ethernet:SPEED_200GB\",\"index\":0,\"num-breakouts\":2,\"num-physical-channels\":4}}]}}"
                         }
                       }
                     })pb",
                port),
            &resp)) {
      return gutil::InternalErrorBuilder().LogError()
             << "Failed to parse response into proto.";
    }
    return resp;
  }

  absl::StatusOr<gnmi::GetResponse> currentBreakoutModeGetMixedResp(
      const std::string port) {
    gnmi::GetResponse resp;
    if (!google::protobuf::TextFormat::ParseFromString(
            absl::Substitute(
                R"pb(notification {
                       timestamp: 1631864194292383538
                       prefix { origin: "openconfig" target: "chassis" }
                       update {
                         path {
                           elem { name: "openconfig-platform:components" }
                           elem {
                             name: "component"
                             key: { key: "name" value: "$0" }
                           }
                           elem { name: "port" }
                           elem { name: "breakout-mode" }
                           elem { name: "groups" }
                         }
                         val {
                           json_ietf_val: "{\"openconfig-platform-port:groups\":{\"group\":[{\"config\":{\"breakout-speed\":\"openconfig-if-ethernet:SPEED_400GB\",\"index\":0,\"num-breakouts\":1,\"num-physical-channels\":4},\"index\":0,\"state\":{\"breakout-speed\":\"openconfig-if-ethernet:SPEED_400GB\",\"index\":0,\"num-breakouts\":1,\"num-physical-channels\":4}}, {\"config\":{\"breakout-speed\":\"openconfig-if-ethernet:SPEED_200GB\",\"index\":1,\"num-breakouts\":2,\"num-physical-channels\":4},\"index\":1,\"state\":{\"breakout-speed\":\"openconfig-if-ethernet:SPEED_200GB\",\"index\":1,\"num-breakouts\":2,\"num-physical-channels\":4}}]}}"
                         }
                       }
                     })pb",
                port),
            &resp)) {
      return gutil::InternalErrorBuilder().LogError()
             << "Failed to parse response into proto.";
    }
    return resp;
  }

  absl::StatusOr<gnmi::GetRequest> hardwarePortGetReq(absl::string_view port) {
    gnmi::GetRequest req;
    if (!google::protobuf::TextFormat::ParseFromString(
            absl::Substitute(
                R"pb(prefix { origin: "openconfig" target: "chassis" }
                     path {
                       elem { name: "interfaces" }
                       elem {
                         name: "interface"
                         key { key: "name" value: "$0" }
                       }
                       elem { name: "state" }
                       elem { name: "hardware-port" }
                     }
                     type: STATE
                     encoding: JSON_IETF
                )pb",
                port),
            &req)) {
      return gutil::InternalErrorBuilder().LogError()
             << "Failed to parse request into proto.";
    }
    return req;
  }

  absl::StatusOr<gnmi::GetResponse> hardwarePortGetResp(
      absl::string_view port, absl::string_view port_number) {
    gnmi::GetResponse resp;
    if (!google::protobuf::TextFormat::ParseFromString(
            absl::Substitute(
                R"pb(notification {
                       timestamp: 1631864194292383538
                       prefix { origin: "openconfig" target: "chassis" }
                       update {
                         path {
                           elem { name: "openconfig-interfaces:interfaces" }
                           elem {
                             name: "interface"
                             key: { key: "name" value: "$0" }
                           }
                           elem { name: "state" }
                           elem { name: "hardware-port" }
                         }
                         val {
                           json_ietf_val: "{\"openconfig-platform-port:hardware-port\":\"1/$1\"}"
                         }
                       }
                     })pb",
                port, port_number),
            &resp)) {
      return gutil::InternalErrorBuilder().LogError()
             << "Failed to parse response into proto.";
    }
    return resp;
  }

  absl::StatusOr<gnmi::GetRequest> portIDGetReq(absl::string_view port) {
    gnmi::GetRequest req;
    if (!google::protobuf::TextFormat::ParseFromString(
            absl::Substitute(
                R"pb(prefix { origin: "openconfig" target: "chassis" }
                     path {
                       elem { name: "interfaces" }
                       elem {
                         name: "interface"
                         key { key: "name" value: "$0" }
                       }
                       elem { name: "state" }
                       elem { name: "id" }
                     }
                     type: STATE
                     encoding: JSON_IETF)pb",
                port),
            &req)) {
      return gutil::InternalErrorBuilder().LogError()
             << "Failed to parse request into proto.";
    }
    return req;
  }

  absl::StatusOr<gnmi::GetResponse> portIDGetResp(absl::string_view port,
                                                  absl::string_view id) {
    gnmi::GetResponse resp;
    if (!google::protobuf::TextFormat::ParseFromString(
            absl::Substitute(
                R"pb(notification {
                       timestamp: 1631864194292383538
                       prefix { origin: "openconfig" target: "chassis" }
                       update {
                         path {
                           elem { name: "openconfig-interfaces:interfaces" }
                           elem {
                             name: "interface"
                             key: { key: "name" value: "$0" }
                           }
                           elem { name: "state" }
                           elem { name: "id" }
                         }
                         val {
                           json_ietf_val: "{\"openconfig-interfaces:id\":$1}"
                         }
                       }
                     })pb",
                port, id),
            &resp)) {
      return gutil::InternalErrorBuilder().LogError()
             << "Failed to parse response into proto.";
    }
    return resp;
  }

  thinkit::MockSwitch mock_switch_;
  gnmi::MockgNMIStub mock_gnmi_stub_;
};

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetSupportedBreakoutModesForPortAnySuccess) {
  const absl::string_view port = "Ethernet1/1/1";
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
  const absl::string_view port = "Ethernet1/1/1";
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
  const absl::string_view port = "Ethernet1/1/1";
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
  const absl::string_view port = "Ethernet1/1/1";
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
  r.port_name = "Ethernet1/1/1";
  r.curr_breakout_mode = "1x400G";
  r.supported_breakout_mode = "2x200G";
  expected_port_info["Ethernet1/1/1"] = r;
  r.port_name = "Ethernet1/2/1";
  r.curr_breakout_mode = "2x200G";
  r.supported_breakout_mode = "1x400G";
  expected_port_info["Ethernet1/2/1"] = r;
  const std::string platform_json_contents =
      R"pb({
             "interfaces": {
               "Ethernet1/1/1": {
                 "breakout_modes": "1x400G, 2x200G[100G,40G]"
               },
               "Ethernet1/2/1": {
                 "breakout_modes": "1x400G, 2x200G[100G,40G]"
               },
               "Ethernet1/2/5": { "breakout_modes": "1x200G[100G,40G]" }
             }
           }
      )pb";
  gnmi::GetRequest interfaces_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_req,
                                                            &interfaces_req));
  gnmi::GetResponse interfaces_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_resp,
                                                            &interfaces_resp));
  gnmi::GetRequest components_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_req,
                                                            &components_req));
  gnmi::GetResponse components_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_resp,
                                                            &components_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(interfaces_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(interfaces_resp), Return(grpc::Status::OK)));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(components_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(components_resp), Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_req_1,
                       currentBreakoutModeGetReq("1/1"));
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_resp_1,
                       currentBreakoutModeGetUnchannelizedResp("1/1"));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_req_1,
                       hardwarePortGetReq("Ethernet1/1/1"));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_resp_1,
                       hardwarePortGetResp("Ethernet1/1/1", "1"));
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_req_2,
                       currentBreakoutModeGetReq("1/2"));
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_resp_2,
                       currentBreakoutModeGetChannelizedResp("1/2"));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_req_2,
                       hardwarePortGetReq("Ethernet1/2/1"));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_resp_2,
                       hardwarePortGetResp("Ethernet1/2/1", "2"));
  ON_CALL(*mock_gnmi_stub_ptr,
          Get(_, EqualsProto(current_breakout_mode_get_req_1), _))
      .WillByDefault(DoAll(SetArgPointee<2>(current_breakout_mode_get_resp_1),
                           Return(grpc::Status::OK)));
  ON_CALL(*mock_gnmi_stub_ptr,
          Get(_, EqualsProto(current_breakout_mode_get_req_2), _))
      .WillByDefault(DoAll(SetArgPointee<2>(current_breakout_mode_get_resp_2),
                           Return(grpc::Status::OK)));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(hardware_port_get_req_1), _))
      .WillByDefault(DoAll(SetArgPointee<2>(hardware_port_get_resp_1),
                           Return(grpc::Status::OK)));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(hardware_port_get_req_2), _))
      .WillByDefault(DoAll(SetArgPointee<2>(hardware_port_get_resp_2),
                           Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(auto random_port_info,
                       pins_test::GetRandomPortWithSupportedBreakoutModes(
                           *mock_gnmi_stub_ptr, platform_json_contents));
  EXPECT_TRUE(expected_port_info.contains(random_port_info.port_name));
  EXPECT_EQ(random_port_info.port_name,
            expected_port_info[random_port_info.port_name].port_name);
  EXPECT_EQ(random_port_info.curr_breakout_mode,
            expected_port_info[random_port_info.port_name].curr_breakout_mode);
  EXPECT_EQ(
      random_port_info.supported_breakout_mode,
      expected_port_info[random_port_info.port_name].supported_breakout_mode);
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetRandomPortWithSupportedBreakoutModesChannelizedSuccess) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  absl::flat_hash_map<std::string, pins_test::RandomPortBreakoutInfo>
      expected_port_info;
  pins_test::RandomPortBreakoutInfo r;
  r.port_name = "Ethernet1/1/1";
  r.curr_breakout_mode = "1x400G";
  r.supported_breakout_mode = "2x200G";
  expected_port_info["Ethernet1/1/1"] = r;
  const std::string platform_json_contents =
      R"pb({
             "interfaces": {
               "Ethernet1/1/1": {
                 "breakout_modes": "1x400G, 2x200G[100G,40G]"
               },
               "Ethernet1/2/1": { "breakout_modes": "1x400G" },
               "Ethernet1/3/1": { "breakout_modes": "1x400G" }
             }
           }
      )pb";
  gnmi::GetRequest interfaces_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_req,
                                                            &interfaces_req));
  gnmi::GetResponse interfaces_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_resp,
                                                            &interfaces_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(interfaces_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(interfaces_resp), Return(grpc::Status::OK)));
  gnmi::GetRequest components_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_req,
                                                            &components_req));
  gnmi::GetResponse components_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_resp,
                                                            &components_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(components_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(components_resp), Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_req_1,
                       currentBreakoutModeGetReq("1/1"));
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_resp_1,
                       currentBreakoutModeGetUnchannelizedResp("1/1"));
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_req_2,
                       currentBreakoutModeGetReq("1/2"));
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_resp_2,
                       currentBreakoutModeGetUnchannelizedResp("1/2"));
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_req_3,
                       currentBreakoutModeGetReq("1/3"));
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_resp_3,
                       currentBreakoutModeGetUnchannelizedResp("1/3"));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_req_1,
                       hardwarePortGetReq("Ethernet1/1/1"));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_resp_1,
                       hardwarePortGetResp("Ethernet1/1/1", "1"));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_req_2,
                       hardwarePortGetReq("Ethernet1/2/1"));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_resp_2,
                       hardwarePortGetResp("Ethernet1/2/1", "2"));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_req_3,
                       hardwarePortGetReq("Ethernet1/3/1"));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_resp_3,
                       hardwarePortGetResp("Ethernet1/3/1", "3"));
  ON_CALL(*mock_gnmi_stub_ptr,
          Get(_, EqualsProto(current_breakout_mode_get_req_1), _))
      .WillByDefault(DoAll(SetArgPointee<2>(current_breakout_mode_get_resp_1),
                           Return(grpc::Status::OK)));
  ON_CALL(*mock_gnmi_stub_ptr,
          Get(_, EqualsProto(current_breakout_mode_get_req_2), _))
      .WillByDefault(DoAll(SetArgPointee<2>(current_breakout_mode_get_resp_2),
                           Return(grpc::Status::OK)));
  ON_CALL(*mock_gnmi_stub_ptr,
          Get(_, EqualsProto(current_breakout_mode_get_req_3), _))
      .WillByDefault(DoAll(SetArgPointee<2>(current_breakout_mode_get_resp_3),
                           Return(grpc::Status::OK)));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(hardware_port_get_req_1), _))
      .WillByDefault(DoAll(SetArgPointee<2>(hardware_port_get_resp_1),
                           Return(grpc::Status::OK)));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(hardware_port_get_req_2), _))
      .WillByDefault(DoAll(SetArgPointee<2>(hardware_port_get_resp_2),
                           Return(grpc::Status::OK)));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(hardware_port_get_req_3), _))
      .WillByDefault(DoAll(SetArgPointee<2>(hardware_port_get_resp_3),
                           Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(auto random_port_info,
                       pins_test::GetRandomPortWithSupportedBreakoutModes(
                           *mock_gnmi_stub_ptr, platform_json_contents,
                           pins_test::BreakoutType::kChannelized));
  EXPECT_TRUE(expected_port_info.contains(random_port_info.port_name));
  EXPECT_EQ(random_port_info.port_name,
            expected_port_info[random_port_info.port_name].port_name);
  EXPECT_EQ(random_port_info.curr_breakout_mode,
            expected_port_info[random_port_info.port_name].curr_breakout_mode);
  EXPECT_EQ(
      random_port_info.supported_breakout_mode,
      expected_port_info[random_port_info.port_name].supported_breakout_mode);
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetRandomPortWithSupportedBreakoutModesWithAllowListSuccess) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  absl::flat_hash_map<std::string, pins_test::RandomPortBreakoutInfo>
      expected_port_info;
  pins_test::RandomPortBreakoutInfo r;
  r.port_name = "Ethernet1/1/1";
  r.curr_breakout_mode = "1x400G";
  r.supported_breakout_mode = "2x200G";
  expected_port_info["Ethernet1/1/1"] = r;
  const std::string platform_json_contents =
      R"pb({
             "interfaces": {
               "Ethernet1/1/1": {
                 "breakout_modes": "1x400G, 2x200G[100G,40G]"
               },
               "Ethernet1/2/1": { "breakout_modes": "1x400G" },
               "Ethernet1/3/1": { "breakout_modes": "1x400G" }
             }
           }
      )pb";
  gnmi::GetRequest interfaces_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_req,
                                                            &interfaces_req));
  gnmi::GetResponse interfaces_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_resp,
                                                            &interfaces_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(interfaces_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(interfaces_resp), Return(grpc::Status::OK)));
  gnmi::GetRequest components_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_req,
                                                            &components_req));
  gnmi::GetResponse components_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_resp,
                                                            &components_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(components_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(components_resp), Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_req_1,
                       currentBreakoutModeGetReq("1/1"));
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_resp_1,
                       currentBreakoutModeGetUnchannelizedResp("1/1"));
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_req_2,
                       currentBreakoutModeGetReq("1/2"));
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_resp_2,
                       currentBreakoutModeGetUnchannelizedResp("1/2"));
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_req_3,
                       currentBreakoutModeGetReq("1/3"));
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_resp_3,
                       currentBreakoutModeGetUnchannelizedResp("1/3"));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_req_1,
                       hardwarePortGetReq("Ethernet1/1/1"));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_resp_1,
                       hardwarePortGetResp("Ethernet1/1/1", "1"));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_req_2,
                       hardwarePortGetReq("Ethernet1/2/1"));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_resp_2,
                       hardwarePortGetResp("Ethernet1/2/1", "2"));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_req_3,
                       hardwarePortGetReq("Ethernet1/3/1"));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_resp_3,
                       hardwarePortGetResp("Ethernet1/3/1", "3"));
  ON_CALL(*mock_gnmi_stub_ptr,
          Get(_, EqualsProto(current_breakout_mode_get_req_1), _))
      .WillByDefault(DoAll(SetArgPointee<2>(current_breakout_mode_get_resp_1),
                           Return(grpc::Status::OK)));
  ON_CALL(*mock_gnmi_stub_ptr,
          Get(_, EqualsProto(current_breakout_mode_get_req_2), _))
      .WillByDefault(DoAll(SetArgPointee<2>(current_breakout_mode_get_resp_2),
                           Return(grpc::Status::OK)));
  ON_CALL(*mock_gnmi_stub_ptr,
          Get(_, EqualsProto(current_breakout_mode_get_req_3), _))
      .WillByDefault(DoAll(SetArgPointee<2>(current_breakout_mode_get_resp_3),
                           Return(grpc::Status::OK)));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(hardware_port_get_req_1), _))
      .WillByDefault(DoAll(SetArgPointee<2>(hardware_port_get_resp_1),
                           Return(grpc::Status::OK)));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(hardware_port_get_req_2), _))
      .WillByDefault(DoAll(SetArgPointee<2>(hardware_port_get_resp_2),
                           Return(grpc::Status::OK)));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(hardware_port_get_req_3), _))
      .WillByDefault(DoAll(SetArgPointee<2>(hardware_port_get_resp_3),
                           Return(grpc::Status::OK)));
  std::vector<absl::string_view> allow_list = {"Ethernet1/1/1"};
  ASSERT_OK_AND_ASSIGN(auto random_port_info,
                       pins_test::GetRandomPortWithSupportedBreakoutModes(
                           *mock_gnmi_stub_ptr, platform_json_contents,
                           pins_test::BreakoutType::kAny,
                           pins_test::BreakoutType::kAny, allow_list));
  EXPECT_TRUE(expected_port_info.contains(random_port_info.port_name));
  EXPECT_EQ(random_port_info.port_name,
            expected_port_info[random_port_info.port_name].port_name);
  EXPECT_EQ(random_port_info.curr_breakout_mode,
            expected_port_info[random_port_info.port_name].curr_breakout_mode);
  EXPECT_EQ(
      random_port_info.supported_breakout_mode,
      expected_port_info[random_port_info.port_name].supported_breakout_mode);
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetRandomPortWithSupportedBreakoutModesOperStatusMapGetFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  gnmi::GetRequest req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(prefix { origin: "openconfig" target: "chassis" }
           path { elem { name: "interfaces" } }
           type: STATE
           encoding: JSON_IETF)pb",
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
       TestGetRandomPortWithSupportedBreakoutModesNoPortsFoundFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  gnmi::GetRequest interfaces_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_req,
                                                            &interfaces_req));
  gnmi::GetResponse interfaces_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1631864194292383538
             prefix { origin: "openconfig" target: "chassis" }
             update {
               path { elem { name: "interfaces" } }
               val {
                 json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[]}}"
               }
             }
           }
      )pb",
      &interfaces_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(interfaces_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(interfaces_resp), Return(grpc::Status::OK)));
  gnmi::GetRequest components_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_req,
                                                            &components_req));
  gnmi::GetResponse components_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_resp,
                                                            &components_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(components_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(components_resp), Return(grpc::Status::OK)));
  EXPECT_THAT(pins_test::GetRandomPortWithSupportedBreakoutModes(
                  *mock_gnmi_stub_ptr, ""),
              StatusIs(absl::StatusCode::kInternal,
                       HasSubstr("No ports found on switch")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetRandomPortWithSupportedBreakoutModesIntfNameToPortIdGetFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  gnmi::GetRequest req;
  ASSERT_TRUE(
      google::protobuf::TextFormat::ParseFromString(all_interfaces_req, &req));
  gnmi::GetResponse resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1631864194292383538
             prefix { origin: "openconfig" target: "chassis" }
             update {
               path { elem { name: "interfaces" } }
               val {
                 json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet1/1/1\",\"state\":{\"oper-status\":\"UP\",\"openconfig-p4rt:id\": 1}},{\"name\":\"Ethernet1/2/1\",\"state\":{\"oper-status\":\"UP\"}},{\"name\":\"Ethernet1/3/1\",\"state\":{\"oper-status\":\"UP\",\"openconfig-p4rt:id\": 2}}]}}"
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

TEST_F(
    GNMIThinkitInterfaceUtilityTest,
    TestGetRandomPortWithSupportedBreakoutModesNoIntfsInPlatformJsonFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string platform_json_contents =
      R"pb({}
      )pb";
  gnmi::GetRequest interfaces_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_req,
                                                            &interfaces_req));
  gnmi::GetResponse interfaces_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_resp,
                                                            &interfaces_resp));
  gnmi::GetRequest components_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_req,
                                                            &components_req));
  gnmi::GetResponse components_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_resp,
                                                            &components_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(interfaces_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(interfaces_resp), Return(grpc::Status::OK)));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(components_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(components_resp), Return(grpc::Status::OK)));
  EXPECT_THAT(pins_test::GetRandomPortWithSupportedBreakoutModes(
                  *mock_gnmi_stub_ptr, platform_json_contents),
              StatusIs(absl::StatusCode::kInternal,
                       HasSubstr("Interfaces not found in platform.json")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetRandomPortWithSupportedBreakoutModesNoPortsWithP4rtIDFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string platform_json_contents =
      R"pb({
             "interfaces": {
               "Ethernet1/1/1": {
                 "breakout_modes": "1x400G, 2x200G[100G,40G]"
               },
               "Ethernet1/2/1": {
                 "breakout_modes": "1x400G, 2x200G[100G,40G]"
               },
               "Ethernet1/2/5": { "breakout_modes": "1x200G[100G,40G]" }
             }
           }
      )pb";
  gnmi::GetRequest req;
  ASSERT_TRUE(
      google::protobuf::TextFormat::ParseFromString(all_interfaces_req, &req));
  gnmi::GetResponse resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1631864194292383538
             prefix { origin: "openconfig" target: "chassis" }
             update {
               path { elem { name: "interfaces" } }
               val {
                 json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet1/1/1\",\"state\":{\"oper-status\":\"UP\",\"openconfig-platform-transceiver:transceiver\":\"Ethernet1\"}}, {\"name\":\"Ethernet1/2/1\",\"state\":{\"oper-status\":\"UP\",\"openconfig-platform-transceiver:transceiver\":\"Ethernet2\"}}]}}"
               }
             }
           }
      )pb",
      &resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(req), _))
      .WillByDefault(DoAll(SetArgPointee<2>(resp), Return(grpc::Status::OK)));
  gnmi::GetRequest components_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_req,
                                                            &components_req));
  gnmi::GetResponse components_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_resp,
                                                            &components_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(components_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(components_resp), Return(grpc::Status::OK)));
  EXPECT_THAT(
      pins_test::GetRandomPortWithSupportedBreakoutModes(
          *mock_gnmi_stub_ptr, platform_json_contents),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr(
                   "No random interface with supported breakout modes found")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetRandomPortWithSupportedBreakoutModesNoEthernetPortsFoundFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string platform_json_contents =
      R"pb({
             "interfaces": {
               "Ethernet1/1/1": {
                 "breakout_modes": "1x400G, 2x200G[100G,40G]"
               },
               "Ethernet1/2/1": {
                 "breakout_modes": "1x400G, 2x200G[100G,40G]"
               },
               "Ethernet1/2/5": { "breakout_modes": "1x200G[100G,40G]" }
             }
           }
      )pb";
  gnmi::GetRequest req;
  ASSERT_TRUE(
      google::protobuf::TextFormat::ParseFromString(all_interfaces_req, &req));
  gnmi::GetResponse resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1631864194292383538
             prefix { origin: "openconfig" target: "chassis" }
             update {
               path { elem { name: "interfaces" } }
               val {
                 json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Loopback0\",\"state\":{\"oper-status\":\"UP\",\"openconfig-p4rt:id\": 1}},{\"name\":\"Loopback1\",\"state\":{\"oper-status\":\"UP\",\"openconfig-p4rt:id\": 2}}]}}"
               }
             }
           }
      )pb",
      &resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(req), _))
      .WillByDefault(DoAll(SetArgPointee<2>(resp), Return(grpc::Status::OK)));
  gnmi::GetRequest components_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_req,
                                                            &components_req));
  gnmi::GetResponse components_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_resp,
                                                            &components_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(components_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(components_resp), Return(grpc::Status::OK)));
  EXPECT_THAT(
      pins_test::GetRandomPortWithSupportedBreakoutModes(
          *mock_gnmi_stub_ptr, platform_json_contents),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr(
                   "No random interface with supported breakout modes found")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetRandomPortWithSupportedBreakoutModesIntConversionFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string platform_json_contents =
      R"pb({
             "interfaces": {
               "Ethernet1/1/1": {
                 "breakout_modes": "1x400G, 2x200G[100G,40G]"
               },
               "Ethernet1/2/1": {
                 "breakout_modes": "1x400G, 2x200G[100G,40G]"
               },
               "Ethernet1/2/5": { "breakout_modes": "1x200G[100G,40G]" }
             }
           }
      )pb";
  gnmi::GetRequest interfaces_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_req,
                                                            &interfaces_req));
  gnmi::GetResponse interfaces_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1631864194292383538
             prefix { origin: "openconfig" target: "chassis" }
             update {
               path { elem { name: "interfaces" } }
               val {
                 json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet1/1/X\",\"state\":{\"oper-status\":\"UP\",\"openconfig-p4rt:id\": 1,\"openconfig-platform-transceiver:transceiver\":\"Ethernet1\"}},{\"name\":\"Ethernet1/2/X\",\"state\":{\"oper-status\":\"UP\",\"openconfig-p4rt:id\":2,\"openconfig-platform-transceiver:transceiver\":\"Ethernet2\"}}]}}"
               }
             }
           }
      )pb",
      &interfaces_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(interfaces_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(interfaces_resp), Return(grpc::Status::OK)));
  gnmi::GetRequest components_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_req,
                                                            &components_req));
  gnmi::GetResponse components_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_resp,
                                                            &components_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(components_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(components_resp), Return(grpc::Status::OK)));
  EXPECT_THAT(pins_test::GetRandomPortWithSupportedBreakoutModes(
                  *mock_gnmi_stub_ptr, platform_json_contents),
              StatusIs(absl::StatusCode::kInternal,
                       HasSubstr("Failed to convert string (X) to integer")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetRandomPortWithSupportedBreakoutModesNoParentPortsFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string platform_json_contents =
      R"pb({
             "interfaces": {
               "Ethernet1/1/1": {
                 "breakout_modes": "1x400G, 2x200G[100G,40G]"
               },
               "Ethernet1/2/1": {
                 "breakout_modes": "1x400G, 2x200G[100G,40G]"
               },
               "Ethernet1/2/5": { "breakout_modes": "1x200G[100G,40G]" }
             }
           }
      )pb";
  gnmi::GetRequest req;
  ASSERT_TRUE(
      google::protobuf::TextFormat::ParseFromString(all_interfaces_req, &req));
  gnmi::GetResponse resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1631864194292383538
             prefix { origin: "openconfig" target: "chassis" }
             update {
               path { elem { name: "interfaces" } }
               val {
                 json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet1/2/5\",\"state\":{\"oper-status\":\"UP\",\"openconfig-p4rt:id\":2,\"openconfig-platform-transceiver:transceiver\":\"Ethernet1\"}}]}}"
               }
             }
           }
      )pb",
      &resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(req), _))
      .WillByDefault(DoAll(SetArgPointee<2>(resp), Return(grpc::Status::OK)));
  gnmi::GetRequest components_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_req,
                                                            &components_req));
  gnmi::GetResponse components_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_resp,
                                                            &components_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(components_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(components_resp), Return(grpc::Status::OK)));
  EXPECT_THAT(
      pins_test::GetRandomPortWithSupportedBreakoutModes(
          *mock_gnmi_stub_ptr, platform_json_contents),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr(
                   "No random interface with supported breakout modes found")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetRandomPortWithSupportedBreakoutModesNoOperUpPortsFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string platform_json_contents =
      R"pb({
             "interfaces": {
               "Ethernet1/1/1": {
                 "breakout_modes": "1x400G, 2x200G[100G,40G]"
               },
               "Ethernet1/2/1": {
                 "breakout_modes": "1x400G, 2x200G[100G,40G]"
               },
               "Ethernet1/2/5": { "breakout_modes": "1x200G[100G,40G]" }
             }
           }
      )pb";
  gnmi::GetRequest interfaces_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_req,
                                                            &interfaces_req));
  gnmi::GetResponse resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1631864194292383538
             prefix { origin: "openconfig" target: "chassis" }
             update {
               path { elem { name: "interfaces" } }
               val {
                 json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet1/1/1\",\"state\":{\"oper-status\":\"DOWN\",\"openconfig-p4rt:id\":1,\"openconfig-platform-transceiver:transceiver\":\"Ethernet1\"}}, {\"name\":\"Ethernet1/2/1\",\"state\":{\"oper-status\":\"DOWN\",\"openconfig-p4rt:id\":2,\"openconfig-platform-transceiver:transceiver\":\"Ethernet2\"}}]}}"
               }
             }
           }
      )pb",
      &resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(interfaces_req), _))
      .WillByDefault(DoAll(SetArgPointee<2>(resp), Return(grpc::Status::OK)));
  gnmi::GetRequest components_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_req,
                                                            &components_req));
  gnmi::GetResponse components_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_resp,
                                                            &components_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(components_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(components_resp), Return(grpc::Status::OK)));
  EXPECT_THAT(
      pins_test::GetRandomPortWithSupportedBreakoutModes(
          *mock_gnmi_stub_ptr, platform_json_contents),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr(
                   "No random interface with supported breakout modes found")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetRandomPortWithSupportedBreakoutModesInterfaceNotFoundFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string platform_json_contents =
      R"pb({ "interfaces": {} }
      )pb";
  gnmi::GetRequest interfaces_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_req,
                                                            &interfaces_req));
  gnmi::GetResponse resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1631864194292383538
             prefix { origin: "openconfig" target: "chassis" }
             update {
               path { elem { name: "interfaces" } }
               val {
                 json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet1/1/1\",\"state\":{\"oper-status\":\"UP\",\"openconfig-p4rt:id\":1,\"openconfig-platform-transceiver:transceiver\":\"Ethernet2\"}}]}}"
               }
             }
           }
      )pb",
      &resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(interfaces_req), _))
      .WillByDefault(DoAll(SetArgPointee<2>(resp), Return(grpc::Status::OK)));
  gnmi::GetRequest components_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_req,
                                                            &components_req));
  gnmi::GetResponse components_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_resp,
                                                            &components_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(components_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(components_resp), Return(grpc::Status::OK)));
  EXPECT_THAT(
      pins_test::GetRandomPortWithSupportedBreakoutModes(
          *mock_gnmi_stub_ptr, platform_json_contents),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr("Ethernet1/1/1 entry not found in platform.json")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetRandomPortWithSupportedBreakoutModesCurrentModeNotFoundFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string platform_json_contents =
      R"pb({
             "interfaces": {
               "Ethernet1/1/1": { "breakout_modes": "1x400G, 2x200G[100G,40G]" }
             }
           }
      )pb";
  gnmi::GetRequest interfaces_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_req,
                                                            &interfaces_req));
  gnmi::GetResponse interfaces_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1631864194292383538
             prefix { origin: "openconfig" target: "chassis" }
             update {
               path { elem { name: "interfaces" } }
               val {
                 json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet1/1/1\",\"state\":{\"oper-status\":\"UP\",\"openconfig-p4rt:id\":1,\"openconfig-platform-transceiver:transceiver\":\"Ethernet1\"}}]}}"
               }
             }
           }
      )pb",
      &interfaces_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(interfaces_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(interfaces_resp), Return(grpc::Status::OK)));
  gnmi::GetRequest components_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_req,
                                                            &components_req));
  gnmi::GetResponse components_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_resp,
                                                            &components_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(components_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(components_resp), Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_req,
                       currentBreakoutModeGetReq("1/1"));
  ON_CALL(*mock_gnmi_stub_ptr,
          Get(_, EqualsProto(current_breakout_mode_get_req), _))
      .WillByDefault(
          Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_req_1,
                       hardwarePortGetReq("Ethernet1/1/1"));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_resp_1,
                       hardwarePortGetResp("Ethernet1/1/1", "1"));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(hardware_port_get_req_1), _))
      .WillByDefault(DoAll(SetArgPointee<2>(hardware_port_get_resp_1),
                           Return(grpc::Status::OK)));
  EXPECT_THAT(
      pins_test::GetRandomPortWithSupportedBreakoutModes(
          *mock_gnmi_stub_ptr, platform_json_contents),
      StatusIs(absl::StatusCode::kDeadlineExceeded,
               HasSubstr("Failed to get GNMI state path value for component "
                         "breakout paths for port Ethernet1/1/1")));
}

TEST_F(
    GNMIThinkitInterfaceUtilityTest,
    TestGetRandomPortWithSupportedBreakoutModesSupportedModesNotFoundFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string platform_json_contents =
      R"pb({ "interfaces": { "Ethernet1/1/1": {} } }
      )pb";
  gnmi::GetRequest interfaces_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_req,
                                                            &interfaces_req));
  gnmi::GetResponse interfaces_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1631864194292383538
             prefix { origin: "openconfig" target: "chassis" }
             update {
               path { elem { name: "interfaces" } }
               val {
                 json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet1/1/1\",\"state\":{\"oper-status\":\"UP\",\"openconfig-p4rt:id\":1,\"openconfig-platform-transceiver:transceiver\":\"Ethernet1\"}}]}}"
               }
             }
           }
      )pb",
      &interfaces_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(interfaces_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(interfaces_resp), Return(grpc::Status::OK)));
  gnmi::GetRequest components_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_req,
                                                            &components_req));
  gnmi::GetResponse components_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_resp,
                                                            &components_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(components_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(components_resp), Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_req,
                       currentBreakoutModeGetReq("1/1"));
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_resp,
                       currentBreakoutModeGetUnchannelizedResp("1/1"));
  ON_CALL(*mock_gnmi_stub_ptr,
          Get(_, EqualsProto(current_breakout_mode_get_req), _))
      .WillByDefault(DoAll(SetArgPointee<2>(current_breakout_mode_get_resp),
                           Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_req_1,
                       hardwarePortGetReq("Ethernet1/1/1"));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_resp_1,
                       hardwarePortGetResp("Ethernet1/1/1", "1"));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(hardware_port_get_req_1), _))
      .WillByDefault(DoAll(SetArgPointee<2>(hardware_port_get_resp_1),
                           Return(grpc::Status::OK)));
  EXPECT_THAT(
      pins_test::GetRandomPortWithSupportedBreakoutModes(
          *mock_gnmi_stub_ptr, platform_json_contents),
      StatusIs(
          absl::StatusCode::kInternal,
          HasSubstr(
              "Breakout modes not found for Ethernet1/1/1 in platform.json")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetRandomPortWithSupportedBreakoutModesNoSupportedNewBreakoutType) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string platform_json_contents =
      R"pb({
             "interfaces": {
               "Ethernet1/1/1": { "breakout_modes": "1x400G" },
               "Ethernet1/2/1": { "breakout_modes": "1x400G" }
             }
           }
      )pb";
  gnmi::GetRequest interfaces_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_req,
                                                            &interfaces_req));
  gnmi::GetResponse interfaces_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_resp,
                                                            &interfaces_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(interfaces_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(interfaces_resp), Return(grpc::Status::OK)));
  gnmi::GetRequest components_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_req,
                                                            &components_req));
  gnmi::GetResponse components_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_resp,
                                                            &components_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(components_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(components_resp), Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_req_1,
                       currentBreakoutModeGetReq("1/1"));
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_resp_1,
                       currentBreakoutModeGetUnchannelizedResp("1/1"));
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_req_2,
                       currentBreakoutModeGetReq("1/2"));
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_resp_2,
                       currentBreakoutModeGetUnchannelizedResp("1/2"));
  ON_CALL(*mock_gnmi_stub_ptr,
          Get(_, EqualsProto(current_breakout_mode_get_req_1), _))
      .WillByDefault(DoAll(SetArgPointee<2>(current_breakout_mode_get_resp_1),
                           Return(grpc::Status::OK)));
  ON_CALL(*mock_gnmi_stub_ptr,
          Get(_, EqualsProto(current_breakout_mode_get_req_2), _))
      .WillByDefault(DoAll(SetArgPointee<2>(current_breakout_mode_get_resp_2),
                           Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_req_1,
                       hardwarePortGetReq("Ethernet1/1/1"));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_resp_1,
                       hardwarePortGetResp("Ethernet1/1/1", "1"));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(hardware_port_get_req_1), _))
      .WillByDefault(DoAll(SetArgPointee<2>(hardware_port_get_resp_1),
                           Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_req_2,
                       hardwarePortGetReq("Ethernet1/2/1"));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_resp_2,
                       hardwarePortGetResp("Ethernet1/2/1", "2"));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(hardware_port_get_req_2), _))
      .WillByDefault(DoAll(SetArgPointee<2>(hardware_port_get_resp_2),
                           Return(grpc::Status::OK)));
  EXPECT_THAT(
      pins_test::GetRandomPortWithSupportedBreakoutModes(
          *mock_gnmi_stub_ptr, platform_json_contents,
          pins_test::BreakoutType::kChannelized),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr(
                   "No random interface with supported breakout modes found")));
}

TEST_F(
    GNMIThinkitInterfaceUtilityTest,
    TestGetRandomPortWithSupportedBreakoutModesNoSupportedCurrentBreakoutType) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string platform_json_contents =
      R"pb({
             "interfaces": {
               "Ethernet1/1/1": {
                 "breakout_modes": "1x400G, 2x200G[100G,40G]"
               },
               "Ethernet1/2/1": { "breakout_modes": "1x400G, 2x200G[100G,40G]" }
             }
           }
      )pb";
  gnmi::GetRequest interfaces_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_req,
                                                            &interfaces_req));
  gnmi::GetResponse interfaces_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_resp,
                                                            &interfaces_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(interfaces_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(interfaces_resp), Return(grpc::Status::OK)));
  gnmi::GetRequest components_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_req,
                                                            &components_req));
  gnmi::GetResponse components_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_resp,
                                                            &components_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(components_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(components_resp), Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_req_1,
                       currentBreakoutModeGetReq("1/1"));
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_resp_1,
                       currentBreakoutModeGetUnchannelizedResp("1/1"));
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_req_2,
                       currentBreakoutModeGetReq("1/2"));
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_resp_2,
                       currentBreakoutModeGetUnchannelizedResp("1/2"));
  ON_CALL(*mock_gnmi_stub_ptr,
          Get(_, EqualsProto(current_breakout_mode_get_req_1), _))
      .WillByDefault(DoAll(SetArgPointee<2>(current_breakout_mode_get_resp_1),
                           Return(grpc::Status::OK)));
  ON_CALL(*mock_gnmi_stub_ptr,
          Get(_, EqualsProto(current_breakout_mode_get_req_2), _))
      .WillByDefault(DoAll(SetArgPointee<2>(current_breakout_mode_get_resp_2),
                           Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_req_1,
                       hardwarePortGetReq("Ethernet1/1/1"));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_resp_1,
                       hardwarePortGetResp("Ethernet1/1/1", "1"));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(hardware_port_get_req_1), _))
      .WillByDefault(DoAll(SetArgPointee<2>(hardware_port_get_resp_1),
                           Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_req_2,
                       hardwarePortGetReq("Ethernet1/2/1"));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_resp_2,
                       hardwarePortGetResp("Ethernet1/2/1", "2"));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(hardware_port_get_req_2), _))
      .WillByDefault(DoAll(SetArgPointee<2>(hardware_port_get_resp_2),
                           Return(grpc::Status::OK)));
  EXPECT_THAT(
      pins_test::GetRandomPortWithSupportedBreakoutModes(
          *mock_gnmi_stub_ptr, platform_json_contents,
          pins_test::BreakoutType::kAny, pins_test::BreakoutType::kChannelized),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr(
                   "No random interface with supported breakout modes found")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetRandomPortWithSupportedBreakoutModesPortNotFoundInGnmiIntfMap) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string platform_json_contents =
      R"pb({
             "interfaces": {
               "Ethernet1/1/1": {
                 "breakout_modes": "1x400G, 2x200G[100G,40G]"
               },
               "Ethernet1/2/1": {
                 "breakout_modes": "1x400G, 2x200G[100G,40G]"
               },
               "Ethernet1/2/5": { "breakout_modes": "1x200G[100G,40G]" },
               "Ethernet1/3/1": { "breakout_modes": "1x400G, 2x200G[100G,40G]" }
             }
           }
      )pb";
  gnmi::GetRequest interfaces_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_req,
                                                            &interfaces_req));
  gnmi::GetResponse interfaces_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_resp,
                                                            &interfaces_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(interfaces_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(interfaces_resp), Return(grpc::Status::OK)));
  gnmi::GetRequest components_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_req,
                                                            &components_req));
  gnmi::GetResponse components_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_resp,
                                                            &components_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(components_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(components_resp), Return(grpc::Status::OK)));
  std::vector<absl::string_view> allow_list = {"Ethernet1/3/1"};
  EXPECT_THAT(
      pins_test::GetRandomPortWithSupportedBreakoutModes(
          *mock_gnmi_stub_ptr, platform_json_contents,
          pins_test::BreakoutType::kAny, pins_test::BreakoutType::kAny,
          allow_list),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr(
                   "No random interface with supported breakout modes found")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetRandomPortWithSupportedBreakoutModesPortNoNonSfppPortsFound) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string platform_json_contents =
      R"pb({
             "interfaces": {
               "Ethernet1/1/1": {
                 "breakout_modes": "1x400G, 2x200G[100G,40G]"
               },
               "Ethernet1/2/1": {
                 "breakout_modes": "1x400G, 2x200G[100G,40G]"
               },
               "Ethernet1/2/5": { "breakout_modes": "1x200G[100G,40G]" },
               "Ethernet1/3/1": { "breakout_modes": "1x400G, 2x200G[100G,40G]" }
             }
           }
      )pb";
  gnmi::GetRequest interfaces_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_req,
                                                            &interfaces_req));
  gnmi::GetResponse interfaces_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_resp,
                                                            &interfaces_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(interfaces_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(interfaces_resp), Return(grpc::Status::OK)));
  gnmi::GetRequest components_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_req,
                                                            &components_req));
  gnmi::GetResponse components_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      all_sfpp_components_resp, &components_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(components_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(components_resp), Return(grpc::Status::OK)));
  EXPECT_THAT(
      pins_test::GetRandomPortWithSupportedBreakoutModes(
          *mock_gnmi_stub_ptr, platform_json_contents,
          pins_test::BreakoutType::kAny, pins_test::BreakoutType::kAny),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr(
                   "No random interface with supported breakout modes found")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetPortSetWithOsfpOpticsFailedInGettingComponents) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  gnmi::GetRequest components_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_req,
                                                            &components_req));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(components_req), _))
      .WillOnce(Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  EXPECT_THAT(pins_test::GetPortSetWithOsfpOptics(*mock_gnmi_stub_ptr),
              StatusIs(absl::StatusCode::kDeadlineExceeded));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetPortSetWithOsfpOpticsInvalidXcvrName) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  gnmi::GetRequest components_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_req,
                                                            &components_req));
  gnmi::GetResponse components_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      invalid_components_resp, &components_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(components_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(components_resp), Return(grpc::Status::OK)));
  EXPECT_THAT(pins_test::GetPortSetWithOsfpOptics(*mock_gnmi_stub_ptr),
              StatusIs(absl::StatusCode::kInternal,
                       HasSubstr("Failed to parse transceiver number in")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest, TestGetPortSetWithOsfpOpticsSuccess) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  gnmi::GetRequest components_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_req,
                                                            &components_req));
  gnmi::GetResponse components_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      multi_form_factor_components_resp, &components_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(components_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(components_resp), Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(
      auto port_set, pins_test::GetPortSetWithOsfpOptics(*mock_gnmi_stub_ptr));
  absl::flat_hash_set<int> expected_port_set_set = {1};
  ASSERT_EQ(port_set, expected_port_set_set);
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetXcvrToInterfacesMapGivenPmdTypeInterfacesGetFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  gnmi::GetRequest interfaces_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_req,
                                                            &interfaces_req));
  gnmi::GetResponse interfaces_resp;
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(interfaces_req), _))
      .WillOnce(Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  EXPECT_THAT(pins_test::GetXcvrToInterfacesMapGivenPmdType(
                  *mock_gnmi_stub_ptr, "ETH_2X400GBASE_DR4"),
              StatusIs(absl::StatusCode::kDeadlineExceeded));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetXcvrToInterfacesMapGivenPmdTypeComponentsGetFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  gnmi::GetRequest interfaces_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_req,
                                                            &interfaces_req));
  gnmi::GetResponse interfaces_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_resp,
                                                            &interfaces_resp));
  gnmi::GetRequest components_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_req,
                                                            &components_req));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(interfaces_req), _))
      .WillOnce(
          DoAll(SetArgPointee<2>(interfaces_resp), Return(grpc::Status::OK)));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(components_req), _))
      .WillOnce(Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  EXPECT_THAT(pins_test::GetXcvrToInterfacesMapGivenPmdType(
                  *mock_gnmi_stub_ptr, "ETH_2X400GBASE_DR4"),
              StatusIs(absl::StatusCode::kDeadlineExceeded));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetXcvrToInterfacesMapGivenPmdTypeXcvrNotFoundFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  gnmi::GetRequest interfaces_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_req,
                                                            &interfaces_req));
  gnmi::GetResponse interfaces_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_resp,
                                                            &interfaces_resp));
  gnmi::GetRequest components_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_req,
                                                            &components_req));
  gnmi::GetResponse components_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1631864194292383538
             prefix { origin: "openconfig" target: "chassis" }
             update {
               path { elem { name: "components" } }
               val {
                 json_ietf_val: "{\"openconfig-platform:components\":{\"component\":[{\"name\":\"Ethernet2\",\"state\":{\"empty\":false},\"openconfig-platform-transceiver:transceiver\":{\"state\":{\"ethernet-pmd\":\"ETH_10GBASE_LR\"}}}]}}"
               }
             }
           }
      )pb",
      &components_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(interfaces_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(interfaces_resp), Return(grpc::Status::OK)));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(components_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(components_resp), Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(auto xcvr_to_interfaces_map,
                       pins_test::GetXcvrToInterfacesMapGivenPmdType(
                           *mock_gnmi_stub_ptr, "ETH_2X400GBASE_DR4"));
  EXPECT_TRUE(xcvr_to_interfaces_map.empty());
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetXcvrToInterfacesMapGivenPmdTypeInvalidXcvrName) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  gnmi::GetRequest interfaces_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_req,
                                                            &interfaces_req));
  gnmi::GetResponse interfaces_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      invalid_interfaces_resp, &interfaces_resp));
  gnmi::GetRequest components_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_req,
                                                            &components_req));
  gnmi::GetResponse components_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      invalid_components_resp, &components_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(interfaces_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(interfaces_resp), Return(grpc::Status::OK)));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(components_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(components_resp), Return(grpc::Status::OK)));
  EXPECT_THAT(pins_test::GetXcvrToInterfacesMapGivenPmdType(
                  *mock_gnmi_stub_ptr, "ETH_2X400GBASE_DR4"),
              StatusIs(absl::StatusCode::kInternal,
                       HasSubstr("Failed to parse transceiver number in")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetXcvrToInterfacesMapGivenPmdTypeSuccess) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  gnmi::GetRequest interfaces_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_req,
                                                            &interfaces_req));
  gnmi::GetResponse interfaces_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_resp,
                                                            &interfaces_resp));
  gnmi::GetRequest components_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_req,
                                                            &components_req));
  gnmi::GetResponse components_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_resp,
                                                            &components_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(interfaces_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(interfaces_resp), Return(grpc::Status::OK)));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(components_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(components_resp), Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(auto xcvr_to_interfaces_map,
                       pins_test::GetXcvrToInterfacesMapGivenPmdType(
                           *mock_gnmi_stub_ptr, "ETH_2X400GBASE_CR4"));
  absl::flat_hash_map<int, std::vector<std::string>>
      expected_xcvr_to_interfaces_map = {{1, {"Ethernet1/1/1"}},
                                         {2, {"Ethernet1/2/1"}}};
  ASSERT_EQ(xcvr_to_interfaces_map, expected_xcvr_to_interfaces_map);
}

TEST_F(GNMIThinkitInterfaceUtilityTest, TestIsSfpPlusPortTrueSuccess) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  gnmi::GetRequest interfaces_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_req,
                                                            &interfaces_req));
  gnmi::GetResponse interfaces_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_resp,
                                                            &interfaces_resp));
  gnmi::GetRequest components_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_req,
                                                            &components_req));
  gnmi::GetResponse components_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      all_sfpp_components_resp, &components_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(interfaces_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(interfaces_resp), Return(grpc::Status::OK)));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(components_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(components_resp), Return(grpc::Status::OK)));
  EXPECT_THAT(pins_test::IsSfpPlusPort(*mock_gnmi_stub_ptr, "Ethernet1/1/1"),
              true);
}

TEST_F(GNMIThinkitInterfaceUtilityTest, TestIsSfpPlusPortFalseSuccess) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  gnmi::GetRequest interfaces_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_req,
                                                            &interfaces_req));
  gnmi::GetResponse interfaces_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_resp,
                                                            &interfaces_resp));
  gnmi::GetRequest components_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_req,
                                                            &components_req));
  gnmi::GetResponse components_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_resp,
                                                            &components_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(interfaces_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(interfaces_resp), Return(grpc::Status::OK)));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(components_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(components_resp), Return(grpc::Status::OK)));
  EXPECT_THAT(pins_test::IsSfpPlusPort(*mock_gnmi_stub_ptr, "Ethernet1/1/1"),
              false);
}

TEST_F(GNMIThinkitInterfaceUtilityTest, TestIsSfpPlusPortInterfacesGetFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  gnmi::GetRequest interfaces_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_req,
                                                            &interfaces_req));
  gnmi::GetResponse interfaces_resp;
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(interfaces_req), _))
      .WillOnce(Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  EXPECT_THAT(pins_test::IsSfpPlusPort(*mock_gnmi_stub_ptr, "Ethernet1/1/1"),
              StatusIs(absl::StatusCode::kDeadlineExceeded));
}

TEST_F(GNMIThinkitInterfaceUtilityTest, TestIsSfpPlusPortComponentsGetFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  gnmi::GetRequest interfaces_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_req,
                                                            &interfaces_req));
  gnmi::GetResponse interfaces_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_resp,
                                                            &interfaces_resp));
  gnmi::GetRequest components_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_req,
                                                            &components_req));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(interfaces_req), _))
      .WillOnce(
          DoAll(SetArgPointee<2>(interfaces_resp), Return(grpc::Status::OK)));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(components_req), _))
      .WillOnce(Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  EXPECT_THAT(pins_test::IsSfpPlusPort(*mock_gnmi_stub_ptr, "Ethernet1/1/1"),
              StatusIs(absl::StatusCode::kDeadlineExceeded));
}

TEST_F(GNMIThinkitInterfaceUtilityTest, TestIsSfpPlusPortIntfNotFoundFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  gnmi::GetRequest interfaces_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_req,
                                                            &interfaces_req));
  gnmi::GetResponse interfaces_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1631864194292383538
             prefix { origin: "openconfig" target: "chassis" }
             update {
               path { elem { name: "interfaces" } }
               val {
                 json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet1/2/1\",\"state\":{\"oper-status\":\"UP\",\"openconfig-p4rt:id\":2,\"openconfig-platform-transceiver:transceiver\":\"Ethernet2\"}},{\"name\":\"Ethernet1/3/1\",\"state\":{\"oper-status\":\"UP\",\"openconfig-p4rt:id\":3,\"openconfig-platform-transceiver:transceiver\":\"Ethernet3\"}}]}}"
               }
             }
           }
      )pb",
      &interfaces_resp));
  gnmi::GetRequest components_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_req,
                                                            &components_req));
  gnmi::GetResponse components_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_resp,
                                                            &components_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(interfaces_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(interfaces_resp), Return(grpc::Status::OK)));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(components_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(components_resp), Return(grpc::Status::OK)));
  EXPECT_THAT(pins_test::IsSfpPlusPort(*mock_gnmi_stub_ptr, "Ethernet1/1/1"),
              StatusIs(absl::StatusCode::kInternal,
                       HasSubstr("Interface Ethernet1/1/1 not found in "
                                 "interfaces to transceiver map")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest, TestIsSfpPlusPortXcvrNotFoundFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  gnmi::GetRequest interfaces_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_req,
                                                            &interfaces_req));
  gnmi::GetResponse interfaces_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_resp,
                                                            &interfaces_resp));
  gnmi::GetRequest components_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_components_req,
                                                            &components_req));
  gnmi::GetResponse components_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1631864194292383538
             prefix { origin: "openconfig" }
             update {
               path { elem { name: "components" } }
               val {
                 json_ietf_val: "{\"openconfig-platform:components\":{\"component\":[{\"name\":\"Ethernet2\",\"state\":{\"empty\":false},\"openconfig-platform-transceiver:transceiver\":{\"state\":{\"ethernet-pmd\":\"ETH_10GBASE_LR\"}}}]}}"
               }
             }
           }
      )pb",
      &components_resp));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(interfaces_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(interfaces_resp), Return(grpc::Status::OK)));
  ON_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(components_req), _))
      .WillByDefault(
          DoAll(SetArgPointee<2>(components_resp), Return(grpc::Status::OK)));
  EXPECT_THAT(
      pins_test::IsSfpPlusPort(*mock_gnmi_stub_ptr, "Ethernet1/1/1"),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr("Transceiver not found for interface Ethernet1/1/1")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetExpectedPortInfoForBreakoutModeUnchannelizedBreakoutModeSuccess) {
  const std::string port = "Ethernet1/1/1";
  absl::string_view breakout_mode = "1x400G";

  ASSERT_OK_AND_ASSIGN(
      auto breakout_info,
      pins_test::GetExpectedPortInfoForBreakoutMode(port, breakout_mode));
  EXPECT_EQ(breakout_info["Ethernet1/1/1"].physical_channels,
            "[0,1,2,3,4,5,6,7]");
  EXPECT_EQ(breakout_info["Ethernet1/1/1"].breakout_speed, "400G");
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetExpectedPortInfoForBreakoutModeChannelizedBreakoutModeSuccess) {
  const std::string port = "Ethernet1/1/1";
  absl::string_view breakout_mode = "2x200G";

  ASSERT_OK_AND_ASSIGN(
      auto breakout_info,
      pins_test::GetExpectedPortInfoForBreakoutMode(port, breakout_mode));
  EXPECT_EQ(breakout_info["Ethernet1/1/1"].physical_channels, "[0,1,2,3]");
  EXPECT_EQ(breakout_info["Ethernet1/1/5"].physical_channels, "[4,5,6,7]");
  EXPECT_EQ(breakout_info["Ethernet1/1/1"].breakout_speed, "200G");
  EXPECT_EQ(breakout_info["Ethernet1/1/5"].breakout_speed, "200G");
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetExpectedPortInfoForBreakoutModeMixedBreakoutModeSuccess) {
  const std::string port = "Ethernet1/1/1";
  absl::string_view breakout_mode = "1x200G(4)+2x100G(4)";

  ASSERT_OK_AND_ASSIGN(
      auto breakout_info,
      pins_test::GetExpectedPortInfoForBreakoutMode(port, breakout_mode));
  EXPECT_EQ(breakout_info["Ethernet1/1/1"].physical_channels, "[0,1,2,3]");
  EXPECT_EQ(breakout_info["Ethernet1/1/5"].physical_channels, "[4,5]");
  EXPECT_EQ(breakout_info["Ethernet1/1/7"].physical_channels, "[6,7]");
  EXPECT_EQ(breakout_info["Ethernet1/1/1"].breakout_speed, "200G");
  EXPECT_EQ(breakout_info["Ethernet1/1/5"].breakout_speed, "100G");
  EXPECT_EQ(breakout_info["Ethernet1/1/7"].breakout_speed, "100G");
}

TEST_F(
    GNMIThinkitInterfaceUtilityTest,
    TestGetExpectedPortInfoForBreakoutModeAlternatedMixedBreakoutModeSuccess) {
  const std::string port = "Ethernet1/1/1";
  absl::string_view breakout_mode = "2x100G(4)+1x200G(4)";
  ASSERT_OK_AND_ASSIGN(
      auto breakout_info,
      pins_test::GetExpectedPortInfoForBreakoutMode(port, breakout_mode));
  EXPECT_EQ(breakout_info["Ethernet1/1/1"].physical_channels, "[0,1]");
  EXPECT_EQ(breakout_info["Ethernet1/1/3"].physical_channels, "[2,3]");
  EXPECT_EQ(breakout_info["Ethernet1/1/5"].physical_channels, "[4,5,6,7]");
  EXPECT_EQ(breakout_info["Ethernet1/1/1"].breakout_speed, "100G");
  EXPECT_EQ(breakout_info["Ethernet1/1/3"].breakout_speed, "100G");
  EXPECT_EQ(breakout_info["Ethernet1/1/5"].breakout_speed, "200G");
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetExpectedPortInfoForBreakoutModeWithQuotesSuccess) {
  const std::string port = "Ethernet1/1/1";
  absl::string_view breakout_mode = "\"1x400G\"";
  ASSERT_OK_AND_ASSIGN(
      auto breakout_info,
      pins_test::GetExpectedPortInfoForBreakoutMode(port, breakout_mode));
  EXPECT_EQ(breakout_info["Ethernet1/1/1"].physical_channels,
            "[0,1,2,3,4,5,6,7]");
  EXPECT_EQ(breakout_info["Ethernet1/1/1"].breakout_speed, "400G");
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetExpectedPortInfoForBreakoutModeEmptyBreakoutModeFailure) {
  const std::string port = "Ethernet1/1/1";
  absl::string_view breakout_mode = "";

  EXPECT_THAT(
      pins_test::GetExpectedPortInfoForBreakoutMode(port, breakout_mode),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr("Found empty breakout mode")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetExpectedPortInfoForBreakoutModePortNumberIntConversionFailure) {
  const std::string port = "Ethernet1/1/X";
  absl::string_view breakout_mode = "1x400G";

  EXPECT_THAT(
      pins_test::GetExpectedPortInfoForBreakoutMode(port, breakout_mode),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr("Failed to convert string (X) to integer")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetExpectedPortInfoForBreakoutModeInvalidModeFailure) {
  const std::string port = "Ethernet1/1/1";
  absl::string_view breakout_mode = "1";

  EXPECT_THAT(
      pins_test::GetExpectedPortInfoForBreakoutMode(port, breakout_mode),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr("Invalid breakout mode found: 1")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetExpectedPortInfoForBreakoutModeNonParentPortFailure) {
  const std::string port = "Ethernet1/2/5";
  absl::string_view breakout_mode = "1x400G";

  EXPECT_THAT(
      pins_test::GetExpectedPortInfoForBreakoutMode(port, breakout_mode),
      StatusIs(
          absl::StatusCode::kInternal,
          HasSubstr("Requested port (Ethernet1/2/5) is not a parent port")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetExpectedPortInfoForBreakoutModeNumBreakoutsIntConversionFailure) {
  const std::string port = "Ethernet1/1/1";
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
  const std::string port = "Ethernet1/1/1";
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
  const std::string port = "Ethernet1/1/1";
  const std::string breakout_mode = "1x400G";
  gnmi::GetRequest interfaces_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_req,
                                                            &interfaces_req));
  gnmi::GetResponse interfaces_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_resp,
                                                            &interfaces_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(interfaces_req), _))
      .WillOnce(
          DoAll(SetArgPointee<2>(interfaces_resp), Return(grpc::Status::OK)));
  gnmi::GetRequest physical_channels_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(prefix { origin: "openconfig" target: "chassis" }
           path {
             elem { name: "interfaces" }
             elem {
               name: "interface"
               key { key: "name" value: "Ethernet1/1/1" }
             }
             elem { name: "state" }
             elem { name: "physical-channel" }
           }
           type: STATE
           encoding: JSON_IETF)pb",
      &physical_channels_req));
  gnmi::GetResponse physical_channels_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1632102697805380043
             prefix { origin: "openconfig" target: "chassis" }
             update {
               path {
                 elem { name: "interfaces" }
                 elem {
                   name: "interface"
                   key { key: "name" value: "Ethernet1/1/1" }
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
      R"pb(prefix { origin: "openconfig" target: "chassis" }
           path {
             elem { name: "interfaces" }
             elem {
               name: "interface"
               key { key: "name" value: "Ethernet1/1/1" }
             }
             elem { name: "state" }
             elem { name: "oper-status" }
           }
           type: STATE
           encoding: JSON_IETF)pb",
      &oper_status_req));
  gnmi::GetResponse oper_status_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1632102697699213032
             prefix { origin: "openconfig" target: "chassis" }
             update {
               path {
                 elem { name: "interfaces" }
                 elem {
                   name: "interface"
                   key { key: "name" value: "Ethernet1/1/1" }
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
  ASSERT_OK_AND_ASSIGN(auto breakout_state_info,
                       pins_test::GetBreakoutStateInfoForPort(
                           mock_gnmi_stub_ptr.get(), port, breakout_mode));
  EXPECT_EQ(breakout_state_info["Ethernet1/1/1"].physical_channels,
            "[0,1,2,3,4,5,6,7]");
  EXPECT_EQ(breakout_state_info["Ethernet1/1/1"].oper_status, "\"UP\"");
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetBreakoutStateInfoForPortExpectedBreakoutInfoFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string port = "Ethernet1/1/1";
  const std::string breakout_mode = "";
  gnmi::GetRequest interfaces_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_req,
                                                            &interfaces_req));
  gnmi::GetResponse interfaces_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_resp,
                                                            &interfaces_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(interfaces_req), _))
      .WillOnce(
          DoAll(SetArgPointee<2>(interfaces_resp), Return(grpc::Status::OK)));
  EXPECT_THAT(pins_test::GetBreakoutStateInfoForPort(mock_gnmi_stub_ptr.get(),
                                                     port, breakout_mode),
              StatusIs(absl::StatusCode::kInternal,
                       HasSubstr(("Found empty breakout mode"))));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetBreakoutStateInfoForPortPhysicalChannelsGetNoPhysicalChannels) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string port = "Ethernet1/3/1";
  const std::string breakout_mode = "1x200G+2x100G";
  gnmi::GetRequest interfaces_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_req,
                                                            &interfaces_req));
  gnmi::GetResponse interfaces_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_resp,
                                                            &interfaces_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(interfaces_req), _))
      .WillOnce(
          DoAll(SetArgPointee<2>(interfaces_resp), Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(auto breakout_state_info,
                       pins_test::GetBreakoutStateInfoForPort(
                           mock_gnmi_stub_ptr.get(), port, breakout_mode));
  EXPECT_EQ(breakout_state_info[port].physical_channels, "");
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetBreakoutStateInfoForPortOperStatusGetNoOperStatus) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string port = "Ethernet1/3/1";
  const std::string breakout_mode = "1x400G";
  gnmi::GetRequest interfaces_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_req,
                                                            &interfaces_req));
  gnmi::GetResponse interfaces_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(all_interfaces_resp,
                                                            &interfaces_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(interfaces_req), _))
      .WillOnce(
          DoAll(SetArgPointee<2>(interfaces_resp), Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(auto breakout_state_info,
                       pins_test::GetBreakoutStateInfoForPort(
                           mock_gnmi_stub_ptr.get(), port, breakout_mode));
  EXPECT_EQ(breakout_state_info[port].oper_status, "");
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetBreakoutModeConfigFromStringUnchannelizedBreakoutModeSuccess) {
  const std::string port_index = "1";
  const std::string intf_name = "Ethernet1/1/1";
  const std::string breakout_mode = "1x400G";
  gnmi::SetRequest req, expected_breakout_config;
  const std::string expected_breakout_config_str =
      R"pb(
    prefix { origin: "openconfig" target: "chassis" }
    replace {
      path {}
      val {
        json_ietf_val: "{\n             \"openconfig-interfaces:interfaces\": { \"interface\": [ {\n             \"config\": {\n               \"enabled\": true,\n               \"loopback-mode\": \"NONE\",\n               \"mtu\": 9216,\n               \"name\": \"Ethernet1/1/1\",\n               \"type\": \"iana-if-type:ethernetCsmacd\",\n               \"openconfig-p4rt:id\": 1\n             },\n             \"name\": \"Ethernet1/1/1\",\n             \"openconfig-if-ethernet:ethernet\": {\n               \"config\": { \"port-speed\": \"openconfig-if-ethernet:SPEED_400GB\" }\n             },\n             \"subinterfaces\": {\n               \"subinterface\":\n               [ {\n                 \"config\": { \"index\": 0 },\n                 \"index\": 0,\n                 \"openconfig-if-ip:ipv6\": {\n                   \"unnumbered\": { \"config\": { \"enabled\": true } }\n                 }\n               }]\n             }\n           }\n       ] },\n             \"openconfig-platform:components\": {\n               \"component\":\n               [ {\n                 \"name\": \"1/1\",\n                 \"config\": { \"name\": \"1/1\" },\n                 \"port\": {\n                   \"config\": { \"port-id\": 1 },\n                   \"breakout-mode\": { \"groups\": { \"group\": [ {\n             \"config\": {\n               \"breakout-speed\": \"openconfig-if-ethernet:SPEED_400GB\",\n               \"index\": 0,\n               \"num-breakouts\": 1,\n               \"num-physical-channels\": 8\n             },\n             \"index\": 0\n           } ] } }\n                 }\n               }]\n             }\n           }"
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
  gnmi::GetRequest ethernet_pmd_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      ethernet_pmd_req_str, &ethernet_pmd_req));
  gnmi::GetResponse ethernet_pmd_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      ethernet_pmd_resp_optic_str, &ethernet_pmd_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(ethernet_pmd_req), _))
      .WillOnce(
          DoAll(SetArgPointee<2>(ethernet_pmd_resp), Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(auto id_req, portIDGetReq("Ethernet1/1/1"));
  ASSERT_OK_AND_ASSIGN(auto id_resp, portIDGetResp("Ethernet1/1/1", "1"));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(id_req), _))
      .WillOnce(DoAll(SetArgPointee<2>(id_resp), Return(grpc::Status::OK)));
  ASSERT_OK(pins_test::GetBreakoutModeConfigFromString(
      req, mock_gnmi_stub_ptr.get(), port_index, intf_name, breakout_mode));
  EXPECT_THAT(req, EqualsProto(expected_breakout_config));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetBreakoutModeConfigFromStringChannelizedBreakoutModeSuccess) {
  const std::string port_index = "1";
  const std::string intf_name = "Ethernet1/1/1";
  const std::string breakout_mode = "2x200G";
  gnmi::SetRequest req, expected_breakout_config;
  const std::string expected_breakout_config_str = R"pb(
    prefix { origin: "openconfig" target: "chassis" }
    replace {
      path {}
      val {
        json_ietf_val: "{\n             \"openconfig-interfaces:interfaces\": { \"interface\": [ {\n             \"config\": {\n               \"enabled\": true,\n               \"loopback-mode\": \"NONE\",\n               \"mtu\": 9216,\n               \"name\": \"Ethernet1/1/1\",\n               \"type\": \"iana-if-type:ethernetCsmacd\",\n               \"openconfig-p4rt:id\": 1\n             },\n             \"name\": \"Ethernet1/1/1\",\n             \"openconfig-if-ethernet:ethernet\": {\n               \"config\": { \"port-speed\": \"openconfig-if-ethernet:SPEED_200GB\" }\n             },\n             \"subinterfaces\": {\n               \"subinterface\":\n               [ {\n                 \"config\": { \"index\": 0 },\n                 \"index\": 0,\n                 \"openconfig-if-ip:ipv6\": {\n                   \"unnumbered\": { \"config\": { \"enabled\": true } }\n                 }\n               }]\n             }\n           }\n      ,{\n             \"config\": {\n               \"enabled\": true,\n               \"loopback-mode\": \"NONE\",\n               \"mtu\": 9216,\n               \"name\": \"Ethernet1/1/5\",\n               \"type\": \"iana-if-type:ethernetCsmacd\",\n               \"openconfig-p4rt:id\": 2562\n             },\n             \"name\": \"Ethernet1/1/5\",\n             \"openconfig-if-ethernet:ethernet\": {\n               \"config\": { \"port-speed\": \"openconfig-if-ethernet:SPEED_200GB\" }\n             },\n             \"subinterfaces\": {\n               \"subinterface\":\n               [ {\n                 \"config\": { \"index\": 0 },\n                 \"index\": 0,\n                 \"openconfig-if-ip:ipv6\": {\n                   \"unnumbered\": { \"config\": { \"enabled\": true } }\n                 }\n               }]\n             }\n           }\n       ] },\n             \"openconfig-platform:components\": {\n               \"component\":\n               [ {\n                 \"name\": \"1/1\",\n                 \"config\": { \"name\": \"1/1\" },\n                 \"port\": {\n                   \"config\": { \"port-id\": 1 },\n                   \"breakout-mode\": { \"groups\": { \"group\": [ {\n             \"config\": {\n               \"breakout-speed\": \"openconfig-if-ethernet:SPEED_200GB\",\n               \"index\": 0,\n               \"num-breakouts\": 2,\n               \"num-physical-channels\": 4\n             },\n             \"index\": 0\n           } ] } }\n                 }\n               }]\n             }\n           }"
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
  gnmi::GetRequest ethernet_pmd_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      ethernet_pmd_req_str, &ethernet_pmd_req));
  gnmi::GetResponse ethernet_pmd_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      ethernet_pmd_resp_optic_str, &ethernet_pmd_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(ethernet_pmd_req), _))
      .WillOnce(
          DoAll(SetArgPointee<2>(ethernet_pmd_resp), Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(auto id_req1, portIDGetReq("Ethernet1/1/1"));
  ASSERT_OK_AND_ASSIGN(auto id_resp1, portIDGetResp("Ethernet1/1/1", "1"));
  ASSERT_OK_AND_ASSIGN(auto id_req2, portIDGetReq("Ethernet1/1/5"));
  ASSERT_OK_AND_ASSIGN(auto id_resp2, portIDGetResp("Ethernet1/1/5", "2562"));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(id_req1), _))
      .WillOnce(DoAll(SetArgPointee<2>(id_resp1), Return(grpc::Status::OK)));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(id_req2), _))
      .WillOnce(DoAll(SetArgPointee<2>(id_resp2), Return(grpc::Status::OK)));
  ASSERT_OK(pins_test::GetBreakoutModeConfigFromString(
      req, mock_gnmi_stub_ptr.get(), port_index, intf_name, breakout_mode));
  EXPECT_THAT(req, EqualsProto(expected_breakout_config));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetBreakoutModeConfigFromStringWithComputedIDSuccess) {
  const std::string port_index = "1";
  const std::string intf_name = "Ethernet1/1/1";
  const std::string breakout_mode = "2x200G";
  gnmi::SetRequest req, expected_breakout_config;
  const std::string expected_breakout_config_str = R"pb(
    prefix { origin: "openconfig" target: "chassis" }
    replace {
      path {}
      val {
        json_ietf_val: "{\n             \"openconfig-interfaces:interfaces\": { \"interface\": [ {\n             \"config\": {\n               \"enabled\": true,\n               \"loopback-mode\": \"NONE\",\n               \"mtu\": 9216,\n               \"name\": \"Ethernet1/1/1\",\n               \"type\": \"iana-if-type:ethernetCsmacd\",\n               \"openconfig-p4rt:id\": 1\n             },\n             \"name\": \"Ethernet1/1/1\",\n             \"openconfig-if-ethernet:ethernet\": {\n               \"config\": { \"port-speed\": \"openconfig-if-ethernet:SPEED_200GB\" }\n             },\n             \"subinterfaces\": {\n               \"subinterface\":\n               [ {\n                 \"config\": { \"index\": 0 },\n                 \"index\": 0,\n                 \"openconfig-if-ip:ipv6\": {\n                   \"unnumbered\": { \"config\": { \"enabled\": true } }\n                 }\n               }]\n             }\n           }\n      ,{\n             \"config\": {\n               \"enabled\": true,\n               \"loopback-mode\": \"NONE\",\n               \"mtu\": 9216,\n               \"name\": \"Ethernet1/1/5\",\n               \"type\": \"iana-if-type:ethernetCsmacd\",\n               \"openconfig-p4rt:id\": 2562\n             },\n             \"name\": \"Ethernet1/1/5\",\n             \"openconfig-if-ethernet:ethernet\": {\n               \"config\": { \"port-speed\": \"openconfig-if-ethernet:SPEED_200GB\" }\n             },\n             \"subinterfaces\": {\n               \"subinterface\":\n               [ {\n                 \"config\": { \"index\": 0 },\n                 \"index\": 0,\n                 \"openconfig-if-ip:ipv6\": {\n                   \"unnumbered\": { \"config\": { \"enabled\": true } }\n                 }\n               }]\n             }\n           }\n       ] },\n             \"openconfig-platform:components\": {\n               \"component\":\n               [ {\n                 \"name\": \"1/1\",\n                 \"config\": { \"name\": \"1/1\" },\n                 \"port\": {\n                   \"config\": { \"port-id\": 1 },\n                   \"breakout-mode\": { \"groups\": { \"group\": [ {\n             \"config\": {\n               \"breakout-speed\": \"openconfig-if-ethernet:SPEED_200GB\",\n               \"index\": 0,\n               \"num-breakouts\": 2,\n               \"num-physical-channels\": 4\n             },\n             \"index\": 0\n           } ] } }\n                 }\n               }]\n             }\n           }"
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
  gnmi::GetRequest ethernet_pmd_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      ethernet_pmd_req_str, &ethernet_pmd_req));
  gnmi::GetResponse ethernet_pmd_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      ethernet_pmd_resp_optic_str, &ethernet_pmd_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(ethernet_pmd_req), _))
      .WillOnce(
          DoAll(SetArgPointee<2>(ethernet_pmd_resp), Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(auto id_req1, portIDGetReq("Ethernet1/1/1"));
  ASSERT_OK_AND_ASSIGN(auto id_req2, portIDGetReq("Ethernet1/1/5"));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(id_req1), _))
      .WillOnce(Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(id_req2), _))
      .WillOnce(Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  ASSERT_OK(pins_test::GetBreakoutModeConfigFromString(
      req, mock_gnmi_stub_ptr.get(), port_index, intf_name, breakout_mode));
  EXPECT_THAT(req, EqualsProto(expected_breakout_config));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetBreakoutModeConfigFromStringMixedBreakoutModeSuccess) {
  const std::string port_index = "1";
  const std::string intf_name = "Ethernet1/1/1";
  const std::string breakout_mode = "1x200G(4)+2x100G(4)";
  gnmi::SetRequest req, expected_breakout_config;
  const std::string expected_breakout_config_str = R"pb(
    prefix { origin: "openconfig" target: "chassis" }
    replace {
      path {}
      val {
        json_ietf_val: "{\n             \"openconfig-interfaces:interfaces\": { \"interface\": [ {\n             \"config\": {\n               \"enabled\": true,\n               \"loopback-mode\": \"NONE\",\n               \"mtu\": 9216,\n               \"name\": \"Ethernet1/1/1\",\n               \"type\": \"iana-if-type:ethernetCsmacd\",\n               \"openconfig-p4rt:id\": 1\n             },\n             \"name\": \"Ethernet1/1/1\",\n             \"openconfig-if-ethernet:ethernet\": {\n               \"config\": { \"port-speed\": \"openconfig-if-ethernet:SPEED_200GB\" }\n             },\n             \"subinterfaces\": {\n               \"subinterface\":\n               [ {\n                 \"config\": { \"index\": 0 },\n                 \"index\": 0,\n                 \"openconfig-if-ip:ipv6\": {\n                   \"unnumbered\": { \"config\": { \"enabled\": true } }\n                 }\n               }]\n             }\n           }\n      ,{\n             \"config\": {\n               \"enabled\": true,\n               \"loopback-mode\": \"NONE\",\n               \"mtu\": 9216,\n               \"name\": \"Ethernet1/1/5\",\n               \"type\": \"iana-if-type:ethernetCsmacd\",\n               \"openconfig-p4rt:id\": 2562\n             },\n             \"name\": \"Ethernet1/1/5\",\n             \"openconfig-if-ethernet:ethernet\": {\n               \"config\": { \"port-speed\": \"openconfig-if-ethernet:SPEED_100GB\" }\n             },\n             \"subinterfaces\": {\n               \"subinterface\":\n               [ {\n                 \"config\": { \"index\": 0 },\n                 \"index\": 0,\n                 \"openconfig-if-ip:ipv6\": {\n                   \"unnumbered\": { \"config\": { \"enabled\": true } }\n                 }\n               }]\n             }\n           }\n      ,{\n             \"config\": {\n               \"enabled\": true,\n               \"loopback-mode\": \"NONE\",\n               \"mtu\": 9216,\n               \"name\": \"Ethernet1/1/7\",\n               \"type\": \"iana-if-type:ethernetCsmacd\",\n               \"openconfig-p4rt:id\": 3586\n             },\n             \"name\": \"Ethernet1/1/7\",\n             \"openconfig-if-ethernet:ethernet\": {\n               \"config\": { \"port-speed\": \"openconfig-if-ethernet:SPEED_100GB\" }\n             },\n             \"subinterfaces\": {\n               \"subinterface\":\n               [ {\n                 \"config\": { \"index\": 0 },\n                 \"index\": 0,\n                 \"openconfig-if-ip:ipv6\": {\n                   \"unnumbered\": { \"config\": { \"enabled\": true } }\n                 }\n               }]\n             }\n           }\n       ] },\n             \"openconfig-platform:components\": {\n               \"component\":\n               [ {\n                 \"name\": \"1/1\",\n                 \"config\": { \"name\": \"1/1\" },\n                 \"port\": {\n                   \"config\": { \"port-id\": 1 },\n                   \"breakout-mode\": { \"groups\": { \"group\": [ {\n             \"config\": {\n               \"breakout-speed\": \"openconfig-if-ethernet:SPEED_200GB\",\n               \"index\": 0,\n               \"num-breakouts\": 1,\n               \"num-physical-channels\": 4\n             },\n             \"index\": 0\n           },{\n             \"config\": {\n               \"breakout-speed\": \"openconfig-if-ethernet:SPEED_100GB\",\n               \"index\": 1,\n               \"num-breakouts\": 2,\n               \"num-physical-channels\": 2\n             },\n             \"index\": 1\n           } ] } }\n                 }\n               }]\n             }\n           }"
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
  gnmi::GetRequest ethernet_pmd_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      ethernet_pmd_req_str, &ethernet_pmd_req));
  gnmi::GetResponse ethernet_pmd_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      ethernet_pmd_resp_optic_str, &ethernet_pmd_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(ethernet_pmd_req), _))
      .WillOnce(
          DoAll(SetArgPointee<2>(ethernet_pmd_resp), Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(auto id_req1, portIDGetReq("Ethernet1/1/1"));
  ASSERT_OK_AND_ASSIGN(auto id_resp1, portIDGetResp("Ethernet1/1/1", "1"));
  ASSERT_OK_AND_ASSIGN(auto id_req2, portIDGetReq("Ethernet1/1/5"));
  ASSERT_OK_AND_ASSIGN(auto id_resp2, portIDGetResp("Ethernet1/1/5", "2562"));
  ASSERT_OK_AND_ASSIGN(auto id_req3, portIDGetReq("Ethernet1/1/7"));
  ASSERT_OK_AND_ASSIGN(auto id_resp3, portIDGetResp("Ethernet1/1/7", "3586"));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(id_req1), _))
      .WillOnce(DoAll(SetArgPointee<2>(id_resp1), Return(grpc::Status::OK)));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(id_req2), _))
      .WillOnce(DoAll(SetArgPointee<2>(id_resp2), Return(grpc::Status::OK)));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(id_req3), _))
      .WillOnce(DoAll(SetArgPointee<2>(id_resp3), Return(grpc::Status::OK)));
  ASSERT_OK(pins_test::GetBreakoutModeConfigFromString(
      req, mock_gnmi_stub_ptr.get(), port_index, intf_name, breakout_mode));
  EXPECT_THAT(req, EqualsProto(expected_breakout_config));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetBreakoutModeConfigFromStringCopperPortSuccess) {
  const std::string port_index = "1";
  const std::string intf_name = "Ethernet1/1/1";
  const std::string breakout_mode = "1x200G(4)+2x100G(4)";
  gnmi::SetRequest req, expected_breakout_config;
  const std::string expected_breakout_config_str = R"pb(
    prefix { origin: "openconfig" target: "chassis" }
    replace {
      path {}
      val {
        json_ietf_val: "{\n             \"openconfig-interfaces:interfaces\": { \"interface\": [ {\n               \"config\": {\n                 \"enabled\": true,\n                 \"loopback-mode\": \"NONE\",\n                 \"mtu\": 9216,\n                 \"name\": \"Ethernet1/1/1\",\n                 \"type\": \"iana-if-type:ethernetCsmacd\",\n                 \"openconfig-p4rt:id\": 1\n               },\n               \"name\": \"Ethernet1/1/1\",\n               \"openconfig-if-ethernet:ethernet\": {\n                 \"config\": {\n                   \"port-speed\": \"openconfig-if-ethernet:SPEED_200GB\",\n                   \"standalone-link-training\": true\n                 }\n               },\n               \"subinterfaces\": {\n                 \"subinterface\":\n                 [ {\n                   \"config\": { \"index\": 0 },\n                   \"index\": 0,\n                   \"openconfig-if-ip:ipv6\": {\n                     \"unnumbered\": { \"config\": { \"enabled\": true } }\n                   }\n                 }]\n               }\n             }\n        ,{\n               \"config\": {\n                 \"enabled\": true,\n                 \"loopback-mode\": \"NONE\",\n                 \"mtu\": 9216,\n                 \"name\": \"Ethernet1/1/5\",\n                 \"type\": \"iana-if-type:ethernetCsmacd\",\n                 \"openconfig-p4rt:id\": 2562\n               },\n               \"name\": \"Ethernet1/1/5\",\n               \"openconfig-if-ethernet:ethernet\": {\n                 \"config\": {\n                   \"port-speed\": \"openconfig-if-ethernet:SPEED_100GB\",\n                   \"standalone-link-training\": true\n                 }\n               },\n               \"subinterfaces\": {\n                 \"subinterface\":\n                 [ {\n                   \"config\": { \"index\": 0 },\n                   \"index\": 0,\n                   \"openconfig-if-ip:ipv6\": {\n                     \"unnumbered\": { \"config\": { \"enabled\": true } }\n                   }\n                 }]\n               }\n             }\n        ,{\n               \"config\": {\n                 \"enabled\": true,\n                 \"loopback-mode\": \"NONE\",\n                 \"mtu\": 9216,\n                 \"name\": \"Ethernet1/1/7\",\n                 \"type\": \"iana-if-type:ethernetCsmacd\",\n                 \"openconfig-p4rt:id\": 3586\n               },\n               \"name\": \"Ethernet1/1/7\",\n               \"openconfig-if-ethernet:ethernet\": {\n                 \"config\": {\n                   \"port-speed\": \"openconfig-if-ethernet:SPEED_100GB\",\n                   \"standalone-link-training\": true\n                 }\n               },\n               \"subinterfaces\": {\n                 \"subinterface\":\n                 [ {\n                   \"config\": { \"index\": 0 },\n                   \"index\": 0,\n                   \"openconfig-if-ip:ipv6\": {\n                     \"unnumbered\": { \"config\": { \"enabled\": true } }\n                   }\n                 }]\n               }\n             }\n         ] },\n             \"openconfig-platform:components\": {\n               \"component\":\n               [ {\n                 \"name\": \"1/1\",\n                 \"config\": { \"name\": \"1/1\" },\n                 \"port\": {\n                   \"config\": { \"port-id\": 1 },\n                   \"breakout-mode\": { \"groups\": { \"group\": [ {\n             \"config\": {\n               \"breakout-speed\": \"openconfig-if-ethernet:SPEED_200GB\",\n               \"index\": 0,\n               \"num-breakouts\": 1,\n               \"num-physical-channels\": 4\n             },\n             \"index\": 0\n           },{\n             \"config\": {\n               \"breakout-speed\": \"openconfig-if-ethernet:SPEED_100GB\",\n               \"index\": 1,\n               \"num-breakouts\": 2,\n               \"num-physical-channels\": 2\n             },\n             \"index\": 1\n           } ] } }\n                 }\n               }]\n             }\n           }"
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
  gnmi::GetRequest ethernet_pmd_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      ethernet_pmd_req_str, &ethernet_pmd_req));
  gnmi::GetResponse ethernet_pmd_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      ethernet_pmd_resp_copper_str, &ethernet_pmd_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(ethernet_pmd_req), _))
      .WillOnce(
          DoAll(SetArgPointee<2>(ethernet_pmd_resp), Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(auto id_req1, portIDGetReq("Ethernet1/1/1"));
  ASSERT_OK_AND_ASSIGN(auto id_resp1, portIDGetResp("Ethernet1/1/1", "1"));
  ASSERT_OK_AND_ASSIGN(auto id_req2, portIDGetReq("Ethernet1/1/5"));
  ASSERT_OK_AND_ASSIGN(auto id_resp2, portIDGetResp("Ethernet1/1/5", "2562"));
  ASSERT_OK_AND_ASSIGN(auto id_req3, portIDGetReq("Ethernet1/1/7"));
  ASSERT_OK_AND_ASSIGN(auto id_resp3, portIDGetResp("Ethernet1/1/7", "3586"));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(id_req1), _))
      .WillOnce(DoAll(SetArgPointee<2>(id_resp1), Return(grpc::Status::OK)));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(id_req2), _))
      .WillOnce(DoAll(SetArgPointee<2>(id_resp2), Return(grpc::Status::OK)));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(id_req3), _))
      .WillOnce(DoAll(SetArgPointee<2>(id_resp3), Return(grpc::Status::OK)));

  ASSERT_OK(pins_test::GetBreakoutModeConfigFromString(
      req, mock_gnmi_stub_ptr.get(), port_index, intf_name, breakout_mode));
  EXPECT_THAT(req, EqualsProto(expected_breakout_config));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetBreakoutModeConfigFromStringIntConversionFailure) {
  const std::string port_index = "1";
  const std::string intf_name = "Ethernet1/1/1";
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
  gnmi::GetRequest ethernet_pmd_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      ethernet_pmd_req_str, &ethernet_pmd_req));
  gnmi::GetResponse ethernet_pmd_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      ethernet_pmd_resp_optic_str, &ethernet_pmd_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(ethernet_pmd_req), _))
      .WillOnce(
          DoAll(SetArgPointee<2>(ethernet_pmd_resp), Return(grpc::Status::OK)));
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
  const std::string intf_name = "Ethernet1/1/1";
  const std::string breakout_mode = "Xx400G";
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  gnmi::GetRequest get_xcvrd_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(prefix { origin: "openconfig" target: "chassis" }
           path {
             elem { name: "interfaces" }
             elem {
               name: "interface"
               key { key: "name" value: "Ethernet1/1/1" }
             }
             elem { name: "state" }
             elem { name: "transceiver" }
           }
           type: STATE
           encoding: JSON_IETF)pb",
      &get_xcvrd_req));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(get_xcvrd_req), _))
      .WillOnce(Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  gnmi::SetRequest req;
  EXPECT_THAT(
      pins_test::GetBreakoutModeConfigFromString(
          req, mock_gnmi_stub_ptr.get(), port_index, intf_name, breakout_mode),
      StatusIs(absl::StatusCode::kDeadlineExceeded,
               HasSubstr("Failed to get GNMI state path value for port "
                         "transceiver for port Ethernet1/1/1")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetBreakoutModeConfigFromStringInvalidLaneNumberFailure) {
  const std::string port_index = "1";
  const std::string intf_name = "Ethernet1/1/X";
  const std::string breakout_mode = "1x400G";
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  gnmi::SetRequest req;
  EXPECT_THAT(
      pins_test::GetBreakoutModeConfigFromString(
          req, mock_gnmi_stub_ptr.get(), port_index, intf_name, breakout_mode),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr("Failed to convert string (X) to integer")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetNonExistingPortsAfterBreakoutForBreakoutAppliedSuccess) {
  absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>
      orig_breakout_info;
  orig_breakout_info["Ethernet1/1/1"] =
      pins_test::PortBreakoutInfo{"[0,1,2,3,4,5,6,7]", pins_test::kStateUp};
  absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>
      new_breakout_info;
  new_breakout_info["Ethernet1/1/1"] =
      pins_test::PortBreakoutInfo{"[0,1,2,3]", pins_test::kStateUp};
  new_breakout_info["Ethernet1/2/5"] =
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
  orig_breakout_info["Ethernet1/1/1"] =
      pins_test::PortBreakoutInfo{"[0,1,2,3]", pins_test::kStateUp};
  orig_breakout_info["Ethernet1/2/5"] =
      pins_test::PortBreakoutInfo{"[4,5,6,7]", pins_test::kStateUp};
  absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>
      new_breakout_info;
  new_breakout_info["Ethernet1/1/1"] =
      pins_test::PortBreakoutInfo{"[0,1,2,3,4,5,6,7]", pins_test::kStateUp};

  std::vector<std::string> expected_non_existing_ports{"Ethernet1/2/5"};
  EXPECT_THAT(GetNonExistingPortsAfterBreakout(orig_breakout_info,
                                               new_breakout_info, true),
              ContainerEq(expected_non_existing_ports));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetNonExistingPortsAfterBreakoutForBreakoutNotAppliedSuccess) {
  absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>
      orig_breakout_info;
  orig_breakout_info["Ethernet1/1/1"] =
      pins_test::PortBreakoutInfo{"[0,1,2,3,4,5,6,7]", pins_test::kStateUp};
  absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>
      new_breakout_info;
  new_breakout_info["Ethernet1/1/1"] =
      pins_test::PortBreakoutInfo{"[0,1,2,3]", pins_test::kStateDown};
  new_breakout_info["Ethernet1/2/5"] =
      pins_test::PortBreakoutInfo{"[4,5,6,7]", pins_test::kStateDown};

  std::vector<std::string> expected_non_existing_ports{"Ethernet1/2/5"};
  EXPECT_THAT(GetNonExistingPortsAfterBreakout(orig_breakout_info,
                                               new_breakout_info, false),
              ContainerEq(expected_non_existing_ports));
}

TEST_F(
    GNMIThinkitInterfaceUtilityTest,
    TestGetNonExistingPortsAfterBreakoutForBreakoutNotAppliedAlternateSuccess) {
  absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>
      orig_breakout_info;
  orig_breakout_info["Ethernet1/1/1"] =
      pins_test::PortBreakoutInfo{"[0,1,2,3]", pins_test::kStateUp};
  orig_breakout_info["Ethernet1/2/5"] =
      pins_test::PortBreakoutInfo{"[4,5,6,7]", pins_test::kStateUp};
  absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>
      new_breakout_info;
  new_breakout_info["Ethernet1/1/1"] =
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
  expected_port_info["Ethernet1/1/1"] =
      pins_test::PortBreakoutInfo{"[0,1,2,3,4,5,6,7]", pins_test::kStateUp};
  std::vector<std::string> non_existing_port_list;
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get)
      .WillOnce(DoAll(
          SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
              R"pb(notification {
                     timestamp: 1620348032128305716
                     prefix { origin: "openconfig" target: "chassis" }
                     update {
                       path { elem { name: "interfaces" } }
                       val {
                         json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet1/1/1\",\"state\":{\"oper-status\":\"DOWN\"}}]}}"
                       }
                     }
                   })pb")),
          Return(grpc::Status::OK)));
  EXPECT_THAT(
      pins_test::ValidateBreakoutState(
          mock_gnmi_stub_ptr.get(), expected_port_info, non_existing_port_list),
      StatusIs(absl::StatusCode::kUnavailable,
               HasSubstr("Some interfaces are not in the expected state UP")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestValidateBreakoutStatePhysicalChannelsMatchFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>
      expected_port_info;
  expected_port_info["Ethernet1/1/1"] =
      pins_test::PortBreakoutInfo{"[0,1,2,3]", pins_test::kStateUp};
  std::vector<std::string> non_existing_port_list;
  gnmi::GetRequest physical_channels_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(prefix { origin: "openconfig" target: "chassis" }
           path {
             elem { name: "interfaces" }
             elem {
               name: "interface"
               key { key: "name" value: "Ethernet1/1/1" }
             }
             elem { name: "state" }
             elem { name: "physical-channel" }
           }
           type: STATE
           encoding: JSON_IETF)pb",
      &physical_channels_req));
  gnmi::GetResponse physical_channels_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1632102697805380043
             prefix { origin: "openconfig" target: "chassis" }
             update {
               path {
                 elem { name: "interfaces" }
                 elem {
                   name: "interface"
                   key { key: "name" value: "Ethernet1/1/1" }
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
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get)
      .WillOnce(DoAll(
          SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
              R"pb(notification {
                     timestamp: 1620348032128305716
                     prefix { origin: "openconfig" target: "chassis" }
                     update {
                       path { elem { name: "interfaces" } }
                       val {
                         json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet1/1/1\",\"state\":{\"oper-status\":\"UP\"}}]}}"
                       }
                     }
                   })pb")),
          Return(grpc::Status::OK)));
  EXPECT_CALL(*mock_gnmi_stub_ptr,
              Get(_, EqualsProto(physical_channels_req), _))
      .WillOnce(DoAll(SetArgPointee<2>(physical_channels_resp),
                      Return(grpc::Status::OK)));
  EXPECT_THAT(
      pins_test::ValidateBreakoutState(
          mock_gnmi_stub_ptr.get(), expected_port_info, non_existing_port_list),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr(absl::StrCat(
                   "Physical channel match failed for port Ethernet1/1/1. got: "
                   "[0,1,2,3,4,5,6,7], want: ",
                   expected_port_info["Ethernet1/1/1"].physical_channels))));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestValidateBreakoutStateNonExistingPortListMatchFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>
      expected_port_info;
  expected_port_info["Ethernet1/1/1"] =
      pins_test::PortBreakoutInfo{"[0,1,2,3,4,5,6,7]", pins_test::kStateUp};
  std::vector<std::string> non_existing_port_list{"Ethernet1/1/1"};
  gnmi::GetRequest oper_status_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(prefix { origin: "openconfig" target: "chassis" }
           path {
             elem { name: "interfaces" }
             elem {
               name: "interface"
               key { key: "name" value: "Ethernet1/1/1" }
             }
             elem { name: "state" }
             elem { name: "oper-status" }
           }
           type: STATE
           encoding: JSON_IETF)pb",
      &oper_status_req));
  gnmi::GetResponse oper_status_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1632102697699213032
             prefix { origin: "openconfig" target: "chassis" }
             update {
               path {
                 elem { name: "interfaces" }
                 elem {
                   name: "interface"
                   key { key: "name" value: "Ethernet1/1/1" }
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
      R"pb(prefix { origin: "openconfig" target: "chassis" }
           path {
             elem { name: "interfaces" }
             elem {
               name: "interface"
               key { key: "name" value: "Ethernet1/1/1" }
             }
             elem { name: "state" }
             elem { name: "physical-channel" }
           }
           type: STATE
           encoding: JSON_IETF)pb",
      &physical_channels_req));
  gnmi::GetResponse physical_channels_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1632102697805380043
             prefix { origin: "openconfig" target: "chassis" }
             update {
               path {
                 elem { name: "interfaces" }
                 elem {
                   name: "interface"
                   key { key: "name" value: "Ethernet1/1/1" }
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
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get)
      .WillOnce(DoAll(
          SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
              R"pb(notification {
                     timestamp: 1620348032128305716
                     prefix { origin: "openconfig" target: "chassis" }
                     update {
                       path { elem { name: "interfaces" } }
                       val {
                         json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet1/1/1\",\"state\":{\"oper-status\":\"UP\"}}]}}"
                       }
                     }
                   })pb")),
          Return(grpc::Status::OK)));
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
               HasSubstr("Unexpected port (Ethernet1/1/1) found after "
                         "application of breakout mode")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest, TestValidateBreakoutStateSuccess) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>
      expected_port_info;
  expected_port_info["Ethernet1/1/1"] =
      pins_test::PortBreakoutInfo{"[0,1,2,3,4,5,6,7]", pins_test::kStateUp};
  std::vector<std::string> non_existing_port_list{};
  gnmi::GetRequest physical_channels_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(prefix { origin: "openconfig" target: "chassis" }
           path {
             elem { name: "interfaces" }
             elem {
               name: "interface"
               key { key: "name" value: "Ethernet1/1/1" }
             }
             elem { name: "state" }
             elem { name: "physical-channel" }
           }
           type: STATE
           encoding: JSON_IETF)pb",
      &physical_channels_req));
  gnmi::GetResponse physical_channels_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(notification {
             timestamp: 1632102697805380043
             prefix { origin: "openconfig" target: "chassis" }
             update {
               path {
                 elem { name: "interfaces" }
                 elem {
                   name: "interface"
                   key { key: "name" value: "Ethernet1/1/1" }
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
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get)
      .WillOnce(DoAll(
          SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
              R"pb(notification {
                     timestamp: 1620348032128305716
                     prefix { origin: "openconfig" target: "chassis" }
                     update {
                       path { elem { name: "interfaces" } }
                       val {
                         json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet1/1/1\",\"state\":{\"oper-status\":\"UP\"}}]}}"
                       }
                     }
                   })pb")),
          Return(grpc::Status::OK)));
  EXPECT_CALL(*mock_gnmi_stub_ptr,
              Get(_, EqualsProto(physical_channels_req), _))
      .WillOnce(DoAll(SetArgPointee<2>(physical_channels_resp),
                      Return(grpc::Status::OK)));
  EXPECT_OK(pins_test::ValidateBreakoutState(
      mock_gnmi_stub_ptr.get(), expected_port_info, non_existing_port_list));
}

TEST_F(GNMIThinkitInterfaceUtilityTest, TestGetPortIndexSuccess) {
  const std::string platform_json_contents =
      R"pb({ "interfaces": { "Ethernet1/1/1": { "index": "1,1,1,1,1,1,1,1" } } }
      )pb";
  const std::string port = "Ethernet1/1/1";
  const std::string expected_port_index = "1";
  EXPECT_THAT(pins_test::GetPortIndex(platform_json_contents, port),
              expected_port_index);
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetPortIndexInterfacesNotFoundFailure) {
  const std::string platform_json_contents =
      R"pb({}
      )pb";
  const std::string port = "Ethernet1/1/1";
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
  const std::string port = "Ethernet1/1/1";
  const std::string expected_port_index = "";
  EXPECT_THAT(pins_test::GetPortIndex(platform_json_contents, port),
              StatusIs(absl::StatusCode::kInternal,
                       HasSubstr(absl::StrCat(
                           port, " entry not found in platform.json"))));
}

TEST_F(GNMIThinkitInterfaceUtilityTest, TestGetPortIndexIndexNotFoundFailure) {
  const std::string platform_json_contents =
      R"pb({ "interfaces": { "Ethernet1/1/1": {} } }
      )pb";
  const std::string port = "Ethernet1/1/1";
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
  EXPECT_THAT(pins_test::BreakoutResultsInSpeedChangeOnly("Ethernet1/1/1",
                                                          "1x400G", "1x100G"),
              true);
  EXPECT_THAT(pins_test::BreakoutResultsInSpeedChangeOnly(
                  "Ethernet1/1/1", "1x200G(4)+2x100G(4)", "1x100G(4)+2x40G(4)"),
              true);
  EXPECT_THAT(pins_test::BreakoutResultsInSpeedChangeOnly("Ethernet1/1/1",
                                                          "1x400G", "2x200G"),
              false);
  EXPECT_THAT(pins_test::BreakoutResultsInSpeedChangeOnly(
                  "Ethernet1/1/1", "1x200G(4)+2x40G(4)", "1x200G(4)+1x40G(4)"),
              false);
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
  gnmi::GetRequest ethernet_pmd_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      ethernet_pmd_req_str, &ethernet_pmd_req));
  gnmi::GetResponse ethernet_pmd_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      ethernet_pmd_resp_optic_str, &ethernet_pmd_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(ethernet_pmd_req), _))
      .WillOnce(
          DoAll(SetArgPointee<2>(ethernet_pmd_resp), Return(grpc::Status::OK)));
  EXPECT_THAT(
      pins_test::IsCopperPort(mock_gnmi_stub_ptr.get(), "Ethernet1/1/1"),
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
  gnmi::GetRequest ethernet_pmd_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      ethernet_pmd_req_str, &ethernet_pmd_req));
  gnmi::GetResponse ethernet_pmd_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      ethernet_pmd_resp_copper_str, &ethernet_pmd_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(ethernet_pmd_req), _))
      .WillOnce(
          DoAll(SetArgPointee<2>(ethernet_pmd_resp), Return(grpc::Status::OK)));
  EXPECT_THAT(
      pins_test::IsCopperPort(mock_gnmi_stub_ptr.get(), "Ethernet1/1/1"), true);
}

TEST_F(GNMIThinkitInterfaceUtilityTest, TestIsCopperPortTransceiverGetFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  gnmi::GetRequest req;
  ASSERT_TRUE(
      google::protobuf::TextFormat::ParseFromString(get_xcvrd_req_str, &req));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(req), _))
      .WillOnce(Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  EXPECT_THAT(
      pins_test::IsCopperPort(mock_gnmi_stub_ptr.get(), "Ethernet1/1/1"),
      StatusIs(absl::StatusCode::kDeadlineExceeded,
               HasSubstr("Failed to get GNMI state path value for "
                         "port transceiver for port Ethernet1/1/1")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest, TestIsCopperPortEthernetPmdGetFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  gnmi::GetRequest req;
  ASSERT_TRUE(
      google::protobuf::TextFormat::ParseFromString(get_xcvrd_req_str, &req));
  gnmi::GetResponse resp;
  ASSERT_TRUE(
      google::protobuf::TextFormat::ParseFromString(get_xcvrd_resp_str, &resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(req), _))
      .WillOnce(DoAll(SetArgPointee<2>(resp), Return(grpc::Status::OK)));
  gnmi::GetRequest ethernet_pmd_req;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      ethernet_pmd_req_str, &ethernet_pmd_req));
  EXPECT_CALL(*mock_gnmi_stub_ptr, Get(_, EqualsProto(ethernet_pmd_req), _))
      .WillOnce(Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  EXPECT_THAT(
      pins_test::IsCopperPort(mock_gnmi_stub_ptr.get(), "Ethernet1/1/1"),
      StatusIs(absl::StatusCode::kDeadlineExceeded,
               HasSubstr("Failed to get GNMI state path value for "
                         "ethernet-pmd for port Ethernet1/1/1")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetSlotPortLaneForPortFrontPanelPortSuccess) {
  EXPECT_THAT(pins_test::GetSlotPortLaneForPort("Ethernet1/1/5"),
              IsOkAndHolds(FieldsAre(1, 1, 5)));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetSlotPortLaneForPortNonFrontPanelPortFailure) {
  EXPECT_THAT(pins_test::GetSlotPortLaneForPort("NonFrontPanelPort1/1/1"),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       HasSubstr("Requested port (NonFrontPanelPort1/1/1) is "
                                 "not a front panel port")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetSlotPortLaneForPortInvalidSlotFailure) {
  EXPECT_THAT(pins_test::GetSlotPortLaneForPort("EthernetX/1/1"),
              StatusIs(absl::StatusCode::kInternal,
                       HasSubstr("Failed to convert string (X) to integer")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetSlotPortLaneForPortInvalidPortFailure) {
  EXPECT_THAT(pins_test::GetSlotPortLaneForPort("Ethernet1/X/1"),
              StatusIs(absl::StatusCode::kInternal,
                       HasSubstr("Failed to convert string (X) to integer")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetSlotPortLaneForPortInvalidLaneFailure) {
  EXPECT_THAT(pins_test::GetSlotPortLaneForPort("Ethernet1/1/X"),
              StatusIs(absl::StatusCode::kInternal,
                       HasSubstr("Failed to convert string (X) to integer")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetSlotPortLaneForPortInvalidPortFormatFailure) {
  EXPECT_THAT(
      pins_test::GetSlotPortLaneForPort("Ethernet1"),
      StatusIs(absl::StatusCode::kInvalidArgument,
               HasSubstr("Requested port (Ethernet1) does not have a "
                         "valid format (EthernetX/Y/Z or EthernetX/Y)")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetSlotPortLaneForPortUnchannelizedPortSuccess) {
  EXPECT_THAT(pins_test::GetSlotPortLaneForPort("Ethernet1/33"),
              IsOkAndHolds(FieldsAre(1, 33, 1)));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetCurrentBreakoutModeForPortUnchannelizedModeSuccess) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_req,
                       currentBreakoutModeGetReq("1/1"));
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_resp,
                       currentBreakoutModeGetUnchannelizedResp("1/1"));
  EXPECT_CALL(*mock_gnmi_stub_ptr,
              Get(_, EqualsProto(current_breakout_mode_get_req), _))
      .WillOnce(DoAll(SetArgPointee<2>(current_breakout_mode_get_resp),
                      Return(grpc::Status::OK)));
  const std::string port_name = "Ethernet1/1/1";
  const std::string expected_breakout_mode = "1x400G";
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_req,
                       hardwarePortGetReq("Ethernet1/1/1"));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_resp,
                       hardwarePortGetResp("Ethernet1/1/1", "1"));
  EXPECT_CALL(*mock_gnmi_stub_ptr,
              Get(_, EqualsProto(hardware_port_get_req), _))
      .WillOnce(DoAll(SetArgPointee<2>(hardware_port_get_resp),
                      Return(grpc::Status::OK)));

  EXPECT_THAT(
      pins_test::GetCurrentBreakoutModeForPort(*mock_gnmi_stub_ptr, port_name),
      expected_breakout_mode);
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetCurrentBreakoutModeForPortMixedModeSuccess) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string port_name = "Ethernet1/1/1";
  const std::string expected_breakout_mode = "1x400G+2x200G";
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_req,
                       currentBreakoutModeGetReq("1/1"));
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_resp,
                       currentBreakoutModeGetMixedResp("1/1"));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_req,
                       hardwarePortGetReq("Ethernet1/1/1"));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_resp,
                       hardwarePortGetResp("Ethernet1/1/1", "1"));
  EXPECT_CALL(*mock_gnmi_stub_ptr,
              Get(_, EqualsProto(hardware_port_get_req), _))
      .WillOnce(DoAll(SetArgPointee<2>(hardware_port_get_resp),
                      Return(grpc::Status::OK)));
  EXPECT_CALL(*mock_gnmi_stub_ptr,
              Get(_, EqualsProto(current_breakout_mode_get_req), _))
      .WillOnce(DoAll(SetArgPointee<2>(current_breakout_mode_get_resp),
                      Return(grpc::Status::OK)));
  EXPECT_THAT(
      pins_test::GetCurrentBreakoutModeForPort(*mock_gnmi_stub_ptr, port_name),
      expected_breakout_mode);
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetCurrentBreakoutModeForPortFailureDueToNonParentPort) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string port_name = "Ethernet1/1/5";
  EXPECT_THAT(
      pins_test::GetCurrentBreakoutModeForPort(*mock_gnmi_stub_ptr, port_name),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr(absl::StrCat("Requested port (", port_name,
                                      ") is not a parent port"))));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetCurrentBreakoutModeForPortInvalidPortFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string port_name = "Ethernet1/1/X";
  EXPECT_THAT(
      pins_test::GetCurrentBreakoutModeForPort(*mock_gnmi_stub_ptr, port_name),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr("Failed to convert string (X) to integer")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetCurrentBreakoutModeForPortGroupNotFoundFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string port_name = "Ethernet1/1/1";
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_req,
                       currentBreakoutModeGetReq("1/1"));
  gnmi::GetResponse current_breakout_mode_get_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(
        notification {
          timestamp: 1631864194292383538
          prefix { origin: "openconfig" target: "chassis" }
          update {
            path {
              elem { name: "openconfig-platform:components" }
              elem {
                name: "component"
                key: { key: "name" value: "$0" }
              }
              elem { name: "port" }
              elem { name: "breakout-mode" }
              elem { name: "groups" }
            }
            val { json_ietf_val: "{\"openconfig-platform-port:groups\":{}}" }
          }
        }
      )pb",
      &current_breakout_mode_get_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr,
              Get(_, EqualsProto(current_breakout_mode_get_req), _))
      .WillOnce(DoAll(SetArgPointee<2>(current_breakout_mode_get_resp),
                      Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_req,
                       hardwarePortGetReq("Ethernet1/1/1"));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_resp,
                       hardwarePortGetResp("Ethernet1/1/1", "1"));
  EXPECT_CALL(*mock_gnmi_stub_ptr,
              Get(_, EqualsProto(hardware_port_get_req), _))
      .WillOnce(DoAll(SetArgPointee<2>(hardware_port_get_resp),
                      Return(grpc::Status::OK)));
  EXPECT_THAT(
      pins_test::GetCurrentBreakoutModeForPort(*mock_gnmi_stub_ptr, port_name),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr("group not found in state path response")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetCurrentBreakoutModeForPortIndexNotFoundInGroupFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string port_name = "Ethernet1/1/1";
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_req,
                       currentBreakoutModeGetReq("1/1"));
  gnmi::GetResponse current_breakout_mode_get_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(
        notification {
          timestamp: 1631864194292383538
          prefix { origin: "openconfig" target: "chassis" }
          update {
            path {
              elem { name: "openconfig-platform:components" }
              elem {
                name: "component"
                key: { key: "name" value: "$0" }
              }
              elem { name: "port" }
              elem { name: "breakout-mode" }
              elem { name: "groups" }
            }
            val {
              json_ietf_val: "{\"openconfig-platform-port:groups\":{\"group\":[{\"config\":{\"breakout-speed\":\"openconfig-if-ethernet:SPEED_200GB\",\"num-breakouts\":2,\"num-physical-channels\":4},\"state\":{\"breakout-speed\":\"openconfig-if-ethernet:SPEED_200GB\",\"index\":0,\"num-breakouts\":2,\"num-physical-channels\":4}}]}}"
            }
          }
        }
      )pb",
      &current_breakout_mode_get_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr,
              Get(_, EqualsProto(current_breakout_mode_get_req), _))
      .WillOnce(DoAll(SetArgPointee<2>(current_breakout_mode_get_resp),
                      Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_req,
                       hardwarePortGetReq("Ethernet1/1/1"));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_resp,
                       hardwarePortGetResp("Ethernet1/1/1", "1"));
  EXPECT_CALL(*mock_gnmi_stub_ptr,
              Get(_, EqualsProto(hardware_port_get_req), _))
      .WillOnce(DoAll(SetArgPointee<2>(hardware_port_get_resp),
                      Return(grpc::Status::OK)));
  EXPECT_THAT(
      pins_test::GetCurrentBreakoutModeForPort(*mock_gnmi_stub_ptr, port_name),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr("index not found in breakout group")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetCurrentBreakoutModeForPortStateNotFoundInGroupFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string port_name = "Ethernet1/1/1";
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_req,
                       currentBreakoutModeGetReq("1/1"));
  gnmi::GetResponse current_breakout_mode_get_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(
        notification {
          timestamp: 1631864194292383538
          prefix { origin: "openconfig" target: "chassis" }
          update {
            path {
              elem { name: "openconfig-platform:components" }
              elem {
                name: "component"
                key: { key: "name" value: "$0" }
              }
              elem { name: "port" }
              elem { name: "breakout-mode" }
              elem { name: "groups" }
            }
            val {
              json_ietf_val: "{\"openconfig-platform-port:groups\":{\"group\":[{\"config\":{\"breakout-speed\":\"openconfig-if-ethernet:SPEED_400GB\",\"index\":0,\"num-breakouts\":1,\"num-physical-channels\":8},\"index\":0}]}}"
            }
          }
        }
      )pb",
      &current_breakout_mode_get_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr,
              Get(_, EqualsProto(current_breakout_mode_get_req), _))
      .WillOnce(DoAll(SetArgPointee<2>(current_breakout_mode_get_resp),
                      Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_req,
                       hardwarePortGetReq("Ethernet1/1/1"));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_resp,
                       hardwarePortGetResp("Ethernet1/1/1", "1"));
  EXPECT_CALL(*mock_gnmi_stub_ptr,
              Get(_, EqualsProto(hardware_port_get_req), _))
      .WillOnce(DoAll(SetArgPointee<2>(hardware_port_get_resp),
                      Return(grpc::Status::OK)));

  EXPECT_THAT(
      pins_test::GetCurrentBreakoutModeForPort(*mock_gnmi_stub_ptr, port_name),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr("state not found in breakout group")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetCurrentBreakoutModeForPortNumBreakoutsNotFoundFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string port_name = "Ethernet1/1/1";
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_req,
                       currentBreakoutModeGetReq("1/1"));
  gnmi::GetResponse current_breakout_mode_get_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(
        notification {
          timestamp: 1631864194292383538
          prefix { origin: "openconfig" target: "chassis" }
          update {
            path {
              elem { name: "openconfig-platform:components" }
              elem {
                name: "component"
                key: { key: "name" value: "$0" }
              }
              elem { name: "port" }
              elem { name: "breakout-mode" }
              elem { name: "groups" }
            }
            val {
              json_ietf_val: "{\"openconfig-platform-port:groups\":{\"group\":[{\"config\":{\"breakout-speed\":\"openconfig-if-ethernet:SPEED_200GB\",\"index\":0,\"num-breakouts\":2,\"num-physical-channels\":4},\"index\":0,\"state\":{\"breakout-speed\":\"openconfig-if-ethernet:SPEED_200GB\",\"index\":0,\"num-physical-channels\":4}}]}}"
            }
          }
        }
      )pb",
      &current_breakout_mode_get_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr,
              Get(_, EqualsProto(current_breakout_mode_get_req), _))
      .WillOnce(DoAll(SetArgPointee<2>(current_breakout_mode_get_resp),
                      Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_req,
                       hardwarePortGetReq("Ethernet1/1/1"));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_resp,
                       hardwarePortGetResp("Ethernet1/1/1", "1"));
  EXPECT_CALL(*mock_gnmi_stub_ptr,
              Get(_, EqualsProto(hardware_port_get_req), _))
      .WillOnce(DoAll(SetArgPointee<2>(hardware_port_get_resp),
                      Return(grpc::Status::OK)));
  EXPECT_THAT(
      pins_test::GetCurrentBreakoutModeForPort(*mock_gnmi_stub_ptr, port_name),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr("num-breakouts not found in breakout group state")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetCurrentBreakoutModeForPortBreakoutSpeedNotFoundFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string port_name = "Ethernet1/1/1";
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_req,
                       currentBreakoutModeGetReq("1/1"));
  gnmi::GetResponse current_breakout_mode_get_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(
        notification {
          timestamp: 1631864194292383538
          prefix { origin: "openconfig" target: "chassis" }
          update {
            path {
              elem { name: "openconfig-platform:components" }
              elem {
                name: "component"
                key: { key: "name" value: "$0" }
              }
              elem { name: "port" }
              elem { name: "breakout-mode" }
              elem { name: "groups" }
            }
            val {
              json_ietf_val: "{\"openconfig-platform-port:groups\":{\"group\":[{\"config\":{\"breakout-speed\":\"openconfig-if-ethernet:SPEED_200GB\",\"index\":0,\"num-breakouts\":2,\"num-physical-channels\":4},\"index\":0,\"state\":{\"index\":0,\"num-breakouts\":2,\"num-physical-channels\":4}}]}}"
            }
          }
        }
      )pb",
      &current_breakout_mode_get_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr,
              Get(_, EqualsProto(current_breakout_mode_get_req), _))
      .WillOnce(DoAll(SetArgPointee<2>(current_breakout_mode_get_resp),
                      Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_req,
                       hardwarePortGetReq("Ethernet1/1/1"));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_resp,
                       hardwarePortGetResp("Ethernet1/1/1", "1"));
  EXPECT_CALL(*mock_gnmi_stub_ptr,
              Get(_, EqualsProto(hardware_port_get_req), _))
      .WillOnce(DoAll(SetArgPointee<2>(hardware_port_get_resp),
                      Return(grpc::Status::OK)));
  EXPECT_THAT(
      pins_test::GetCurrentBreakoutModeForPort(*mock_gnmi_stub_ptr, port_name),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr("breakout-speed not found in breakout group state")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetCurrentBreakoutModeForPortInvalidIndexFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string port_name = "Ethernet1/1/1";
  ASSERT_OK_AND_ASSIGN(auto current_breakout_mode_get_req,
                       currentBreakoutModeGetReq("1/1"));
  gnmi::GetResponse current_breakout_mode_get_resp;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(
        notification {
          timestamp: 1631864194292383538
          prefix { origin: "openconfig" target: "chassis" }
          update {
            path {
              elem { name: "openconfig-platform:components" }
              elem {
                name: "component"
                key: { key: "name" value: "$0" }
              }
              elem { name: "port" }
              elem { name: "breakout-mode" }
              elem { name: "groups" }
            }
            val {
              json_ietf_val: "{\"openconfig-platform-port:groups\":{\"group\":[{\"config\":{\"breakout-speed\":\"openconfig-if-ethernet:SPEED_400GB\",\"index\":0,\"num-breakouts\":1,\"num-physical-channels\":8},\"index\":\"X\",\"state\":{\"breakout-speed\":\"openconfig-if-ethernet:SPEED_400GB\",\"index\":0,\"num-breakouts\":1,\"num-physical-channels\":8}}]}}"
            }
          }
        }
      )pb",
      &current_breakout_mode_get_resp));
  EXPECT_CALL(*mock_gnmi_stub_ptr,
              Get(_, EqualsProto(current_breakout_mode_get_req), _))
      .WillOnce(DoAll(SetArgPointee<2>(current_breakout_mode_get_resp),
                      Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_req,
                       hardwarePortGetReq("Ethernet1/1/1"));
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_resp,
                       hardwarePortGetResp("Ethernet1/1/1", "1"));
  EXPECT_CALL(*mock_gnmi_stub_ptr,
              Get(_, EqualsProto(hardware_port_get_req), _))
      .WillOnce(DoAll(SetArgPointee<2>(hardware_port_get_resp),
                      Return(grpc::Status::OK)));
  EXPECT_THAT(
      pins_test::GetCurrentBreakoutModeForPort(*mock_gnmi_stub_ptr, port_name),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr("Failed to convert string (\"X\") to integer")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest,
       TestGetCurrentBreakoutModeForPortPhysicalPortGetFailure) {
  auto mock_gnmi_stub_ptr = absl::make_unique<gnmi::MockgNMIStub>();
  const std::string port_name = "Ethernet1/1/1";
  ASSERT_OK_AND_ASSIGN(auto hardware_port_get_req,
                       hardwarePortGetReq("Ethernet1/1/1"));
  EXPECT_CALL(*mock_gnmi_stub_ptr,
              Get(_, EqualsProto(hardware_port_get_req), _))
      .WillOnce(Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  EXPECT_THAT(
      pins_test::GetCurrentBreakoutModeForPort(*mock_gnmi_stub_ptr, port_name),
      StatusIs(absl::StatusCode::kDeadlineExceeded,
               HasSubstr("Failed to get GNMI state path value for interface "
                         "hardware-port for port Ethernet1/1/1")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest, TestIsParentPortSuccessForParentPort) {
  const std::string port = "Ethernet1/1/1";
  EXPECT_THAT(IsParentPort(port), true);
}

TEST_F(GNMIThinkitInterfaceUtilityTest, TestIsParentPortSuccessForChildPort) {
  const std::string port = "Ethernet1/1/5";
  EXPECT_THAT(IsParentPort(port), false);
}

TEST_F(GNMIThinkitInterfaceUtilityTest, TestIsParentPortIntConversionFailure) {
  const std::string port = "Ethernet1/1/X";
  EXPECT_THAT(IsParentPort(port),
              StatusIs(absl::StatusCode::kInternal,
                       HasSubstr("Failed to convert string (X) to integer")));
}

TEST_F(GNMIThinkitInterfaceUtilityTest, TestDeriveEkPhysicalPortSuccess) {
  const std::string port = "Ethernet1/1/2";
  EXPECT_THAT(DeriveEkPhysicalPort(port), "phy-1/1");
}

TEST_F(GNMIThinkitInterfaceUtilityTest, TestDeriveEkPhysicalPortFailure) {
  const std::string port = "Ethernet1/X";
  EXPECT_THAT(
      DeriveEkPhysicalPort(port),
      StatusIs(absl::StatusCode::kInternal, HasSubstr("no match found for ")));
}

}  // namespace pins_test
