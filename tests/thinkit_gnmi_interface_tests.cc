// Copyright 2024 Google LLC
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

#include "tests/thinkit_gnmi_interface_tests.h"

#include <algorithm>
#include <string>
#include <utility>

#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "lib/gnmi/gnmi_helper.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "include/nlohmann/json.hpp"
#include "tests/thinkit_util.h"
#include "thinkit/ssh_client.h"
#include "thinkit/switch.h"

namespace pins_test {
namespace {

using ::nlohmann::json;
using ::testing::HasSubstr;

}  // namespace

void TestGnmiInterfaceConfigSetAdminStatus(thinkit::Switch& sut,
                                           absl::string_view if_name) {
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());

  // Disable front panel port.
  LOG(INFO) << "Disabling front panel port: " << if_name;
  const std::string if_enabled_config_path =
      absl::StrCat("interfaces/interface[name=", if_name, "]/config/enabled");
  ASSERT_OK(SetGnmiConfigPath(sut_gnmi_stub.get(), if_enabled_config_path,
                              GnmiSetType::kUpdate, kEnabledFalse));

  // Perform state path verifications.
  // Verify /interfaces/interface[name=<port>]/state/enabled = false.
  std::string if_state_path =
      absl::StrCat("interfaces/interface[name=", if_name, "]/state/enabled");
  std::string resp_parse_str = "openconfig-interfaces:enabled";
  ASSERT_OK_AND_ASSIGN(
      std::string state_path_response,
      GetGnmiStatePathInfo(sut_gnmi_stub.get(), if_state_path, resp_parse_str));
  EXPECT_THAT(state_path_response, HasSubstr("false"));

  // Verify /interfaces/interface[name=<port>]/state/admin-status = DOWN.
  if_state_path = absl::StrCat("interfaces/interface[name=", if_name,
                               "]/state/admin-status");
  resp_parse_str = "openconfig-interfaces:admin-status";
  ASSERT_OK_AND_ASSIGN(
      state_path_response,
      GetGnmiStatePathInfo(sut_gnmi_stub.get(), if_state_path, resp_parse_str));
  EXPECT_THAT(state_path_response, HasSubstr(kStateDown));

  // Verify /interfaces/interface[name=<port>]/state/oper-status = DOWN.
  if_state_path = absl::StrCat("interfaces/interface[name=", if_name,
                               "]/state/oper-status");
  resp_parse_str = "openconfig-interfaces:oper-status";
  ASSERT_OK_AND_ASSIGN(
      state_path_response,
      GetGnmiStatePathInfo(sut_gnmi_stub.get(), if_state_path, resp_parse_str));
  EXPECT_THAT(state_path_response, HasSubstr(kStateDown));

  // Enable front panel port.
  LOG(INFO) << "Enabling front panel port: " << if_name;
  ASSERT_OK(SetGnmiConfigPath(sut_gnmi_stub.get(), if_enabled_config_path,
                              GnmiSetType::kUpdate, kEnabledTrue));

  // Perform state path verifications.
  // Verify /interfaces/interface[name=<port>]/state/enabled = true.
  if_state_path =
      absl::StrCat("interfaces/interface[name=", if_name, "]/state/enabled");
  resp_parse_str = "openconfig-interfaces:enabled";
  ASSERT_OK_AND_ASSIGN(
      state_path_response,
      GetGnmiStatePathInfo(sut_gnmi_stub.get(), if_state_path, resp_parse_str));
  EXPECT_THAT(state_path_response, HasSubstr("true"));

  // Verify /interfaces/interface[name=<port>]/state/admin-status = UP.
  if_state_path = absl::StrCat("interfaces/interface[name=", if_name,
                               "]/state/admin-status");
  resp_parse_str = "openconfig-interfaces:admin-status";
  ASSERT_OK_AND_ASSIGN(
      state_path_response,
      GetGnmiStatePathInfo(sut_gnmi_stub.get(), if_state_path, resp_parse_str));
  EXPECT_THAT(state_path_response, HasSubstr(kStateUp));

  // Verify /interfaces/interface[name=<port>]/state/oper-status = UP.
  absl::SleepFor(absl::Seconds(5));
  if_state_path = absl::StrCat("interfaces/interface[name=", if_name,
                               "]/state/oper-status");
  resp_parse_str = "openconfig-interfaces:oper-status";
  ASSERT_OK_AND_ASSIGN(
      state_path_response,
      GetGnmiStatePathInfo(sut_gnmi_stub.get(), if_state_path, resp_parse_str));
  EXPECT_THAT(state_path_response, HasSubstr(kStateUp));
}

void TestGnmiPortComponentPaths(thinkit::SSHClient& ssh_client,
                                thinkit::Switch& sut,
                                absl::string_view platform_json_path) {
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());

  // Configure integrated circuit name on the switch.
  const std::string ic_name = "integrated-circuit0";
  const std::string ic_name_config_path =
      absl::StrCat("components/component[name=", ic_name, "]/config/name");
  ASSERT_OK(SetGnmiConfigPath(sut_gnmi_stub.get(), ic_name_config_path,
                              GnmiSetType::kUpdate,
                              ConstructGnmiConfigSetString("name", ic_name)));

  // Fetch platform.json from the switch.
  const std::string ssh_command =
      absl::StrCat("cat ", platform_json_path, kPlatformJson);
  LOG(INFO) << "Fetching " << kPlatformJson
            << " contents from switch path: " << platform_json_path;
  ASSERT_OK_AND_ASSIGN(std::string platform_json_contents,
                       ssh_client.RunCommand(sut.ChassisName(), ssh_command,
                                             absl::ZeroDuration()));
  LOG(INFO) << kPlatformJson << " contents: " << platform_json_contents;

  // Fetch interface information from platform.json.
  const auto platform_json = json::parse(platform_json_contents);
  const auto interface_json = platform_json.find(kInterfaces);
  ASSERT_NE(interface_json, platform_json.end());

  for (const auto& interface : interface_json->items()) {
    const std::string port_name = interface.key();
    const auto port_info = interface.value();
    ASSERT_EQ(port_info.count("index"), 1);

    // Fetch /interfaces/interface[name=<port>]/state/hardware-port.
    const std::string hw_port_state_path = absl::StrCat(
        "interfaces/interface[name=", port_name, "]/state/hardware-port");
    const std::string hw_port_parse_str =
        "openconfig-platform-port:hardware-port";
    ASSERT_OK_AND_ASSIGN(
        std::string hw_port,
        GetGnmiStatePathInfo(sut_gnmi_stub.get(), hw_port_state_path,
                             hw_port_parse_str));
    hw_port.erase(std::remove(hw_port.begin(), hw_port.end(), '"'),
                  hw_port.end());

    // hardware-port is in the format 1/<port_no>. Fetch port number from this
    // information and verify that it is same as index attribute of the port in
    // platform.json.
    const auto separator_location = hw_port.find("/");
    ASSERT_NE(separator_location, std::string::npos);
    const std::string port_number = hw_port.substr(separator_location + 1);
    ASSERT_EQ(port_info["index"], port_number);

    // Verify that hardware-port attribute matches information in path
    // /components/component[name=<port>]/state/name.
    const std::string component_name_state_path =
        absl::StrCat("components/component[name=", hw_port, "]/state/name");
    const std::string component_name_parse_str = "openconfig-platform:name";
    ASSERT_OK_AND_ASSIGN(
        const std::string component_name,
        GetGnmiStatePathInfo(sut_gnmi_stub.get(), component_name_state_path,
                             component_name_parse_str));
    EXPECT_THAT(component_name, HasSubstr(hw_port));

    // Verify that integrated circuit name matches information in path
    // /components/component[name=<port>]/state/parent.
    const std::string component_parent_state_path =
        absl::StrCat("components/component[name=", hw_port, "]/state/parent");
    const std::string component_parent_parse_str = "openconfig-platform:parent";
    ASSERT_OK_AND_ASSIGN(
        const std::string component_parent,
        GetGnmiStatePathInfo(sut_gnmi_stub.get(), component_parent_state_path,
                             component_parent_parse_str));
    EXPECT_THAT(component_parent, HasSubstr(ic_name));
  }
}

}  // namespace pins_test
