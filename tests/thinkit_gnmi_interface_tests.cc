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
#include <unordered_map>
#include <utility>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_split.h"
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

void TestGnmiPortComponentPaths(
    thinkit::SSHClient& ssh_client, thinkit::Switch& sut,
    absl::flat_hash_map<std::string, std::string>& expected_port_index_map) {
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());

  // Configure integrated circuit name on the switch.
  const std::string ic_name = "integrated_circuit0";
  const std::string ic_name_config_path =
      absl::StrCat("components/component[name=", ic_name, "]/config/name");
  ASSERT_OK(SetGnmiConfigPath(sut_gnmi_stub.get(), ic_name_config_path,
                              GnmiSetType::kUpdate,
                              ConstructGnmiConfigSetString("name", ic_name)));

  for (const auto& [port_name, port_index] : expected_port_index_map) {
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
    const auto separator_location = hw_port.find('/');
    ASSERT_NE(separator_location, std::string::npos);
    const std::string port_number = hw_port.substr(separator_location + 1);
    ASSERT_EQ(port_index, port_number);

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

void TestGnmiInterfaceConfigSetPortSpeed(
    thinkit::Switch& sut, absl::string_view if_name,
    const std::vector<int>& supported_speeds) {
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());

  // Get current configured port speed for the port.
  std::string if_state_path = absl::StrCat(
      "interfaces/interface[name=", if_name, "]/ethernet/state/port-speed");
  std::string resp_parse_str = "openconfig-if-ethernet:port-speed";
  ASSERT_OK_AND_ASSIGN(
      std::string state_path_response,
      GetGnmiStatePathInfo(sut_gnmi_stub.get(), if_state_path, resp_parse_str));
  state_path_response.erase(
      std::remove(state_path_response.begin(), state_path_response.end(), '\"'),
      state_path_response.end());
  // Save the original port speed to reset it later.
  const std::string kOriginalPortSpeedStr = state_path_response;

  // Extract current port speed from port speed string.
  // Port speed string is in the format:
  // "openconfig-if-ethernet:SPEED_<numerical_speed_value_in_GB>GB"
  auto separator_location = state_path_response.find('_');
  ASSERT_NE(separator_location, std::string::npos);
  std::string current_port_speed_str =
      kOriginalPortSpeedStr.substr(separator_location + 1);
  separator_location = current_port_speed_str.find(kGB);
  ASSERT_NE(separator_location, std::string::npos);
  current_port_speed_str = current_port_speed_str.substr(0, separator_location);

  int current_port_speed = 0;
  ASSERT_TRUE(absl::SimpleAtoi(current_port_speed_str, &current_port_speed));
  LOG(INFO) << "Current port speed for port " << if_name << " is "
            << current_port_speed << kGB << ".";

  // Pick a valid new port speed for the port that is less than current speed.
  int new_port_speed = 0;
  for (const auto& speed : supported_speeds) {
    if (speed < current_port_speed) {
      new_port_speed = speed;
      break;
    }
  }
  // Set new speed for the port if a valid lower speed is found.
  if (new_port_speed) {
    const std::string kNewPortSpeedStr = absl::StrCat(
        "openconfig-if-ethernet:SPEED_", std::to_string(new_port_speed), kGB);
    LOG(INFO) << "Changing port speed for " << if_name
              << " to a lower supported speed (" << kNewPortSpeedStr << ").";

    // Set new port speed.
    std::string if_port_speed_config_path = absl::StrCat(
        "interfaces/interface[name=", if_name, "]/ethernet/config/port-speed");
    ASSERT_OK(SetGnmiConfigPath(
        sut_gnmi_stub.get(), if_port_speed_config_path, GnmiSetType::kUpdate,
        ConstructGnmiConfigSetString(kPortSpeed, kNewPortSpeedStr)));
    absl::SleepFor(absl::Seconds(5));

    // Perform state path verifications.
    // Verify /interfaces/interface[name=<port>]/ethernet/state/port-speed =
    // new port speed.
    ASSERT_OK_AND_ASSIGN(state_path_response,
                         GetGnmiStatePathInfo(sut_gnmi_stub.get(),
                                              if_state_path, resp_parse_str));
    EXPECT_THAT(state_path_response, HasSubstr(kNewPortSpeedStr));
    // Verify that /interfaces/interface[name=<port>]/state/oper-status = DOWN.
    if_state_path = absl::StrCat("interfaces/interface[name=", if_name,
                                 "]/state/oper-status");
    resp_parse_str = "openconfig-interfaces:oper-status";
    ASSERT_OK_AND_ASSIGN(state_path_response,
                         GetGnmiStatePathInfo(sut_gnmi_stub.get(),
                                              if_state_path, resp_parse_str));
    EXPECT_THAT(state_path_response, HasSubstr(kStateDown));
  } else {
    LOG(INFO) << "No lower supported port speed found for port " << if_name
              << ". Resetting original port speed.";
  }
  LOG(INFO) << "Setting port speed for " << if_name << " to "
            << kOriginalPortSpeedStr;
  // Reset port speed to original speed.
  std::string if_port_speed_config_path = absl::StrCat(
      "interfaces/interface[name=", if_name, "]/ethernet/config/port-speed");
  ASSERT_OK(SetGnmiConfigPath(
      sut_gnmi_stub.get(), if_port_speed_config_path, GnmiSetType::kUpdate,
      ConstructGnmiConfigSetString(kPortSpeed, kOriginalPortSpeedStr)));
  absl::SleepFor(absl::Seconds(5));

  // Verify /interfaces/interface[name=<port>]/ethernet/state/port-speed =
  // original speed.
  if_state_path = absl::StrCat("interfaces/interface[name=", if_name,
                               "]/ethernet/state/port-speed");
  resp_parse_str = "openconfig-if-ethernet:port-speed";
  ASSERT_OK_AND_ASSIGN(
      state_path_response,
      GetGnmiStatePathInfo(sut_gnmi_stub.get(), if_state_path, resp_parse_str));
  EXPECT_THAT(state_path_response, HasSubstr(kOriginalPortSpeedStr));

  // Verify that /interfaces/interface[name=<port>]/state/oper-status = UP.
  if_state_path = absl::StrCat("interfaces/interface[name=", if_name,
                               "]/state/oper-status");
  resp_parse_str = "openconfig-interfaces:oper-status";
  ASSERT_OK_AND_ASSIGN(
      state_path_response,
      GetGnmiStatePathInfo(sut_gnmi_stub.get(), if_state_path, resp_parse_str));
  EXPECT_THAT(state_path_response, HasSubstr(kStateUp));
}

void TestGnmiInterfaceConfigSetId(thinkit::Switch& sut,
                                  absl::string_view if_name, const int id) {
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());

  // Set port Id.
  const std::string if_id_config_path =
      absl::StrCat("interfaces/interface[name=", if_name, "]/config/id");
  ASSERT_OK(SetGnmiConfigPath(sut_gnmi_stub.get(), if_id_config_path,
                              GnmiSetType::kUpdate,
                              ConstructGnmiConfigSetString("id", id)));
  absl::SleepFor(absl::Seconds(5));

  // Perform state path verifications.
  // Verify /interfaces/interface[name=<port>]/state/id = <configured_value>.
  std::string if_state_path =
      absl::StrCat("interfaces/interface[name=", if_name, "]/state/id");
  std::string resp_parse_str = "openconfig-pins-interfaces:id";
  ASSERT_OK_AND_ASSIGN(
      std::string state_path_response,
      GetGnmiStatePathInfo(sut_gnmi_stub.get(), if_state_path, resp_parse_str));
  EXPECT_THAT(state_path_response, HasSubstr(std::to_string(id)));
}
}  // namespace pins_test
