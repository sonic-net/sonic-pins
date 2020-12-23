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

}  // namespace pins_test
