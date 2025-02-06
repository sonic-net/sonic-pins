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
#include "tests/gnmi/util.h"

#include <string>

#include "absl/status/status.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "glog/logging.h"
#include "gutil/status.h"
#include "lib/gnmi/gnmi_helper.h"
#include "proto/gnmi/gnmi.grpc.pb.h"

namespace pins_test {
namespace {

constexpr char kEnabledFalse[] = "{\"enabled\":false}";
constexpr char kEnabledTrue[] = "{\"enabled\":true}";

}  // namespace

absl::Status SetAdminStatus(gnmi::gNMI::StubInterface* gnmi_stub,
                            absl::string_view if_name,
                            absl::string_view if_status) {
  std::string enable_status;
  if (if_status == "UP") {
    enable_status = kEnabledTrue;
  } else if (if_status == "DOWN") {
    enable_status = kEnabledFalse;
  } else {
    return absl::InvalidArgumentError("Interface status invalid.");
  }

  // Enable/Disable front panel port.
  LOG(INFO) << "Set front panel port " << if_name << " status: " << if_status;
  const std::string if_enabled_config_path =
      absl::StrCat("interfaces/interface[name=", if_name, "]/config/enabled");
  RETURN_IF_ERROR(pins_test::SetGnmiConfigPath(
      gnmi_stub, if_enabled_config_path, GnmiSetType::kUpdate, enable_status));
  absl::SleepFor(absl::Seconds(15));

  // Verifies /interfaces/interface[name=<port>]/state/admin-status = UP/DOWN.
  std::string if_state_path =
      absl::StrCat("interfaces/interface[name=", if_name, "]/state");
  std::string resp_parse_str = "openconfig-interfaces:state";
  ASSIGN_OR_RETURN(
      std::string state_path_response,
      GetGnmiStatePathInfo(gnmi_stub, if_state_path, resp_parse_str));
  if (!absl::StrContains(state_path_response, if_status)) {
    return absl::InternalError(
        absl::StrCat("Unable to set admin status: ", if_status));
  }
  return absl::OkStatus();
}

}  // namespace pins_test
