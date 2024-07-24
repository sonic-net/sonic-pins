// Copyright 2024 Google LLC
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
#include "tests/gnmi/link_flap_tests.h"

#include <string>

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "lib/gnmi/gnmi_helper.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/proto/generic_testbed.pb.h"
#include "thinkit/switch.h"

namespace pins_test {
namespace {

using ::gutil::IsOkAndHolds;

constexpr char kEnabledFalse[] = "{\"enabled\":false}";
constexpr char kEnabledTrue[] = "{\"enabled\":true}";

absl::Status SetAdminStatus(gnmi::gNMI::Stub* gnmi_stub,
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

}  // namespace

TEST_P(ExampleTestFixture, LinkFlapTest) {
  thinkit::TestRequirements requirements =
      gutil::ParseProtoOrDie<thinkit::TestRequirements>(
          R"pb(interface_requirements {
                 count: 1
                 interface_mode: CONTROL_INTERFACE
               })pb");
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<thinkit::GenericTestbed> generic_testbed,
                       GetTestbedWithRequirements(requirements));
  absl::flat_hash_map<std::string, thinkit::InterfaceInfo> interface_info =
      generic_testbed->GetSutInterfaceInfo();
  std::string sut_interface;
  std::string peer_interface;
  for (const auto& [interface, info] : interface_info) {
    if (info.interface_mode == thinkit::CONTROL_INTERFACE) {
      sut_interface = interface;
      peer_interface = info.peer_interface_name;
      break;
    }
  }
  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, generic_testbed->Sut().CreateGnmiStub());

  // Flaps SUT port through gNMI (admin state) and checks that the control
  // switch detects it.

  // Sets admin-status Down through gNMI.
  LOG(INFO) << "Set sut " << sut_interface << " admin link state down.";
  EXPECT_OK(SetAdminStatus(gnmi_stub.get(), sut_interface, "DOWN"));
  EXPECT_THAT(generic_testbed->Interface().GetUpLinks({peer_interface}),
              IsOkAndHolds(testing::IsEmpty()));
  // Sets admin-status Up through gNMI.
  EXPECT_OK(SetAdminStatus(gnmi_stub.get(), sut_interface, "UP"));
  EXPECT_THAT(generic_testbed->Interface().GetUpLinks({peer_interface}),
              IsOkAndHolds(testing::Contains(sut_interface)));

  // Flaps control switch port and checks that SUT’s gNMI reflects that.
  LOG(INFO) << "Set control switch " << peer_interface
            << " admin link state down.";
  EXPECT_OK(generic_testbed->Interface().SetAdminLinkState(
      {peer_interface}, thinkit::LinkState::kDown));
  absl::SleepFor(absl::Seconds(15));
  // Checks oper-status through gNMI.
  EXPECT_THAT(GetInterfaceOperStatusOverGnmi(*gnmi_stub, sut_interface),
              IsOkAndHolds(OperStatus::kDown));
  EXPECT_OK(generic_testbed->Interface().SetAdminLinkState(
      {peer_interface}, thinkit::LinkState::kUp));
  absl::SleepFor(absl::Seconds(15));
  EXPECT_THAT(GetInterfaceOperStatusOverGnmi(*gnmi_stub, sut_interface),
              IsOkAndHolds(OperStatus::kUp));
}

}  // namespace pins_test
