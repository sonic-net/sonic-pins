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

#include "tests/integration/system/nsf/nsf_dynamic_state_update_test.h"

#include <memory>
#include <string>
#include <vector>

#include "absl/log/log.h"
#include "absl/random/random.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "lib/gnmi/gnmi_helper.h"
#include "tests/integration/system/nsf/interfaces/testbed.h"
#include "tests/integration/system/nsf/util.h"
#include "thinkit/control_device.h"
#include "thinkit/proto/generic_testbed.pb.h"
#include "thinkit/ssh_client.h"
#include "thinkit/switch.h"

namespace pins_test {

using ::gnoi::system::RebootMethod;
using ::testing::IsEmpty;

TEST_P(NsfDynamicStateUpdateTestFixture, NsfDynamicStateUpdateTest) {
  GetParam().generic_testbed->ExpectLinkFlaps();

  thinkit::TestRequirements requirements =
      gutil::ParseProtoOrDie<thinkit::TestRequirements>(
          R"pb(interface_requirements {
                 count: 1
                 interface_mode: CONTROL_INTERFACE
               })pb");
  ASSERT_OK_AND_ASSIGN(
      auto generic_testbed,
      GetParam().generic_testbed->GetTestbedWithRequirements(requirements));
  // Get control switch and SUT
  thinkit::Switch& sut = generic_testbed->Sut();
  thinkit::ControlDevice& control_device = generic_testbed->ControlDevice();

  // Get pins_test testbed

  // Get ssh client and gnmi stub
  thinkit::SSHClient& ssh_client = *GetParam().ssh_client;
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());

  // The following section of code is to select a up port randomly
  ASSERT_OK_AND_ASSIGN(const auto up_ports,
                       pins_test::GetUpInterfacesOverGnmi(*sut_gnmi_stub));
  if (up_ports.empty()) {
    GTEST_SKIP() << "The test cannot be performed because not enough ports "
                 << "are up. Requires at least 1. "
                 << "Actual: " << up_ports.size();
  }
  absl::BitGen gen;
  const int random_member_index =
      absl::Uniform<int>(absl::IntervalClosedOpen, gen, 0, up_ports.size());
  const std::string& sut_intf_to_check = up_ports[random_member_index];
  LOG(INFO) << "Size of up port list: " << up_ports.size()
            << " Selected index: " << random_member_index
            << " Selected interface: " << sut_intf_to_check;
  std::string control_intf_to_check;
  auto sut_interface_info = generic_testbed->GetSutInterfaceInfo();
  auto it = sut_interface_info.find(sut_intf_to_check);
  ASSERT_NE(it, sut_interface_info.end());
  control_intf_to_check = {it->second.peer_interface_name};

  LOG(INFO) << "Control interface to check: " << control_intf_to_check;
  LOG(INFO) << "Sut interface to check: " << sut_intf_to_check;

  ASSERT_OK(control_device.ValidatePortsUp({control_intf_to_check}));
  ASSERT_THAT(
      GetInterfaceOperStatusOverGnmi(*sut_gnmi_stub.get(), sut_intf_to_check),
      gutil::IsOkAndHolds(OperStatus::kUp));
  ASSERT_OK(NsfReboot(generic_testbed.get()));
  EXPECT_OK(WaitForSwitchState(sut, SwitchState::kDown, absl::Seconds(90),
                               ssh_client));
  EXPECT_OK(control_device.SetAdminLinkState({control_intf_to_check},
                                             thinkit::LinkState::kDown));
  absl::Status reboot_status =
      WaitForNsfReboot(generic_testbed.get(), ssh_client,
                       /*image_config_param=*/nullptr,
                       /*check_interfaces_up =*/false);
  if (!reboot_status.ok()) {
    // Cold reboot the testbed as the failed NSF reboot could leave the testbed
    // in unhealthy state
    LOG(INFO) << "NSF reboot failed. " << reboot_status.message()
              << "Cold rebooting the switch.";
    EXPECT_OK(Reboot(RebootMethod::COLD, sut, generic_testbed->Environment()));
    EXPECT_OK(WaitForReboot(generic_testbed.get(), ssh_client, false));
    FAIL() << "Failure in NSF reboot.";
  }

  EXPECT_THAT(control_device.GetUpLinks({control_intf_to_check}),
              gutil::IsOkAndHolds(IsEmpty()));
  EXPECT_THAT(
      GetInterfaceOperStatusOverGnmi(*sut_gnmi_stub.get(), sut_intf_to_check),
      gutil::IsOkAndHolds(OperStatus::kDown));
  // Restore the interface state
  EXPECT_OK(control_device.SetAdminLinkState({control_intf_to_check},
                                             thinkit::LinkState::kUp));
  absl::SleepFor(absl::Seconds(10));
  ASSERT_OK(control_device.ValidatePortsUp({control_intf_to_check}));
  EXPECT_THAT(
      GetInterfaceOperStatusOverGnmi(*sut_gnmi_stub.get(), sut_intf_to_check),
      gutil::IsOkAndHolds(OperStatus::kUp));
}

}  // namespace pins_test
