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

#include "absl/random/random.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"  
#include "lib/gnmi/gnmi_helper.h"
#include "tests/gnmi/util.h"
#include "tests/integration/system/nsf/interfaces/testbed.h"
#include "tests/integration/system/nsf/util.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/proto/generic_testbed.pb.h"
#include "thinkit/ssh_client.h"
#include "thinkit/switch.h"

namespace pins_test {

TEST_P(NsfDynamicStateUpdateTestFixture, NsfDynamicStateUpdateTest) {
  GetParam().mirror_testbed->ExpectLinkFlaps();
  // Get mirror testbed
  thinkit::MirrorTestbed& mirror_testbed =
      GetParam().mirror_testbed->GetMirrorTestbed();

  // Get control switch and SUT
  thinkit::Switch& sut = mirror_testbed.Sut();
  thinkit::Switch& control_switch = mirror_testbed.ControlSwitch();

  // Get pins_test testbed
  pins_test::Testbed testbed;
  testbed.emplace<thinkit::MirrorTestbed*>(&mirror_testbed);

  // Get ssh client and gnmi stub
  thinkit::SSHClient& ssh_client = *GetParam().ssh_client;
  ASSERT_OK_AND_ASSIGN(auto control_switch_gnmi_stub,
                       control_switch.CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());

  // The following section of code is to select a up port randomly
  ASSERT_OK_AND_ASSIGN(
      const auto up_ports,
      pins_test::GetUpInterfacesOverGnmi(*control_switch_gnmi_stub.get()));
  if (up_ports.empty()) {
    GTEST_SKIP() << "The test cannot be performed because not enough ports "
                 << "are up. Requires at least 1. "
                 << "Actual: " << up_ports.size();
  }
  absl::BitGen gen;
  const int random_member_index =
      absl::Uniform<int>(absl::IntervalClosedOpen, gen, 0, up_ports.size());
  std::string intf_to_check = up_ports[random_member_index];
  LOG(INFO) << "Size of up port list: " << up_ports.size()
            << " Selected index: " << random_member_index
            << " Selected interface: " << intf_to_check;

  // Start the test
  ASSERT_THAT(GetInterfaceOperStatusOverGnmi(*control_switch_gnmi_stub.get(),
                                             intf_to_check),
              gutil::IsOkAndHolds(OperStatus::kUp));
  ASSERT_THAT(
      GetInterfaceOperStatusOverGnmi(*sut_gnmi_stub.get(), intf_to_check),
      gutil::IsOkAndHolds(OperStatus::kUp));
  ASSERT_OK(NsfReboot(testbed));
  EXPECT_OK(WaitForSwitchState(sut, SwitchState::kDown, absl::Seconds(90),
                               ssh_client));
  EXPECT_OK(
      SetAdminStatus(control_switch_gnmi_stub.get(), intf_to_check, "DOWN"));
  if (!WaitForNsfReboot(testbed, ssh_client, /*image_config_param=*/nullptr,
                        /*check_interfaces_up =*/false)
           .ok()) {
    // Cold reboot the testbed as the failed NSF reboot could leave the testbed
    // in unhealthy state
    LOG(INFO) << "NSF reboot failed. Cold rebooting the switch.";
    EXPECT_OK(Reboot(gnoi::system::RebootMethod::COLD, testbed));
    EXPECT_OK(WaitForReboot(testbed, ssh_client, false));
    FAIL() << "Failure in NSF reboot.";
  }
  EXPECT_THAT(GetInterfaceOperStatusOverGnmi(*control_switch_gnmi_stub.get(),
                                             intf_to_check),
              gutil::IsOkAndHolds(OperStatus::kDown));
  EXPECT_THAT(
      GetInterfaceOperStatusOverGnmi(*sut_gnmi_stub.get(), intf_to_check),
      gutil::IsOkAndHolds(OperStatus::kDown));
  // Restore the interface state
  EXPECT_OK(
      SetAdminStatus(control_switch_gnmi_stub.get(), intf_to_check, "UP"));
  absl::SleepFor(absl::Seconds(10));
  EXPECT_THAT(GetInterfaceOperStatusOverGnmi(*control_switch_gnmi_stub.get(),
                                             intf_to_check),
              gutil::IsOkAndHolds(OperStatus::kUp));
  EXPECT_THAT(
      GetInterfaceOperStatusOverGnmi(*sut_gnmi_stub.get(), intf_to_check),
      gutil::IsOkAndHolds(OperStatus::kUp));
}
}  // namespace pins_test
