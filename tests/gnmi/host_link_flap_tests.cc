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
#include <memory>
#include <string>

#include "absl/container/flat_hash_map.h"
#include "absl/log/log.h"
#include "absl/strings/str_format.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "lib/gnmi/gnmi_helper.h"
#include "tests/gnmi/link_flap_tests.h"
#include "tests/gnmi/util.h"
#include "thinkit/control_device.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/proto/generic_testbed.pb.h"
#include "thinkit/switch.h"

namespace pins_test {

using ::gutil::IsOkAndHolds;
using ::testing::Contains;
using ::testing::IsEmpty;

constexpr absl::Duration kFlapTimeout = absl::Minutes(2);

TEST_P(ExampleTestFixture, LinkFlapTest) {
  LOG(INFO) << "Get testbed requirements.";
  thinkit::TestRequirements requirements =
      gutil::ParseProtoOrDie<thinkit::TestRequirements>(
          R"pb(interface_requirements {
                 count: 1
                 interface_mode: CONTROL_INTERFACE
               })pb");
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<thinkit::GenericTestbed> generic_testbed,
                       GetTestbedWithRequirements(requirements));
  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, generic_testbed->Sut().CreateGnmiStub());

  LOG(INFO) << "Get SUT interface info.";
  absl::flat_hash_map<std::string, thinkit::InterfaceInfo> interface_info =
      generic_testbed->GetSutInterfaceInfo();
  std::string sut_interface;
  std::string peer_interface;
  int peer_device_index;
  for (const auto& [interface, info] : interface_info) {
    if (info.interface_modes.contains(thinkit::CONTROL_INTERFACE)) {
      // Find an operationally up link to flap.
      ASSERT_OK_AND_ASSIGN(
          pins_test::OperStatus oper_status,
          GetInterfaceOperStatusOverGnmi(*gnmi_stub, interface));
      if (oper_status == pins_test::OperStatus::kUp) {
        sut_interface = interface;
        peer_interface = info.peer_interface_name;
        peer_device_index = info.peer_device_index;
        break;
      }
      LOG(INFO) << absl::StrFormat("Ignoring %s since it is operationally DOWN",
                                   interface);
    }
  }
  ASSERT_THAT(sut_interface, Not(IsEmpty()));
  ASSERT_THAT(peer_interface, Not(IsEmpty()));
  LOG(INFO) << absl::StrFormat(
      "sut_interface: %s, peer_interface: %s, peer_device_index: %d",
      sut_interface, peer_interface, peer_device_index);

  LOG(INFO) << absl::StrFormat("Validate control device port %s is UP",
                               peer_interface);
  ASSERT_THAT(generic_testbed->ControlDevice(peer_device_index)
                  .GetUpLinks({peer_interface}),
              IsOkAndHolds(Contains(peer_interface)));

  // Flap SUT port through gNMI (admin state) and checks that the control
  // device detects it.
  // Set admin-status DOWN through gNMI.
  LOG(INFO) << absl::StrFormat("Set SUT port %s admin DOWN", sut_interface);
  EXPECT_OK(
      SetAdminStatus(gnmi_stub.get(), sut_interface, "DOWN", kFlapTimeout));
  LOG(INFO) << absl::StrFormat("Validate SUT port %s state: DOWN",
                               sut_interface);
  EXPECT_THAT(GetInterfaceOperStatusOverGnmi(*gnmi_stub, sut_interface),
              IsOkAndHolds(OperStatus::kDown));

  // Set admin-status UP through gNMI.
  LOG(INFO) << absl::StrFormat("Set SUT port %s admin UP", sut_interface);
  EXPECT_OK(SetAdminStatus(gnmi_stub.get(), sut_interface, "UP", kFlapTimeout));
  LOG(INFO) << absl::StrFormat("Validate control device port %s state: UP",
                               peer_interface);
  EXPECT_THAT(generic_testbed->ControlDevice(peer_device_index)
                  .GetUpLinks({peer_interface}),
              IsOkAndHolds(Contains(peer_interface)));
  LOG(INFO) << absl::StrFormat("Validate SUT port %s state: UP", sut_interface);
  EXPECT_THAT(GetInterfaceOperStatusOverGnmi(*gnmi_stub, sut_interface),
              IsOkAndHolds(OperStatus::kUp));
}

}  // namespace pins_test
