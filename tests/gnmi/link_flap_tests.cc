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

#include <memory>
#include <string>
#include <type_traits>

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "lib/gnmi/gnmi_helper.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "tests/gnmi/util.h"
#include "thinkit/control_device.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/proto/generic_testbed.pb.h"
#include "thinkit/switch.h"

namespace pins_test {
namespace {

using ::gutil::IsOkAndHolds;
using ::testing::Contains;

}  // namespace

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

  LOG(INFO) << "Get sut interface info.";
  absl::flat_hash_map<std::string, thinkit::InterfaceInfo> interface_info =
      generic_testbed->GetSutInterfaceInfo();
  std::string sut_interface;
  std::string peer_interface;
  for (const auto& [interface, info] : interface_info) {
    if (info.interface_modes.contains(thinkit::CONTROL_INTERFACE)) {
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
  LOG(INFO) << "Validate " << peer_interface << " state: DOWN.";
  EXPECT_THAT(generic_testbed->ControlDevice().GetUpLinks({peer_interface}),
              IsOkAndHolds(testing::IsEmpty()));

  // Sets admin-status Up through gNMI.
  LOG(INFO) << "Set sut " << sut_interface << " admin link state up.";
  EXPECT_OK(SetAdminStatus(gnmi_stub.get(), sut_interface, "UP"));
  LOG(INFO) << "Validate " << peer_interface << " state: UP.";
  EXPECT_THAT(generic_testbed->ControlDevice().GetUpLinks({peer_interface}),
              IsOkAndHolds(Contains(peer_interface)));

  // Flaps control switch port and checks that SUT’s gNMI reflects that.
  LOG(INFO) << "Set control switch " << peer_interface
            << " admin link state down.";
  EXPECT_OK(generic_testbed->ControlDevice().SetAdminLinkState(
      {peer_interface}, thinkit::LinkState::kDown));
  absl::SleepFor(absl::Seconds(15));
  // Checks oper-status through gNMI.
  LOG(INFO) << "Validate " << sut_interface << " state: DOWN.";
  EXPECT_THAT(GetInterfaceOperStatusOverGnmi(*gnmi_stub, sut_interface),
              IsOkAndHolds(OperStatus::kDown));
  LOG(INFO) << "Set control switch " << peer_interface
            << " admin link state up.";
  EXPECT_OK(generic_testbed->ControlDevice().SetAdminLinkState(
      {peer_interface}, thinkit::LinkState::kUp));
  absl::SleepFor(absl::Seconds(15));
  LOG(INFO) << "Validate " << sut_interface << " state: UP.";
  EXPECT_THAT(GetInterfaceOperStatusOverGnmi(*gnmi_stub, sut_interface),
              IsOkAndHolds(OperStatus::kUp));
}

}  // namespace pins_test
