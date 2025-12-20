// Copyright (c) 2024, Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "tests/integration/system/control_device_reboot_test.h"

#include <string>
#include <thread>  // NOLINT
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/strings/substitute.h"
#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "thinkit/control_device.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/proto/generic_testbed.pb.h"

namespace pins_test {
namespace {

constexpr absl::Duration kTurnDownTimeout = absl::Seconds(210);  // 3.5 minutes
constexpr absl::Duration kTurnUpTimeout = absl::Minutes(20);

enum class ControlDeviceState { kUp, kDown };

absl::Status WaitForControlDevice(thinkit::ControlDevice& control_device,
                                  ControlDeviceState state,
                                  absl::Duration timeout) {
  std::string elapsed_time = "";
  std::string state_name = (state == ControlDeviceState::kUp) ? "kUp" : "kDown";
  absl::Status device_ready = absl::InternalError("Uninitialized");

  absl::Time start_time = absl::Now();
  while (absl::Now() - start_time < timeout) {
    device_ready = control_device.CheckUp();

    // For kDown state, control device is ready when it is no longer reachable.
    if (state == ControlDeviceState::kDown) {
      device_ready =
          device_ready.ok()
              ? absl::InternalError(
                    "Control device is reachable. Expected: unreachable.")
              : absl::OkStatus();
    }

    if (device_ready.ok()) {
      elapsed_time = absl::FormatDuration(absl::Now() - start_time);
      LOG(INFO) << absl::Substitute("Control device $0 state reached in $1.",
                                    state_name, elapsed_time);
      return absl::OkStatus();
    }
  }

  return absl::DeadlineExceededError(absl::Substitute(
      "Control device $0 state not reached after $1. Status: $2", state_name,
      absl::FormatDuration(timeout), device_ready.message()));
}

}  // namespace

// Reboots control device and validates that the link to the device comes up.
TEST_P(ControlDeviceRebootTestFixture, TestControlDeviceReboot) {
  LOG(INFO) << "Get testbed with at least one thinkit::CONTROL_INTERFACE.";
  thinkit::TestRequirements requirements =
      gutil::ParseProtoOrDie<thinkit::TestRequirements>(
          R"pb(interface_requirements {
                 count: 1
                 interface_mode: CONTROL_INTERFACE
               })pb");
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<thinkit::GenericTestbed> generic_testbed,
                       GetTestbedWithRequirements(requirements));

  // Connect to TestTracker for test status
  generic_testbed->Environment().SetTestCaseID(
      "3b8dc5fd-d5f9-4e8d-856f-9495c802d39f");

  LOG(INFO) << "Get all ports on control device connected to sut.";
  absl::flat_hash_map<std::string, thinkit::InterfaceInfo> interface_info =
      generic_testbed->GetSutInterfaceInfo();

  absl::flat_hash_map<int, std::vector<std::string>> peer_interfaces;
  for (const auto& [interface, info] : interface_info) {
    if (info.interface_modes.contains(thinkit::CONTROL_INTERFACE)) {
      LOG(INFO) << absl::StrFormat(
          "sut_interface: %s, peer_interface_name: %s, peer_device_index: %d",
          interface, info.peer_interface_name, info.peer_device_index);
      peer_interfaces[info.peer_device_index].push_back(
          info.peer_interface_name);
    }
  }

  std::vector<std::thread> threads;
  for (const auto& [index, interfaces] : peer_interfaces) {
    std::thread reboot_thread = std::thread([&, &index = index,
                                             &interfaces = interfaces]() {
      LOG(INFO) << absl::StrFormat(
          "(control device index: %d) Check that all ports are up", index);
      ASSERT_OK(
          generic_testbed->ControlDevice(index).ValidatePortsUp(interfaces));

      LOG(INFO) << absl::StrFormat(
          "(control device index: %d): Rebooting control device", index);
      ASSERT_OK(generic_testbed->ControlDevice(index).Reboot(
          thinkit::RebootType::kCold));

      ASSERT_OK(WaitForControlDevice(generic_testbed->ControlDevice(index),
                                     ControlDeviceState::kDown,
                                     kTurnDownTimeout))
          << "Control device " << index
          << " did not reach kDown state after reboot.";

      ASSERT_OK(WaitForControlDevice(generic_testbed->ControlDevice(index),
                                     ControlDeviceState::kUp, kTurnUpTimeout))
          << "Control device " << index
          << " did not reach kUp state after reboot.";

      LOG(INFO) << absl::StrFormat(
          "(control device index: %d): Check that all ports are up after "
          "reboot",
          index);
      ASSERT_OK(
          generic_testbed->ControlDevice(index).ValidatePortsUp(interfaces));
      LOG(INFO) << absl::StrFormat(
          "(control device index: %d): All ports are up after reboot", index);
    });
    threads.push_back(std::move(reboot_thread));
  }

  for (auto& t : threads) {
    t.join();
  }
}

}  // namespace pins_test
