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

#ifndef PINS_TESTS_INTEGRATION_SYSTEM_NSF_UTIL_H_
#define PINS_TESTS_INTEGRATION_SYSTEM_NSF_UTIL_H_

#include <memory>
#include <string>
#include <vector>

#include "absl/base/nullability.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "tests/integration/system/nsf/interfaces/component_validator.h"
#include "tests/integration/system/nsf/interfaces/test_params.h"
#include "tests/integration/system/nsf/interfaces/testbed.h"
#include "thinkit/ssh_client.h"
#include "thinkit/switch.h"
#include "thinkit/test_environment.h"

namespace pins_test {

// State of the switch.
enum class SwitchState { kUp, kDown, kReady, kReadyWithoutInterfacesUp };

void SetupTestbed(TestbedInterface& testbed_interface);

void TearDownTestbed(TestbedInterface& testbed_interface);

absl::StatusOr<Testbed> GetTestbed(TestbedInterface& testbed_interface);

thinkit::Switch& GetSut(Testbed& testbed);

thinkit::TestEnvironment &GetTestEnvironment(Testbed &testbed);

// Returns the list of connected interfaces for the SUT.
std::vector<std::string> GetConnectedInterfacesForSut(Testbed& testbed);

// Runs validations that validate the switch to be ready. Does the switch
// respond over: ping, SSH, P4, gNMI, gNOI.
absl::Status RunReadyValidations(thinkit::Switch& thinkit_switch,
                                 thinkit::SSHClient& ssh_client,
                                 absl::Span<const std::string> interfaces = {},
                                 bool check_interfaces_state = true,
                                 bool with_healthz = true);

// Waits for a target switch to be up or down based on the state provided.
absl::Status WaitForSwitchState(thinkit::Switch& thinkit_switch,
                                SwitchState state, absl::Duration timeout,
                                thinkit::SSHClient& ssh_client,
                                absl::Span<const std::string> interfaces = {});

// Reboot the SUT using the given reboot `method`.
absl::Status Reboot(gnoi::system::RebootMethod method, Testbed& testbed);

// Performs image copy on the inactive side using gNOI, and returns the upgraded
// image version on success.
// Note: This doesn't involve a reboot.
absl::StatusOr<std::string> ImageCopy(const std::string& image_label,
                                      Testbed& testbed,
                                      thinkit::SSHClient& ssh_client);

absl::Status
InstallRebootPushConfig(Testbed &testbed, thinkit::SSHClient &ssh_client,
                        const ImageConfigParams &image_config_param);

// Validates P4, gNMI, SSH connections and port status of the SUT and Control
// Switch (if present) along with validating the stack version of the SUT.
// Also optionally validates the gNMI config convergence if an
// `image_config_param` is provided.
absl::Status ValidateTestbedState(
    Testbed &testbed, thinkit::SSHClient &ssh_client,
    absl::Nullable<const ImageConfigParams *> image_config_param = nullptr,
    bool check_interfaces_up = true);

absl::Status ValidateComponents(
    absl::Status (ComponentValidator::*validate)(absl::string_view, Testbed &,
                                                 thinkit::SSHClient &),
    absl::Span<const std::unique_ptr<ComponentValidator>> validators,
    absl::string_view version, Testbed &testbed,
    thinkit::SSHClient &ssh_client);

// Performs NSF Reboot on the SUT in the given testbed.
absl::Status NsfReboot(Testbed& testbed);

// Waits for the SUT to cold reboot. If `check_interfaces_up` is `true`, it
// additionally checks whether all the SUT interfaces are UP after turnup.
absl::Status WaitForReboot(Testbed& testbed, thinkit::SSHClient& ssh_client,
                           bool check_interfaces_up = true);

// Waits for the SUT to warm reboot. If `check_interfaces_up` is `true`, it
// additionally checks whether all the SUT interfaces are UP after turnup.
absl::Status WaitForNsfReboot(
    Testbed &testbed, thinkit::SSHClient &ssh_client,
    absl::Nullable<const ImageConfigParams *> image_config_param = nullptr,
    bool check_interfaces_up = true);

// Performs NSF Reboot and waits for the SUT to be ready.
absl::Status DoNsfRebootAndWaitForSwitchReady(
    Testbed &testbed, thinkit::SSHClient &ssh_client,
    absl::Nullable<const ImageConfigParams *> image_config_param = nullptr,
    bool check_interfaces_up = true);

absl::Status PushConfig(const ImageConfigParams& image_config_param,
                        Testbed& testbed, thinkit::SSHClient& ssh_client,
                        bool is_fresh_install = false);

absl::StatusOr<::p4::v1::ReadResponse> TakeP4FlowSnapshot(Testbed& testbed);

absl::Status CompareP4FlowSnapshots(::p4::v1::ReadResponse snapshot_1,
                                    ::p4::v1::ReadResponse snapshot_2);

absl::Status SaveP4FlowSnapshot(Testbed& testbed,
                                ::p4::v1::ReadResponse snapshot,
                                absl::string_view file_name);

// Stores the healthz debug artifacts of the SUT with the given `prefix` as:
// "{prefix}_healthz"
absl::Status StoreSutDebugArtifacts(absl::string_view prefix, Testbed& testbed);

}  // namespace pins_test

#endif  // PINS_TESTS_INTEGRATION_SYSTEM_NSF_UTIL_H_
