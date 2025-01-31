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

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/types/span.h"
#include "p4/config/v1/p4info.pb.h"
#include "tests/integration/system/nsf/interfaces/component_validator.h"
#include "tests/integration/system/nsf/interfaces/testbed.h"
#include "thinkit/ssh_client.h"
#include "thinkit/switch.h"

namespace pins_test {

void SetupTestbed(TestbedInterface& testbed_interface);

void TearDownTestbed(TestbedInterface& testbed_interface);

absl::StatusOr<Testbed> GetTestbed(TestbedInterface& testbed_interface);

thinkit::Switch& GetSut(Testbed& testbed);

// Performs image copy on the inactive side using gNOI.
// Note: This doesn't involve a reboot.
absl::Status ImageCopy(const std::string& image_label, Testbed& testbed,
                       thinkit::SSHClient& ssh_client);

absl::Status InstallRebootPushConfig(const std::string& image_label,
                                     const std::string& gnmi_config,
                                     Testbed& testbed,
                                     thinkit::SSHClient& ssh_client);

// Validates P4, gNMI, SSH connections and port status along with validating the
// Stack version of the SUT.
absl::Status ValidateSutState(absl::string_view version, Testbed& testbed,
                              thinkit::SSHClient& ssh_client);

absl::Status ValidateComponents(
    absl::Status (ComponentValidator::*validate)(absl::string_view, Testbed&),
    absl::Span<const std::unique_ptr<ComponentValidator>> validators,
    absl::string_view version, Testbed& testbed);

// Performs NSF Reboot on the SUT in the given testbed.
absl::Status NsfReboot(Testbed& testbed);

absl::Status WaitForReboot(Testbed& testbed, thinkit::SSHClient& ssh_client);

absl::Status PushConfig(const std::string& gnmi_config, Testbed& testbed,
                        thinkit::SSHClient& ssh_client);

p4::v1::ReadResponse TakeP4FlowSnapshot();

absl::Status CompareP4FlowSnapshots(const p4::v1::ReadResponse& a,
                                    const p4::v1::ReadResponse& b);

absl::Status CaptureDbState();

absl::Status ValidateDbState();

}  // namespace pins_test

#endif  // PINS_TESTS_INTEGRATION_SYSTEM_NSF_UTIL_H_
