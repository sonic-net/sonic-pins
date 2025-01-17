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
#include "absl/strings/string_view.h"
#include "absl/types/span.h"
#include "p4/config/v1/p4info.pb.h"
#include "tests/integration/system/nsf/interfaces/component_validator.h"
#include "thinkit/generic_testbed.h"

namespace pins_test {

absl::Status InstallRebootPushConfig(absl::string_view version);

// Validates P4, gNMI, SSH connections and port status along with validating the
// Stack version.
absl::Status ValidateSwitchState(absl::string_view version);

absl::Status ValidateComponents(
    absl::Status (ComponentValidator::*validate)(absl::string_view,
                                                 thinkit::GenericTestbed&),
    absl::Span<const std::unique_ptr<ComponentValidator>> validators,
    absl::string_view version, thinkit::GenericTestbed& testbed);

absl::Status Upgrade(absl::string_view version);

absl::Status NsfReboot(absl::string_view version);

absl::Status PushConfig(absl::string_view version);

p4::v1::ReadResponse TakeP4FlowSnapshot();

absl::Status CompareP4FlowSnapshots(const p4::v1::ReadResponse& a,
                                    const p4::v1::ReadResponse& b);

absl::Status CaptureDbState();

absl::Status ValidateDbState();

}  // namespace pins_test

#endif  // PINS_TESTS_INTEGRATION_SYSTEM_NSF_UTIL_H_
