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

#include "tests/integration/system/nsf/util.h"

#include <functional>
#include <memory>

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "absl/types/span.h"
#include "gutil/status.h"  // NOLINT: Need to add gutil/status.h for using `RETURN_IF_ERROR` in upstream code.
#include "p4/config/v1/p4info.pb.h"
#include "tests/integration/system/nsf/interfaces/component_validator.h"
#include "thinkit/generic_testbed.h"

namespace pins_test {

using p4::v1::ReadResponse;

absl::Status InstallRebootPushConfig(absl::string_view version) {
  return absl::OkStatus();
}

absl::Status ValidateSwitchState(absl::string_view version) {
  return absl::OkStatus();
}

absl::Status ValidateComponents(
    absl::Status (ComponentValidator::*validate)(absl::string_view,
                                                 thinkit::GenericTestbed&),
    const absl::Span<const std::unique_ptr<ComponentValidator>> validators,
    absl::string_view version, thinkit::GenericTestbed& testbed) {
  for (const std::unique_ptr<ComponentValidator>& validator : validators) {
    RETURN_IF_ERROR((std::invoke(validate, validator, version, testbed)));
  }
  return absl::OkStatus();
}

absl::Status Upgrade(absl::string_view version) { return absl::OkStatus(); }

absl::Status NsfReboot(absl::string_view version) { return absl::OkStatus(); }

absl::Status PushConfig(absl::string_view version) { return absl::OkStatus(); }

ReadResponse TakeP4FlowSnapshot() { return ReadResponse(); }

absl::Status CompareP4FlowSnapshots(const ReadResponse& a,
                                    const ReadResponse& b) {
  return absl::OkStatus();
}

absl::Status CaptureDbState() { return absl::OkStatus(); }

absl::Status ValidateDbState() { return absl::OkStatus(); }

}  // namespace pins_test
