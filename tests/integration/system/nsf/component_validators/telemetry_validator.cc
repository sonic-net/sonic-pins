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

#include "tests/integration/system/nsf/component_validators/telemetry_validator.h"

#include <string>

#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "grpcpp/support/status.h"
#include "tests/integration/system/nsf/interfaces/testbed.h"
#include "tests/integration/system/nsf/util.h"
#include "thinkit/ssh_client.h"
#include "thinkit/switch.h"

namespace pins_test {
namespace {

absl::Status ValidateTelemetryWarmboot(const Testbed &testbed,
                                       thinkit::SSHClient &ssh_client) {
  return absl::OkStatus();
}
}  // namespace

absl::Status TelemetryValidator::OnNsfReboot(absl::string_view version,
                                             const Testbed &testbed,
                                             thinkit::SSHClient &ssh_client) {
  return ValidateTelemetryWarmboot(testbed, ssh_client);
}

}  // namespace pins_test
