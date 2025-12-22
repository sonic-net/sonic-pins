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

#include "lib/ssh/common_ssh_util.h"

#include <string>
#include <string_view>

#include "absl/status/statusor.h"
#include "absl/time/time.h"
#include "thinkit/ssh_client.h"

namespace pins_test {
namespace {

constexpr std::string_view kRebootCommand = "reboot";
constexpr std::string_view kPowerOffCommand = "/sbin/poweroff";
constexpr std::string_view kSetTimezoneCommand =
    "sudo timedatectl set-timezone America/Los_Angeles";

}  // namespace

absl::StatusOr<std::string> Reboot(thinkit::SSHClient* ssh_client,
                                   std::string_view sut,
                                   absl::Duration timeout) {
  return ssh_client->RunCommand(sut, kRebootCommand, timeout);
}

absl::StatusOr<std::string> PowerCycle(thinkit::SSHClient* ssh_client,
                                       std::string_view sut,
                                       absl::Duration timeout) {
  return ssh_client->RunCommand(sut, kPowerOffCommand, timeout);
}

absl::StatusOr<std::string> SetTimezoneToPst(thinkit::SSHClient* ssh_client,
                                             std::string_view sut,
                                             absl::Duration timeout) {
  return ssh_client->RunCommand(sut, kSetTimezoneCommand, timeout);
}

}  // namespace pins_test
