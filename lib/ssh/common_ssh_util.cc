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
#include <vector>

#include "absl/log/log.h"
#include "absl/status/statusor.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "lib/ssh/linux_ssh_helper.h"
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

absl::StatusOr<std::vector<thinkit::GetFileResult>> GetFileResults(
    std::string_view sut, thinkit::SSHClient* ssh_client,
    absl::Span<const GetFileOption> get_file_options, absl::Duration timeout) {
  std::vector<thinkit::GetFileResult> get_file_results;
  for (const auto& get_file_option : get_file_options) {
    absl::StatusOr<std::string> output =
        ssh_client->RunCommand(sut, get_file_option.read_file_command, timeout);
    if (!output.ok()) {
      LOG(WARNING) << "Failed to get " << get_file_option.file_name << ": "
                   << output.status();
      continue;
    }
    get_file_results.push_back(thinkit::GetFileResult{
        .file_name = get_file_option.file_name, .file_content = *output});
  }
  return get_file_results;
}

}  // namespace pins_test
