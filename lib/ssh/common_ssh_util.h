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

#ifndef PINS_LIB_SSH_COMMON_SSH_UTIL_H_
#define PINS_LIB_SSH_COMMON_SSH_UTIL_H_

#include <string>
#include <string_view>
#include <vector>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "lib/ssh/linux_ssh_helper.h"
#include "thinkit/ssh_client.h"

namespace pins_test {

// Represents options for retrieving a file from a switch.
//
// Members:
//   read_file_command: The command-line command used to read the content.
//   file_name: The desired name for the file when saved.
struct GetFileOption {
  std::string read_file_command;
  std::string file_name;
};

inline constexpr absl::Duration kSshTimeout = absl::Seconds(20);

absl::StatusOr<std::string> Reboot(thinkit::SSHClient* ssh_client,
                                   std::string_view sut,
                                   absl::Duration timeout = kSshTimeout);

absl::StatusOr<std::string> PowerCycle(thinkit::SSHClient* ssh_client,
                                       std::string_view sut,
                                       absl::Duration timeout = kSshTimeout);

absl::StatusOr<std::string> SetTimezoneToPst(
    thinkit::SSHClient* ssh_client, std::string_view sut,
    absl::Duration timeout = kSshTimeout);

absl::StatusOr<std::vector<thinkit::GetFileResult>> GetFileResults(
    std::string_view sut, thinkit::SSHClient* ssh_client,
    absl::Span<const GetFileOption> get_file_options, absl::Duration timeout);

absl::Span<const GetFileOption> GetSavepinsDbStateFileOptions(
    absl::string_view container_cmd_prefix);

// Returns the file options for saving the PINS Redis records.
// The `redis_dump_cmd_template` is expected to be a string with a single
// substitution point for the Redis record name. The redis record file is
// usually found at `/var/log/swss/<redis_record_name>`.
absl::Span<const GetFileOption> GetSavepinsRedisRecordFileOptions(
    absl::string_view redis_dump_cmd_template);

}  // namespace pins_test

#endif  // PINS_LIB_SSH_COMMON_SSH_UTIL_H_
