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

#include "absl/status/statusor.h"
#include "absl/time/time.h"
#include "thinkit/ssh_client.h"

namespace pins_test {

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

}  // namespace pins_test

#endif  // PINS_LIB_SSH_COMMON_SSH_UTIL_H_
