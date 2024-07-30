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

#include "lib/validator/common_backend.h"

#include "lib/validator/validator_lib.h"

namespace pins_test {

absl::Status CommonBackend::IsPingable(absl::string_view chassis,
                                       absl::Duration timeout) {
  return pins_test::Pingable(chassis, timeout);
}

// The switch is SSHable if running the command "echo foo" returns "foo" in
// stdout with no errors.
absl::Status CommonBackend::IsSSHable(absl::string_view chassis,
                                      absl::Duration timeout) {
  return pins_test::SSHable(chassis, *ssh_client_, timeout);
}

}  // namespace pins_test
