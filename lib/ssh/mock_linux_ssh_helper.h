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

#ifndef PINS_LIB_SSH_MOCK_LINUX_SSH_HELPER_H_
#define PINS_LIB_SSH_MOCK_LINUX_SSH_HELPER_H_

#include <string>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "lib/ssh/linux_ssh_helper.h"
#include "thinkit/ssh_client.h"

namespace thinkit {

class MockLinuxSshHelper : public LinuxSshHelper {
 public:
  MOCK_METHOD(absl::StatusOr<std::string>, Reboot,
              (absl::string_view sut, SSHClient* ssh_client,
               absl::Duration timeout),
              (override));
  MOCK_METHOD(absl::StatusOr<std::string>, PowerCycle,
              (absl::string_view sut, SSHClient* ssh_client,
               absl::Duration timeout),
              (override));
  MOCK_METHOD(absl::StatusOr<std::string>, SetTimezoneToPst,
              (absl::string_view sut, SSHClient* ssh_client,
               absl::Duration timeout),
              (override));
};

}  // namespace thinkit

#endif  // PINS_LIB_SSH_MOCK_LINUX_SSH_HELPER_H_
