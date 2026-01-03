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

#ifndef PINS_LIB_SSH_SSH_WRAPPER_CLIENT_H_
#define PINS_LIB_SSH_SSH_WRAPPER_CLIENT_H_

#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "lib/ssh/linux_ssh_helper.h"
#include "thinkit/ssh_client.h"

namespace thinkit {

// SSH wrapper client is a wrapper class of LinuxSshHelper that provides APIs
// for common operations on the switches running on different operation systems.
class SshWrapperClient : public LinuxSshHelper {
 public:
  explicit SshWrapperClient(
      absl::flat_hash_map<std::string, std::unique_ptr<thinkit::LinuxSshHelper>>
          linux_ssh_helper_per_sut)
      : linux_ssh_helper_per_sut_(std::move(linux_ssh_helper_per_sut)) {}

  // Reboots the switch.
  absl::StatusOr<std::string> Reboot(absl::string_view sut,
                                     thinkit::SSHClient* ssh_client,
                                     absl::Duration timeout) override;

  // Power cycles the switch.
  absl::StatusOr<std::string> PowerCycle(absl::string_view sut,
                                         thinkit::SSHClient* ssh_client,
                                         absl::Duration timeout) override;

  // Sets the timezone to PST on the switch.
  absl::StatusOr<std::string> SetTimezoneToPst(absl::string_view sut,
                                               thinkit::SSHClient* ssh_client,
                                               absl::Duration timeout) override;

  // Gets the PINs version on the switch.
  absl::StatusOr<std::string> GetpinsVersion(absl::string_view sut,
                                              thinkit::SSHClient* ssh_client,
                                              absl::Duration timeout) override;

  // Returns file name of the debug artifact tarball.
  absl::StatusOr<std::string> GetDebugArtifactFileName(
      absl::string_view sut, SSHClient* ssh_client,
      absl::Duration timeout) override;

  // Clears the PINs logs on the switch.
  absl::Status ClearpinsLogs(absl::string_view sut, SSHClient* ssh_client,
                              absl::Duration timeout) override;

  // Returns list of PINs logs file names and their contents.
  absl::StatusOr<std::vector<GetFileResult>> SavepinsLog(
      absl::string_view sut, SSHClient* ssh_client,
      absl::Duration timeout) override;

  // Returns list of the PINs DB state file names and their contents.
  absl::StatusOr<std::vector<GetFileResult>> SavepinsDbState(
      absl::string_view sut, SSHClient* ssh_client,
      absl::Duration timeout) override;

  // Returns list of the PINs Redis record file names and their contents.
  absl::StatusOr<std::vector<GetFileResult>> SavepinsRedisRecord(
      absl::string_view sut, SSHClient* ssh_client,
      absl::Duration timeout) override;

  // Translates the logical docker enum to the switch-specific string name.
  absl::StatusOr<std::string> GetContainerName(
      absl::string_view chassis_name, thinkit::Container docker) override;

  // Executes a command inside a docker on the switch.
  absl::StatusOr<std::string> ExecuteCommandInContainer(
      absl::string_view chassis_name, thinkit::SSHClient* ssh_client,
      thinkit::Container docker, absl::string_view command,
      absl::Duration timeout) override;

 private:
  // Returns a LinuxSshHelper instance for the given SUT.
  absl::StatusOr<LinuxSshHelper*> GetSshHelper(absl::string_view sut);

  // Map of SUT name to LinuxSshHelper instance.
  absl::flat_hash_map<std::string, std::unique_ptr<LinuxSshHelper>>
      linux_ssh_helper_per_sut_;
};

}  // namespace thinkit

#endif  // PINS_LIB_SSH_SSH_WRAPPER_CLIENT_H_
