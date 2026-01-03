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

#ifndef PINS_LIB_SSH_LINUX_SSH_HELPER_H_
#define PINS_LIB_SSH_LINUX_SSH_HELPER_H_

#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "thinkit/ssh_client.h"

namespace thinkit {

// Represents the result of retrieving a file from a switch.
//
// Members:
//   file_name: The name of the file to save.
//   file_content: The content of the retrieved file.
struct GetFileResult {
  std::string file_name;
  std::string file_content;
};

enum class Container {
  kDatabase,
  kSystem,
  kGnmi,
  kP4rt,
  kPmon,
  kSwss,
  kSflow,
  kSyncd,
  kTeamd
};

enum class CertFile {
  kSshCaBundle,
  kSshServerKey,
  kSshServerCert,
  kGrpcAuthzPolicy,
  kGnmiAuthzPolicy,
  kGrpcAuthnPolicy,
  kCrlFile,
  kCrlFlushFile,
  kGrpcVersionFile,
  kGnoiCaBundle,
  kGnoiServerKey,
  kGnoiServerCert,
  kShadowFile,
  kSshAuthKeys,
  kSshAuthUsers,
  kDefaultSshCaPubKeyPath,
  kMountedConfigSshCaPubKeyPath,
};

// LinuxSshHelper is an interface for common operations on the switches
// regardless of the switch OS.
class LinuxSshHelper {
 public:
  virtual ~LinuxSshHelper() = default;

  // Reboot the switch and return the output.
  virtual absl::StatusOr<std::string> Reboot(absl::string_view sut,
                                             SSHClient* ssh_client,
                                             absl::Duration timeout) = 0;

  // Power cycle the switch and return the output.
  virtual absl::StatusOr<std::string> PowerCycle(absl::string_view sut,
                                                 SSHClient* ssh_client,
                                                 absl::Duration timeout) = 0;

  // Set the timezone to PST and return the output.
  virtual absl::StatusOr<std::string> SetTimezoneToPst(
      absl::string_view sut, SSHClient* ssh_client, absl::Duration timeout) = 0;

  // Get the PINs version and return the output.
  virtual absl::StatusOr<std::string> GetpinsVersion(
      absl::string_view sut, SSHClient* ssh_client, absl::Duration timeout) = 0;

  // Returns file name of the debug artifact tarball.
  virtual absl::StatusOr<std::string> GetDebugArtifactFileName(
      absl::string_view sut, SSHClient* ssh_client, absl::Duration timeout) = 0;

  // Clears the PINs logs on the switch.
  virtual absl::Status ClearpinsLogs(absl::string_view sut,
                                      SSHClient* ssh_client,
                                      absl::Duration timeout) = 0;
  // Removes the config db on the switch.
  virtual absl::Status RemoveConfigDb(absl::string_view sut,
                                      SSHClient* ssh_client,
                                      absl::Duration timeout) = 0;

  // Returns list of PINs logs file names and their contents.
  virtual absl::StatusOr<std::vector<GetFileResult>> SavepinsLog(
      absl::string_view sut, SSHClient* ssh_client, absl::Duration timeout) = 0;

  // Returns list of the PINs DB state file names and their contents.
  virtual absl::StatusOr<std::vector<GetFileResult>> SavepinsDbState(
      absl::string_view sut, SSHClient* ssh_client, absl::Duration timeout) = 0;

  // Returns list of the PINs Redis record file names and their contents.
  virtual absl::StatusOr<std::vector<GetFileResult>> SavepinsRedisRecord(
      absl::string_view sut, SSHClient* ssh_client, absl::Duration timeout) = 0;

  // Translates the logical container enum to the switch-specific string name.
  virtual absl::StatusOr<std::string> GetContainerName(
      absl::string_view chassis_name, thinkit::Container container) = 0;

  // Executes a command inside a container on the switch.
  virtual absl::StatusOr<std::string> ExecuteCommandInContainer(
      absl::string_view chassis_name, thinkit::SSHClient* ssh_client,
      thinkit::Container container, absl::string_view command,
      absl::Duration timeout) = 0;

  // Fetches the cert file name from the switch.
  virtual absl::StatusOr<std::string_view> FetchCertFileName(
      absl::string_view chassis_name, thinkit::CertFile cert_file) = 0;

  // Checks and restore Boot install on the switch.
  virtual absl::Status CheckAndRestoreBootinstall(
      absl::string_view chassis_name, thinkit::SSHClient* ssh_client,
      absl::Duration timeout) = 0;

  // Checks the status of all containers and returns an error if not all of them
  // are running.
  virtual absl::Status CheckContainersUp(absl::string_view chassis_name,
                                         thinkit::SSHClient& ssh_client) = 0;
};

}  // namespace thinkit

#endif  // PINS_LIB_SSH_LINUX_SSH_HELPER_H_
