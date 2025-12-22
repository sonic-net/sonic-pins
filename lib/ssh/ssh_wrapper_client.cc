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

#include "lib/ssh/ssh_wrapper_client.h"

#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "gutil/gutil/status.h"
#include "lib/ssh/linux_ssh_helper.h"
#include "thinkit/ssh_client.h"

namespace thinkit {

absl::StatusOr<LinuxSshHelper*> SshWrapperClient::GetSshHelper(
    absl::string_view sut) {
  auto it = linux_ssh_helper_per_sut_.find(sut);
  if (it == linux_ssh_helper_per_sut_.end()) {
    return absl::NotFoundError(
        absl::StrCat("No SSH client found for SUT: ", sut));
  }
  return it->second.get();
}

absl::StatusOr<std::string> SshWrapperClient::Reboot(
    absl::string_view sut, thinkit::SSHClient* ssh_client,
    absl::Duration timeout) {
  ASSIGN_OR_RETURN(auto* ssh_helper, SshWrapperClient::GetSshHelper(sut));
  return ssh_helper->Reboot(sut, ssh_client, timeout);
}

absl::StatusOr<std::string> SshWrapperClient::PowerCycle(
    absl::string_view sut, thinkit::SSHClient* ssh_client,
    absl::Duration timeout) {
  ASSIGN_OR_RETURN(auto* ssh_helper, SshWrapperClient::GetSshHelper(sut));
  return ssh_helper->PowerCycle(sut, ssh_client, timeout);
}

absl::StatusOr<std::string> SshWrapperClient::SetTimezoneToPst(
    absl::string_view sut, thinkit::SSHClient* ssh_client,
    absl::Duration timeout) {
  ASSIGN_OR_RETURN(auto* ssh_helper, SshWrapperClient::GetSshHelper(sut));
  return ssh_helper->SetTimezoneToPst(sut, ssh_client, timeout);
}

absl::StatusOr<std::string> SshWrapperClient::GetpinsVersion(
    absl::string_view sut, thinkit::SSHClient* ssh_client,
    absl::Duration timeout) {
  ASSIGN_OR_RETURN(auto* ssh_helper, SshWrapperClient::GetSshHelper(sut));
  return ssh_helper->GetpinsVersion(sut, ssh_client, timeout);
}

absl::StatusOr<std::string> SshWrapperClient::GetDebugArtifactFileName(
    absl::string_view sut, SSHClient* ssh_client, absl::Duration timeout) {
  ASSIGN_OR_RETURN(auto* ssh_helper, SshWrapperClient::GetSshHelper(sut));
  return ssh_helper->GetDebugArtifactFileName(sut, ssh_client, timeout);
}

absl::Status SshWrapperClient::ClearpinsLogs(absl::string_view sut,
                                              SSHClient* ssh_client,
                                              absl::Duration timeout) {
  ASSIGN_OR_RETURN(auto* ssh_helper, SshWrapperClient::GetSshHelper(sut));
  return ssh_helper->ClearpinsLogs(sut, ssh_client, timeout);
}

absl::StatusOr<std::vector<GetFileResult>> SshWrapperClient::SavepinsLog(
    absl::string_view sut, SSHClient* ssh_client, absl::Duration timeout) {
  ASSIGN_OR_RETURN(auto* ssh_helper, SshWrapperClient::GetSshHelper(sut));
  return ssh_helper->SavepinsLog(sut, ssh_client, timeout);
}

absl::StatusOr<std::vector<GetFileResult>> SshWrapperClient::SavepinsDbState(
    absl::string_view sut, SSHClient* ssh_client, absl::Duration timeout) {
  ASSIGN_OR_RETURN(auto* ssh_helper, SshWrapperClient::GetSshHelper(sut));
  return ssh_helper->SavepinsDbState(sut, ssh_client, timeout);
}

absl::StatusOr<std::vector<GetFileResult>>
SshWrapperClient::SavepinsRedisRecord(absl::string_view sut,
                                       SSHClient* ssh_client,
                                       absl::Duration timeout) {
  ASSIGN_OR_RETURN(auto* ssh_helper, SshWrapperClient::GetSshHelper(sut));
  return ssh_helper->SavepinsRedisRecord(sut, ssh_client, timeout);
}

absl::StatusOr<std::string> SshWrapperClient::GetContainerName(
    absl::string_view chassis_name, thinkit::Container container) {
  ASSIGN_OR_RETURN(auto* ssh_helper,
                   SshWrapperClient::GetSshHelper(chassis_name));
  return ssh_helper->GetContainerName(chassis_name, container);
}

absl::StatusOr<std::string> SshWrapperClient::ExecuteCommandInContainer(
    absl::string_view chassis_name, thinkit::SSHClient* ssh_client,
    thinkit::Container container_name, absl::string_view command,
    absl::Duration timeout) {
  ASSIGN_OR_RETURN(auto* ssh_helper,
                   SshWrapperClient::GetSshHelper(chassis_name));
  return ssh_helper->ExecuteCommandInContainer(
      chassis_name, ssh_client, container_name, command, timeout);
}
}  // namespace thinkit

