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

#include "absl/status/status.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/substitute.h"
#include "gutil/status.h"

namespace pins_test {

absl::Status CommonBackend::IsPingable(absl::string_view chassis,
                                       absl::Duration timeout) {
  constexpr char kPingCommand[] = R"(fping -t $0 $1)";
  FILE* in;
  char buff[1024];
  std::string pingCommand =
      absl::Substitute(kPingCommand, absl::ToInt64Seconds(timeout), chassis);
  if (!(in = popen(pingCommand.c_str(), "r"))) {
    return absl::UnknownError(
        absl::StrCat("Failed to run command: ", pingCommand));
  }
  std::string response;
  while (fgets(buff, sizeof(buff), in) != nullptr) {
    absl::StrAppend(&response, buff);
  }
  pclose(in);

  if (!absl::StrContains(response, "alive")) {
    return absl::UnavailableError(
        absl::StrCat("Switch ", chassis,
                     " is not reachable. Unexpected result: ", response));
  }
  return absl::OkStatus();
}

// The switch is SSHable if running the command "echo foo" returns "foo" in
// stdout with no errors.
absl::Status CommonBackend::IsSSHable(absl::string_view chassis,
                                      absl::Duration timeout) {
  ASSIGN_OR_RETURN(std::string response,
                   ssh_client_->RunCommand(chassis, "echo foo", timeout));

  if (response != "foo\n") {
    return absl::UnavailableError(absl::StrCat(
        "Switch ", chassis, " is not SSHable. Unexpected result: ", response));
  }

  return absl::OkStatus();
}

}  // namespace pins_test
