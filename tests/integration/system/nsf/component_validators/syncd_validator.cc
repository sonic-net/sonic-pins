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
#include "tests/integration/system/nsf/component_validators/syncd_validator.h"

#include <string>

#include "absl/container/flat_hash_set.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "tests/integration/system/nsf/interfaces/testbed.h"
#include "tests/integration/system/nsf/util.h"
#include "thinkit/ssh_client.h"
#include "thinkit/switch.h"

namespace pins_test {
namespace {

absl::Status ValidateSyncdWarmboot(
    thinkit::Switch& sut, absl::flat_hash_set<absl::string_view>& allowlist) {
  return absl::OkStatus();
}

absl::Status PrepareAllowListInSyncdInit(
    thinkit::Switch& sut, absl::flat_hash_set<absl::string_view>& allowlist) {
  return absl::OkStatus();
}

}  // namespace

absl::Status SyncdValidator::OnNsfReboot(absl::string_view version,
                                         const Testbed &testbed,
                                         thinkit::SSHClient &ssh_client) {
  return ValidateSyncdWarmboot(GetSut(testbed), allowlist_);
}

absl::Status SyncdValidator::OnImageCopy(absl::string_view version,
                                         const Testbed& testbed,
                                         thinkit::SSHClient& ssh_client) {
  return PrepareAllowListInSyncdInit(GetSut(testbed), allowlist_);
}

}  // namespace pins_test
