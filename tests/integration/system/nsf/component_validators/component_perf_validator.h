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

#ifndef PINS_TESTS_INTEGRATION_SYSTEM_NSF_COMPONENT_VALIDATORS_COMPONENT_PERF_VALIDATOR_H_
#define PINS_TESTS_INTEGRATION_SYSTEM_NSF_COMPONENT_VALIDATORS_COMPONENT_PERF_VALIDATOR_H_

#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "tests/integration/system/nsf/interfaces/component_validator.h"
#include "tests/integration/system/nsf/interfaces/testbed.h"
#include "thinkit/ssh_client.h"

namespace pins_test {

class ComponentPerfValidator : public ComponentValidator {
  absl::Status OnImageCopy(absl::string_view version, const Testbed& testbed,
                           thinkit::SSHClient& ssh_client) override;
  absl::Status OnNsfReboot(absl::string_view version, const Testbed& testbed,
                           thinkit::SSHClient& ssh_client) override;

 private:
  absl::Status FetchPreWarmRebootRegistrationInformation(thinkit::Switch& sut);
  absl::Status ValidateComponentWarmbootPerformance(thinkit::Switch& sut);

  absl::flat_hash_set<std::string> freeze_apps_;
  absl::flat_hash_set<std::string> checkpoint_apps_;
};

}  // namespace pins_test

#endif  // PINS_TESTS_INTEGRATION_SYSTEM_NSF_COMPONENT_VALIDATORS_COMPONENT_PERF_VALIDATOR_H_
