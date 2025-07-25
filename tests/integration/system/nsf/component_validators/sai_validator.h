// Copyright 2024 Google LLC
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

#ifndef PINS_TESTS_INTEGRATION_SYSTEM_NSF_COMPONENT_VALIDATORS_SAI_VALIDATOR_H_
#define PINS_TESTS_INTEGRATION_SYSTEM_NSF_COMPONENT_VALIDATORS_SAI_VALIDATOR_H_

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "glog/logging.h"
#include "tests/integration/system/nsf/interfaces/component_validator.h"
#include "tests/integration/system/nsf/interfaces/testbed.h"
#include "thinkit/ssh_client.h"

namespace pins_test {

// Dummy validators added as example of ComponentValidators implementation.
// Component owners need to have their own implementations and register to be
// used by the NSF Upgrade tests.
class SaiValidator : public ComponentValidator {
  absl::Status OnInit(absl::string_view version, Testbed &testbed,
                      thinkit::SSHClient &ssh_client) override {
    LOG(INFO) << "Sai Init";
    return absl::OkStatus();
  }
  absl::Status OnFlowCleanup(absl::string_view version, Testbed &testbed,
                             thinkit::SSHClient &ssh_client) override {
    LOG(INFO) << "Sai Flow Cleanup";
    return absl::OkStatus();
  }
};

}  // namespace pins_test

#endif  // PINS_TESTS_INTEGRATION_SYSTEM_NSF_COMPONENT_VALIDATORS_SAI_VALIDATOR_H_
