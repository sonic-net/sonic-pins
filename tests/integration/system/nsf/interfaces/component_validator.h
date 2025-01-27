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

#ifndef PINS_TESTS_INTEGRATION_SYSTEM_NSF_INTERFACES_COMPONENT_VALIDATOR_H_
#define PINS_TESTS_INTEGRATION_SYSTEM_NSF_INTERFACES_COMPONENT_VALIDATOR_H_

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "tests/integration/system/nsf/interfaces/testbed.h"

namespace pins_test {

// Interface to provide a mechanism to implement component-level validations
// during NSF integration tests.
//
// The different methods of this interface are called *after* the corresponding
// operation is performed during the test.
//
// Eg. After every flow programming operation, the `OnFlowProgram` method is
// called.
//
// The given `version` is the image version of the software stack running on the
// SUT at the time the function is called.
//
// The given `testbed` can be used by the implementation to interact with the
// SUT, ControlDevice, TrafficClient, or the test environment.
//
// Typically an implementation of the `ComponentValidator` would grab and store
// some state which is specific to a particular component and/or validate it
// against such a previously stored component-specific state.
//
// Note that it can also be used for other kinds of validations that do not
// necessarily involve grabbing or validating state from the SUT.
//
// Eg. We can use these methods to track performance by calculating the time
// difference between function calls.
class ComponentValidator {
 public:
  virtual ~ComponentValidator() = default;

  // Called before starting every NSF test.
  virtual absl::Status OnInit(absl::string_view version, Testbed& testbed) {
    return absl::OkStatus();
  }

  // Called after programming flows on SUT.
  virtual absl::Status OnFlowProgram(absl::string_view version,
                                     Testbed& testbed) {
    return absl::OkStatus();
  }

  // Called after starting traffic from the Control Device or the Traffic
  // Generator in the testbed.
  virtual absl::Status OnStartTraffic(absl::string_view version,
                                      Testbed& testbed) {
    return absl::OkStatus();
  }

  // Called after an upgrade is performed on the SUT.
  virtual absl::Status OnUpgrade(absl::string_view version, Testbed& testbed) {
    return absl::OkStatus();
  }

  // Called after a successful NSF reboot of the SUT.
  virtual absl::Status OnNsfReboot(absl::string_view version,
                                   Testbed& testbed) {
    return absl::OkStatus();
  }

  // Called after pushing config on the SUT.
  virtual absl::Status OnConfigPush(absl::string_view version,
                                    Testbed& testbed) {
    return absl::OkStatus();
  }

  // Called after stopping traffic from the Control Device or the Traffic
  // Generator in the testbed.
  virtual absl::Status OnStopTraffic(absl::string_view version,
                                     Testbed& testbed) {
    return absl::OkStatus();
  }

  // Called after clearing up flows from the SUT.
  virtual absl::Status OnFlowCleanup(absl::string_view version,
                                     Testbed& testbed) {
    return absl::OkStatus();
  }
};

}  // namespace pins_test

#endif  // PINS_TESTS_INTEGRATION_SYSTEM_NSF_INTERFACES_COMPONENT_VALIDATOR_H_
