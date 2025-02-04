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

#ifndef PINS_TESTS_INTEGRATION_SYSTEM_NSF_INTERFACES_TRAFFIC_HELPER_H_
#define PINS_TESTS_INTEGRATION_SYSTEM_NSF_INTERFACES_TRAFFIC_HELPER_H_

#include "absl/status/status.h"
#include "tests/integration/system/nsf/interfaces/testbed.h"

namespace pins_test {

// Interface to control traffic in the given `testbed` during NSF integration
// test.
//
// Note: The caller is responsible for ensuring that exact same testbed is
// passed throughout the test.
class TrafficHelper {
 public:
  virtual ~TrafficHelper() = default;

  // Starts traffic with a predefined traffic configuration from a Control
  // Device or Traffic Generator in the testbed.
  virtual absl::Status StartTraffic(Testbed& testbed) = 0;

  // Stops traffic in the testbed.
  virtual absl::Status StopTraffic(Testbed& testbed) = 0;

  // Validates traffic in the testbed.
  absl::Status ValidateTraffic(Testbed& testbed) {
    return ValidateTraffic(testbed, 0);
  };
  virtual absl::Status ValidateTraffic(Testbed& testbed,
                                       int error_percentage) = 0;
};

}  // namespace pins_test

#endif  // PINS_TESTS_INTEGRATION_SYSTEM_NSF_INTERFACES_TRAFFIC_HELPER_H_
