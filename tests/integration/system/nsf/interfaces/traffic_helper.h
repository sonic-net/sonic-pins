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
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
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
  //
  // The `config_label`, if present, is the label/version of the config that is
  // expected to be present on the SUT at the time of starting the traffic
  // through it.
  // Note: If not provided, the `config_label` is by default an empty string.
  virtual absl::Status StartTraffic(Testbed& testbed,
                                    absl::string_view config_label) = 0;
  absl::Status StartTraffic(Testbed& testbed) {
    return StartTraffic(testbed, /*config_label=*/"");
  }

  // Stops traffic in the testbed.
  virtual absl::Status StopTraffic(Testbed& testbed) = 0;

  // Validates traffic in the testbed.
  // The `max_acceptable_outage` is the upper limit of the traffic disruption
  // duration. If the total duration of the traffic disruption detected during
  // the entire flow of traffic is found to be less than the
  // `max_acceptable_outage` duration, it will be considered permissible and
  // would not cause traffic validation failure.
  virtual absl::Status ValidateTraffic(
      Testbed& testbed, absl::Duration max_acceptable_outage) = 0;
  absl::Status ValidateTraffic(Testbed& testbed) {
    return ValidateTraffic(testbed, absl::ZeroDuration());
  };
};

}  // namespace pins_test

#endif  // PINS_TESTS_INTEGRATION_SYSTEM_NSF_INTERFACES_TRAFFIC_HELPER_H_
