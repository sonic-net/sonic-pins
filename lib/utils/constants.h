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

#ifndef PINS_LIB_UTILS_CONSTANTS_H_
#define PINS_LIB_UTILS_CONSTANTS_H_

#include "absl/time/time.h"
#include "artifacts/otg.pb.h"

namespace pins_test {

// TODO: Reduce reboot up time.
// Don't use this function in the test code as much as possible.
// Timeouts for all platforms.
inline constexpr absl::Duration kColdRebootWaitForUpTime = absl::Minutes(6);

// Returns the time to wait for the SUT to cold reboot.
absl::Duration GetColdRebootWaitForUpTime();

}  // namespace pins_test

#endif  // PINS_LIB_UTILS_CONSTANTS_H_
