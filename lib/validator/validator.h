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

#ifndef PINS_LIB_VALIDATOR_VALIDATOR_H_
#define PINS_LIB_VALIDATOR_VALIDATOR_H_

#include <memory>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "lib/validator/validator_backend.h"

namespace pins_test {

// `Validator` provides a backend-agnostic class for tests to run certain
// validation routines on arbitrary devices. This allows tests to properly check
// the status of those devices, even if the devices themselves have proprietary
// routines. Because `ValidatorBackend` instances to bind arbitrary functions
// to string tags, tests can then run a set of string tags on any device
// supported by at least one of the backends. The device is defined by some
// reachable address, whether that be a FQDN or an IP address.
//
// Usage:
// validator.RunValidations({"device1.net"}, {Validator::kReady});
class Validator {
 public:
  // `kReady` refers to when the device is ready to have operations run on it.
  static constexpr absl::string_view kReady = "Ready";

  // Initializes the 'Validator' with the provided 'backends'. Calls
  // 'SetupValidations' on every backend.
  Validator(std::vector<std::unique_ptr<ValidatorBackend>> backends);

  // Runs the provided `validations` on the provided reachable addresses of the
  // `devices`. The provided `retry_count` option refers to how many times a
  // specific validation will have to fail before being considered a failure.
  // The provided `timeout` option refers to how long each try should take
  // before timing out.
  absl::Status RunValidations(absl::Span<const absl::string_view> devices,
                              absl::Span<const absl::string_view> validations,
                              int retry_count = 3,
                              absl::Duration timeout = absl::Minutes(5));

 private:
  // The provided backends that this `Validator` will use.
  std::vector<std::unique_ptr<ValidatorBackend>> backends_;
};

}  // namespace pins_test

#endif  // PINS_LIB_VALIDATOR_VALIDATOR_H_
