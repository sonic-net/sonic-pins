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

#ifndef PINS_LIB_VALIDATOR_VALIDATOR_BACKEND_H_
#define PINS_LIB_VALIDATOR_VALIDATOR_BACKEND_H_

#include <functional>
#include <string>
#include <utility>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "absl/types/span.h"

namespace pins_test {

// `ValidatorBackend` is an abstract class that performs the common operations
// of keeping track of callbacks and devices for its subclasses, while providing
// the interface for the `Validator` class to run validations on arbitrary
// device types. Subclasses of `ValidatorBackend` should define a set of
// validation functions and add them with `AddCallbacksToValidation` in the
// overriden `SetupValidations` function.
class ValidatorBackend {
public:
  virtual ~ValidatorBackend() {}

  // Runs the various `validations` on the specified reachable `device` address,
  // with the provided `retry_count` and `timeout` options. Returns
  // `absl::StatusCode::kNotFound` if the `device` is ignored because it is not
  // supported.
  absl::Status RunValidations(absl::string_view device,
                              absl::Span<const absl::string_view> validations,
                              int retry_count, absl::Duration timeout);

  // Sets up all validation callbacks to validation tag bindings. Called by
  // `Validator` upon receiving backends in constructor.
  virtual void SetupValidations() = 0;

protected:
  // Initializes set of supported `devices` for this backend. These `devices`
  // are provided by the subclass.
  ValidatorBackend(absl::flat_hash_set<std::string> devices)
      : devices_(std::move(devices)) {}

  // `Callback` is a validation function:
  // Parameters:
  //   `absl::string_view` chassis - Address of chassis to run validation on.
  //   `absl::Duration` timeout - Timeout duration for the validation.
  // Returns `absl::Status` - Whether or not the validation succeeded or not.
  using Callback =
      std::function<absl::Status(absl::string_view, absl::Duration)>;

  // Adds the provided `callbacks` to the `validation` tag. Called by subclass
  // to bind their validations to various tags in `SetupValidations`.
  void AddCallbacksToValidation(absl::string_view validation,
                                absl::Span<const Callback> callbacks);

  // The set of all devices supported by this backend. Devices not in this set
  // will be ignored by this backend.
  absl::flat_hash_set<std::string> devices_;

private:
  // The map of validation tag and callbacks.
  absl::flat_hash_map<std::string, std::vector<Callback>> validation_map_;
};

} // namespace pins_test

#endif // PINS_LIB_VALIDATOR_VALIDATOR_BACKEND_H_
