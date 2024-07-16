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

#include "lib/validator/validator.h"

#include <memory>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "lib/validator/validator_backend.h"

namespace pins_test {

Validator::Validator(std::vector<std::unique_ptr<ValidatorBackend>> backends)
    : backends_(std::move(backends)) {}

absl::Status Validator::RunValidations(
    absl::Span<const absl::string_view> devices,
    absl::Span<const absl::string_view> validations, int retry_count,
    absl::Duration timeout) {
  return absl::OkStatus();
}

}  // namespace pins_test
