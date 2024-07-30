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

#include <functional>
#include <iterator>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "absl/algorithm/container.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "lib/validator/validator_backend.h"

namespace pins_test {

Validator::Validator(std::vector<std::unique_ptr<ValidatorBackend>> backends)
    : backends_(std::move(backends)) {
  for (const auto& backend : backends_) {
    backend->SetupValidations();
  }
}

absl::Status Validator::RunValidations(
    absl::Span<const absl::string_view> devices,
    absl::Span<const absl::string_view> validations, int retry_count,
    absl::Duration timeout) {
  std::vector<std::string> messages;
  auto validate_device = [&](absl::string_view device, const auto& backend) {
    return backend->RunValidations(device, validations, retry_count, timeout);
  };

  for (const auto& device : devices) {
    std::vector<absl::Status> validation_statuses;
    std::vector<std::string> validation_messages;
    absl::c_transform(
        backends_, std::back_inserter(validation_statuses),
        [&](const auto& backend) { return validate_device(device, backend); });

    absl::c_for_each(validation_statuses, [&](const absl::Status& status) {
      if (!status.ok() && status.code() != absl::StatusCode::kNotFound) {
        validation_messages.push_back(
            absl::StrCat(device, " failed with: ", status.message()));
      }
    });

    bool any_validation_passed =
        absl::c_any_of(validation_statuses, std::mem_fn(&absl::Status::ok));
    // If all statuses failed but there are no messages, then all statuses were
    // NOT_FOUND.
    if (!any_validation_passed && validation_messages.empty()) {
      validation_messages.push_back(
          absl::StrCat("No backends ran any validations on ", device));
    }
    messages.insert(messages.begin(), validation_messages.begin(),
                    validation_messages.end());
  }
  if (!messages.empty()) {
    return absl::InternalError(absl::StrJoin(messages, "; "));
  }
  return absl::OkStatus();
}

}  // namespace pins_test
