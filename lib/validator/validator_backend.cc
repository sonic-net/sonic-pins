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

#include "lib/validator/validator_backend.h"

#include <functional>
#include <string>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/log/log.h"
#include "absl/meta/type_traits.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "absl/types/span.h"

namespace pins_test {

absl::Status ValidatorBackend::RunValidations(
    absl::string_view device, absl::Span<const absl::string_view> validations,
    int retry_count, absl::Duration timeout) {
  if (!devices_.contains(device)) {
    return absl::NotFoundError(
        absl::StrCat(device, " not supported by backend."));
  }

  bool validation_support = false;
  for (const auto& validation_tag : validations) {
    // Check the validation tag.
    auto validation_it = validation_map_.find(validation_tag);
    if (validation_it == validation_map_.end()) continue;
    validation_support = true;

    for (const auto& callback : validation_it->second) {
      absl::Status operation_status;
      for (int execution_count = 1; execution_count <= retry_count + 1;
           ++execution_count) {
        operation_status = callback(device, timeout);
        if (operation_status.ok()) break;
        LOG(INFO) << "Running " << validation_tag << " on " << device
                  << " failed on " << execution_count << "/" << retry_count + 1
                  << " attempts with: " << operation_status.message();
      }
      if (!operation_status.ok())
        return absl::InternalError(absl::StrCat(
            "Running ", validation_tag, " on ", device,
            " fails with internal error after ", retry_count, " retries"));
    }
  }
  if (!validation_support) {
    return absl::NotFoundError(
        absl::StrCat("Validations are not supported by backend."));
  }
  return absl::OkStatus();
}

void ValidatorBackend::AddCallbacksToValidation(
    absl::string_view validation, absl::Span<const Callback> callbacks) {
  for (const auto& callback : callbacks) {
    validation_map_[validation].push_back(callback);
  }
}

}  // namespace pins_test
