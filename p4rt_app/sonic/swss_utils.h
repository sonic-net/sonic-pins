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

#ifndef PINS_P4RT_APP_SONIC_SWSS_UTILS_H_
#define PINS_P4RT_APP_SONIC_SWSS_UTILS_H_

// This file contains utilities for working with swss_common.

#include <string>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "swss/rediscommand.h"

namespace p4rt_app {
namespace sonic {

// Returns true if left exactly equals right.
bool kfvEq(const swss::KeyOpFieldsValuesTuple& left,
           const swss::KeyOpFieldsValuesTuple& right);

// Look up and return the value for the given field.
absl::StatusOr<std::string> kfvFieldLookup(
    const swss::KeyOpFieldsValuesTuple& kfv, absl::string_view field);

}  // namespace sonic
}  // namespace p4rt_app

#endif  // PINS_P4RT_APP_SONIC_SWSS_UTILS_H_
