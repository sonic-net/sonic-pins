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
#include "lib/utils/json_test_utils.h"

#include <ostream>
#include <string_view>

#include "absl/status/statusor.h"
#include "include/nlohmann/json.hpp"
#include "lib/utils/json_utils.h"

namespace pins_test {

bool JsonIsMatcher::MatchAndExplain(std::string_view actual_json,
                                    std::ostream* os) const {
  absl::StatusOr<nlohmann::json> actual = json_yang::ParseJson(actual_json);
  if (!actual.ok()) {
    if (os != nullptr) {
      *os << "Failed to parse JSON: " << actual.status();
    }
    return false;
  }

  nlohmann::json difference = nlohmann::json::diff(expected_json_, *actual);
  if (difference.empty()) {
    return true;
  }

  if (os != nullptr) {
    *os << "Difference:\n" << json_yang::DumpJson(difference);
  }
  return false;
}

}  // namespace pins_test
