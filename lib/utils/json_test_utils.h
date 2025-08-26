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
#ifndef PINS_LIB_UTILS_JSON_TEST_UTILS_H_
#define PINS_LIB_UTILS_JSON_TEST_UTILS_H_

#include <ostream>
#include <string_view>

#include "gtest/gtest.h"
#include "include/nlohmann/json.hpp"
#include "lib/utils/json_utils.h"

namespace pins_test {

// Implementation of a matcher that checks if a string is a valid JSON and if it
// is equal to the expected JSON. Since this is used in tests, it is okay to
// crash if the expected JSON is invalid.
class JsonIsMatcher {
 public:
  // Needed to be treated as a matcher by googletest.
  using is_gtest_matcher = void;

  explicit JsonIsMatcher(std::string_view expected_json)
      : expected_json_(json_yang::ParseJson(expected_json).value())  // Crash ok
  {}

  // Checks if the input `json` string is valid JSON and equivalent to the
  // expected JSON. If not, prints a diff to `os` or an error if it fails to
  // parse `json`.
  bool MatchAndExplain(std::string_view json, std::ostream* os) const;

  // Describes what the matcher is matching to.
  void DescribeTo(std::ostream* os) const {
    *os << "Equal to:\n" << json_yang::DumpJson(expected_json_);
  }

  // Describes what the matcher is not matching to if negated.
  void DescribeNegationTo(std::ostream* os) const {
    *os << "Not equal to:\n" << json_yang::DumpJson(expected_json_);
  }

 private:
  nlohmann::json expected_json_;
};

// Creates a matcher that checks if a string is valid JSON and if it is
// equivalent to the `expected_json`. Crashes if the expected JSON is invalid.
inline testing::Matcher<std::string_view> JsonIs(
    std::string_view expected_json) {
  return JsonIsMatcher(expected_json);
}

}  // namespace pins_test

#endif  // PINS_LIB_UTILS_JSON_TEST_UTILS_H_
