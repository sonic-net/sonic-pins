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

#include "p4_infra/string_encodings/decimal_string.h"

#include <cctype>
#include <cstdint>
#include <limits>
#include <string>

#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "gutil/gutil/status.h"

namespace string_encodings {
namespace {

template <typename IntType>
absl::StatusOr<IntType> DecimalStringTo(absl::string_view decimal_string) {
  static_assert(sizeof(IntType) == 4 || sizeof(IntType) == 8,
                "DecimalStringTo works only with 32-bit or 64-bit integers.");
  IntType result = 0;
  const IntType max_value = std::numeric_limits<IntType>::max();
  for (const char decimal_char : decimal_string) {
    // We only allow positive value without sign. So, any character that is not
    // a valid digit will be treated as invalid character. (e.g. '-', '+').
    if (!std::isdigit(decimal_char)) {
      return gutil::InvalidArgumentErrorBuilder()
             << "invalid decimal string, " << decimal_string
             << " contains non-digit character: " << decimal_char << ".";
    }
    int digit = decimal_char - '0';
    // Check the leading 0 case (e.g., "0123").
    if (result == 0 && digit == 0 && decimal_string.size() > 1)
      return gutil::InvalidArgumentErrorBuilder()
             << "invalid decimal string, " << decimal_string
             << " starts with 0.";

    // Check the overflow case.
    if (result > max_value / 10 || result * 10 > max_value - digit) {
      return gutil::InvalidArgumentErrorBuilder()
             << "invalid decimal string, " << decimal_string
             << " exceeds the numeric limit of " << max_value << ".";
    }
    result = result * 10 + digit;
  }

  return result;
}

template <typename IntType>
absl::StatusOr<std::string> ToDecimalString(IntType value) {
  // Only positive decimal value is allowed here.
  if (value < 0) {
    return gutil::InvalidArgumentErrorBuilder()
           << "invalid decimal value, only positive value is allowed but input "
              "value is: "
           << value << ".";
  }
  return absl::StrCat(value);
}

}  // namespace

absl::StatusOr<int> DecimalStringToInt(absl::string_view decimal_string) {
  return DecimalStringTo<int>(decimal_string);
}
absl::StatusOr<int32_t> DecimalStringToInt32(absl::string_view decimal_string) {
  return DecimalStringTo<int32_t>(decimal_string);
}
absl::StatusOr<int64_t> DecimalStringToInt64(absl::string_view decimal_string) {
  return DecimalStringTo<int64_t>(decimal_string);
}
absl::StatusOr<uint32_t> DecimalStringToUint32(
    absl::string_view decimal_string) {
  return DecimalStringTo<uint32_t>(decimal_string);
}
absl::StatusOr<uint64_t> DecimalStringToUint64(
    absl::string_view decimal_string) {
  return DecimalStringTo<uint64_t>(decimal_string);
}

absl::StatusOr<std::string> IntToDecimalString(int value) {
  return ToDecimalString<int>(value);
}
absl::StatusOr<std::string> IntToDecimalString(int64_t value) {
  return ToDecimalString<int64_t>(value);
}
absl::StatusOr<std::string> IntToDecimalString(uint32_t value) {
  return ToDecimalString<uint32_t>(value);
}
absl::StatusOr<std::string> IntToDecimalString(uint64_t value) {
  return ToDecimalString<uint64_t>(value);
}

}  // namespace string_encodings
