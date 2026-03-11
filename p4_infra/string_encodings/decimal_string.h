// Copyright 2021 Google LLC
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

// This file defines conversion functions to and from decimal strings with
// positive value such as "10" to ease working with PD protos.

#ifndef PINS_P4_INFRA_STRING_ENCODINGS_DECIMAL_STRING_H_
#define PINS_P4_INFRA_STRING_ENCODINGS_DECIMAL_STRING_H_

#include <cstdint>
#include <string>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"

namespace string_encodings {

// Converts given decimal string to integer value, returns an error status if
// the conversion fails.
// We only allow positive value without sign and leading 0s. (e.g., "-10",
// "+10", "012" will be treated as invalid input).
absl::StatusOr<int> DecimalStringToInt(absl::string_view decimal_string);
absl::StatusOr<int32_t> DecimalStringToInt32(absl::string_view decimal_string);
absl::StatusOr<int64_t> DecimalStringToInt64(absl::string_view decimal_string);
absl::StatusOr<uint32_t>
DecimalStringToUint32(absl::string_view decimal_string);
absl::StatusOr<uint64_t>
DecimalStringToUint64(absl::string_view decimal_string);

// Converts given integer value to decimal string if the integer is
// non-negative, or returns an error status otherwise.
absl::StatusOr<std::string> IntToDecimalString(int value);
absl::StatusOr<std::string> IntToDecimalString(int64_t value);
absl::StatusOr<std::string> IntToDecimalString(uint32_t value);
absl::StatusOr<std::string> IntToDecimalString(uint64_t value);
}  // namespace string_encodings

#endif  // PINS_P4_INFRA_STRING_ENCODINGS_DECIMAL_STRING_H_
