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

#include <iostream>

#include "absl/status/status.h"
#include "p4_infra/string_encodings/decimal_string.h"

#define TEST_STATUSOR(function_call)                                           \
  do {                                                                         \
    std::cout << "$ " << #function_call << "\n-> ";                            \
    if (auto status_or = function_call; status_or.ok()) {                      \
      std::cout << status_or.value();                                          \
    } else {                                                                   \
      std::cout << "error: "                                                   \
                << absl::StatusCodeToString(status_or.status().code()) << ": " \
                << status_or.status().message();                               \
    }                                                                          \
    std::cout << "\n\n";                                                       \
  } while (false)

int main() {
  TEST_STATUSOR(string_encodings::DecimalStringToInt("0123"));
  TEST_STATUSOR(string_encodings::DecimalStringToInt("x123"));
  TEST_STATUSOR(string_encodings::DecimalStringToInt("-123"));
  TEST_STATUSOR(string_encodings::DecimalStringToInt("+123"));
  TEST_STATUSOR(string_encodings::DecimalStringToInt("2147483648"));
  TEST_STATUSOR(string_encodings::DecimalStringToInt("2147483650"));
  TEST_STATUSOR(string_encodings::DecimalStringToInt("0x1112323"));
  TEST_STATUSOR(string_encodings::DecimalStringToInt("2147483647"));
  TEST_STATUSOR(string_encodings::DecimalStringToInt("0"));

  TEST_STATUSOR(string_encodings::DecimalStringToInt64("9223372036854775807"));
  TEST_STATUSOR(string_encodings::DecimalStringToInt64("9223372036854775808"));

  TEST_STATUSOR(string_encodings::DecimalStringToInt32("2147483648"));
  TEST_STATUSOR(string_encodings::DecimalStringToInt32("2147483647"));
  TEST_STATUSOR(string_encodings::DecimalStringToUint32("4294967295"));
  TEST_STATUSOR(string_encodings::DecimalStringToUint32("4294967296"));

  TEST_STATUSOR(
      string_encodings::DecimalStringToUint64("18446744073709551615"));
  TEST_STATUSOR(
      string_encodings::DecimalStringToUint64("18446744073709551616"));

  TEST_STATUSOR(string_encodings::IntToDecimalString(-1));
  // decimal literal.
  TEST_STATUSOR(string_encodings::IntToDecimalString(213));
  TEST_STATUSOR(string_encodings::IntToDecimalString(2147483648));
  TEST_STATUSOR(string_encodings::IntToDecimalString(4294967296));
  TEST_STATUSOR(string_encodings::IntToDecimalString(4294967295U));
  TEST_STATUSOR(string_encodings::IntToDecimalString(9223372036854775807));
  TEST_STATUSOR(string_encodings::IntToDecimalString(18446744073709551615U));
  // octal literal.
  TEST_STATUSOR(string_encodings::IntToDecimalString(0213));
  // hexadecimal literal.
  TEST_STATUSOR(string_encodings::IntToDecimalString(0x213));
}
