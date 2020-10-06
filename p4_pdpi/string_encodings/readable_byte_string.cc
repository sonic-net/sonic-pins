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
#include "p4_pdpi/string_encodings/readable_byte_string.h"

#include <algorithm>
#include <string>

#include "absl/status/status.h"
#include "absl/strings/ascii.h"
#include "absl/strings/escaping.h"
#include "absl/strings/match.h"
#include "absl/strings/str_replace.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/strings/strip.h"
#include "gutil/status.h"
#include "p4_pdpi/string_encodings/bit_string.h"
#include "p4_pdpi/string_encodings/hex_string.h"

namespace pdpi {

absl::StatusOr<std::string> ReadableByteStringToByteString(
    absl::string_view readable_byte_string) {
  BitString result;

  // Process line by line
  for (absl::string_view line_raw :
       absl::StrSplit(readable_byte_string, '\n')) {
    // Remove whitespace
    std::string line = absl::StrReplaceAll(line_raw, {{" ", ""}});

    // Skip label
    auto colon_pos = line.find(':');
    if (colon_pos != std::string::npos) {
      line = line.substr(colon_pos + 1);
    }

    // Remove comments
    auto hash_pos = line.find('#');
    if (hash_pos != std::string::npos) {
      line = line.substr(0, hash_pos);
    }

    // Skip empty lines
    if (line.empty()) continue;

    // Append value
    absl::string_view value = line;
    if (absl::ConsumePrefix(&value, "0b")) {
      for (uint8_t character : value) {
        if (character == '0') {
          result.AppendBit(0);
        } else if (character == '1') {
          result.AppendBit(1);
        } else {
          return gutil::InvalidArgumentErrorBuilder()
                 << "Invalid character in 0b expression: '" << character << "'";
        }
      }
    } else if (absl::ConsumePrefix(&value, "0x")) {
      for (uint8_t character : value) {
        if (auto char_value = HexCharToDigit(character); char_value.ok()) {
          result.AppendBits(std::bitset<4>(*char_value));
        } else {
          return gutil::InvalidArgumentErrorBuilder()
                 << "Invalid character in 0x expression: '" << character << "'";
        }
      }
    } else {
      return gutil::InvalidArgumentErrorBuilder()
             << "Cannot parse readable byte string value: '" << value << "'";
    }
  }

  return result.ToByteString();
}

}  // namespace pdpi
