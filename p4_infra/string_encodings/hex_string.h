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

// This file defines conversion functions to and from hexadecimal strings such
// as "0xf0a1" to ease working with PD protos.
// See the documentation of HEX_STRING in ir.proto for details of the encoding.

#ifndef PINS_INFRA_P4_INFRA_STRING_ENCODINGS_HEX_STRING_H_
#define PINS_INFRA_P4_INFRA_STRING_ENCODINGS_HEX_STRING_H_

#include <stddef.h>

#include <algorithm>
#include <bitset>
#include <cstddef>
#include <cstdint>
#include <string>

#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/strings/strip.h"
#include "gutil/gutil/status.h"

namespace string_encodings {

// -- Conversions to Hex Strings -----------------------------------------------

template <std::size_t num_bits>
std::string BitsetToHexString(const std::bitset<num_bits>& bitset);

std::string ByteStringToHexString(absl::string_view byte_string);

// We do not provide direct conversions from integer types; use
// BitsetToHexString for that purpose, e.g.:
// ```
//   int port;
//   BitsetToHexString(std::bitset<kPortWidth>(port));
//
//   // Using the implicit std::bitset constructor.
//   BitsetToHexString<kPortWidth>(port);
// ```

// -- Conversions from Hex Strings ---------------------------------------------

// The following functions return an error status iff the input string is
// invalid (i.e., is not a '0x'-prefixed hex string) or the conversion would
// cause a loss of information (i.e., the input string contains non-zero bits
// that would have to be discarded).
//
// Additionally, `HexStringToBitset<num_bits>` returns an error status if
// num_bits is not in the interval [4 * # hex digits - 3, 4 * # hex digits].

template <std::size_t num_bits>
absl::StatusOr<std::bitset<num_bits>> HexStringToBitset(
    absl::string_view hex_string);

absl::StatusOr<int> HexStringToInt(absl::string_view hex_string);
absl::StatusOr<int32_t> HexStringToInt32(absl::string_view hex_string);
absl::StatusOr<int64_t> HexStringToInt64(absl::string_view hex_string);
absl::StatusOr<uint32_t> HexStringToUint32(absl::string_view hex_string);
absl::StatusOr<uint64_t> HexStringToUint64(absl::string_view hex_string);

absl::StatusOr<std::string> HexStringToByteString(absl::string_view hex_string);

// == END OF PUBLIC INTERFACE ==================================================

char HexDigitToChar(int digit);
absl::StatusOr<int> HexCharToDigit(char hex_char);

template <std::size_t num_bits>
std::string BitsetToHexString(const std::bitset<num_bits>& bitset) {
  // Each hexadecimal digit is given by 4 bits in the bitset.
  const int num_hex_digits = (num_bits + 3) / 4;  // ceil(num_bits / 4.0)

  // Construct hex_string in reverse order, starting from least significant
  // digit.
  std::string hex_string;
  for (int i = 0; i < num_hex_digits; ++i) {
    int ith_digit = 0;
    // The ith digit is given by bits 4i+3 to 4i; we set the bits from most to
    // least significant.
    for (int k = 4 * i + 3; k >= 4 * i; --k) {
      int kth_bit = (k < num_bits) ? bitset[k] : 0;  // Implicit bits are 0.
      ith_digit = (ith_digit << 1) | kth_bit;
    }
    hex_string.push_back(HexDigitToChar(ith_digit));
  }

  // Reverse string and prepend "0x" prefix
  std::reverse(hex_string.begin(), hex_string.end());
  return absl::StrCat("0x", hex_string);
}

template <std::size_t num_bits>
absl::StatusOr<std::bitset<num_bits>> HexStringToAnyLargeEnoughBitset(
    absl::string_view hex_string) {
  if (!absl::ConsumePrefix(&hex_string, "0x")) {
    return gutil::InvalidArgumentErrorBuilder()
           << "missing '0x'-prefix in hexadecimal string: '" << hex_string
           << "'";
  }

  // Compute and set bits from least to most significant.
  std::bitset<num_bits> bitset;
  for (int i = 0; i < hex_string.size(); ++i) {
    const char ith_char = hex_string[hex_string.size() - i - 1];
    ASSIGN_OR_RETURN(
        const int ith_digit, HexCharToDigit(ith_char),
        _ << " while trying to convert hex string: " << hex_string);
    for (int j = 0; j < 4; ++j) {
      // k is the index of the j-th bit of the i-th hex digit.
      const std::size_t k = 4 * i + j;
      const bool kth_bit = (ith_digit >> j) % 2 == 1;
      if (!kth_bit) continue;
      if (k < num_bits) {
        bitset.set(k, kth_bit);
      } else {
        return gutil::InvalidArgumentErrorBuilder()
               << "hex string '0x" << hex_string << "' has bit #" << (k + 1)
               << " set to 1; conversion to " << num_bits
               << " bits would lose information";
      }
    }
  }
  return bitset;
}

template <std::size_t num_bits>
absl::StatusOr<std::bitset<num_bits>> HexStringToBitset(
    absl::string_view hex_string) {
  // Sanity check: hex_string.size() - 2 == ceil(num_bits/4).
  if (absl::StartsWith(hex_string, "0x")) {
    const int num_hex_chars = hex_string.size() - 2;  // Due to "0x"-prefix.
    const int expected_num_hex_chars = (num_bits + 3) / 4;  // ceil(num_bits/4)
    if (num_hex_chars != expected_num_hex_chars) {
      return gutil::InvalidArgumentErrorBuilder()
             << "illegal conversion from hex string '" << hex_string << "' to "
             << num_bits << " bits; expected " << expected_num_hex_chars
             << " hex digits but got " << num_hex_chars;
    }
  }
  return HexStringToAnyLargeEnoughBitset<num_bits>(hex_string);
}

}  // namespace string_encodings

#endif  // PINS_INFRA_P4_INFRA_STRING_ENCODINGS_HEX_STRING_H_
