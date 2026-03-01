// Copyright 2020 Google LLC
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

#include <cstdint>
#include <iostream>
#include <limits>

#include "absl/status/status.h"
#include "p4_infra/string_encodings/hex_string.h"

#define TEST_PURE(function_call)                                       \
  do {                                                                 \
    std::cout << "$ " << #function_call << "\n-> " << (function_call); \
    std::cout << "\n\n";                                               \
  } while (false)

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

using ::string_encodings::BitsetToHexString;
using ::string_encodings::HexStringToBitset;
using ::string_encodings::HexStringToInt;
using ::string_encodings::HexStringToInt32;
using ::string_encodings::HexStringToInt64;
using ::string_encodings::HexStringToUint32;
using ::string_encodings::HexStringToUint64;

int main() {
  // BitsetToHexString.
  TEST_PURE(BitsetToHexString(std::bitset<1>("0")));
  TEST_PURE(BitsetToHexString(std::bitset<1>("1")));
  TEST_PURE(BitsetToHexString(std::bitset<3>("100")));
  TEST_PURE(BitsetToHexString(std::bitset<3>("101")));
  TEST_PURE(BitsetToHexString(std::bitset<3>("110")));
  TEST_PURE(BitsetToHexString(std::bitset<3>("111")));
  TEST_PURE(BitsetToHexString(std::bitset<4>("1110")));
  TEST_PURE(BitsetToHexString(std::bitset<4>("1111")));
  TEST_PURE(BitsetToHexString(std::bitset<5>("00000")));
  TEST_PURE(BitsetToHexString(std::bitset<5>("00001")));
  TEST_PURE(BitsetToHexString(std::bitset<5>("10000")));
  TEST_PURE(BitsetToHexString(std::bitset<5>("10001")));
  TEST_PURE(BitsetToHexString(std::bitset<5>("11111")));
  TEST_PURE(BitsetToHexString<8 * sizeof(int)>(0));
  TEST_PURE(BitsetToHexString<8 * sizeof(int)>(1));
  TEST_PURE(BitsetToHexString<8 * sizeof(int)>(-1));
  TEST_PURE(BitsetToHexString<8 * sizeof(int)>(15));
  TEST_PURE(
      BitsetToHexString<8 * sizeof(int)>(std::numeric_limits<int>::max()));
  TEST_PURE(
      BitsetToHexString<8 * sizeof(int)>(std::numeric_limits<int>::min()));

  // HexStringToBitset.
  TEST_STATUSOR(HexStringToBitset<1>("0x0"));
  TEST_STATUSOR(HexStringToBitset<1>("0x1"));
  TEST_STATUSOR(HexStringToBitset<1>("0x01"));
  TEST_STATUSOR(HexStringToBitset<1>("0x000"));
  TEST_STATUSOR(HexStringToBitset<1>("0x2"));
  TEST_STATUSOR(HexStringToBitset<7>("0xf0"));
  TEST_STATUSOR(HexStringToBitset<8>("0xf0"));
  TEST_STATUSOR(HexStringToBitset<8>("0x00ff"));

  // HexStringToInt.
  TEST_STATUSOR(HexStringToInt("0x0"));
  TEST_STATUSOR(HexStringToInt("0x1"));
  TEST_STATUSOR(HexStringToInt("0x01"));
  TEST_STATUSOR(HexStringToInt("0x000"));
  TEST_STATUSOR(HexStringToInt("0x0fffffff"));
  TEST_STATUSOR(HexStringToInt("0xffffffff"));
  TEST_STATUSOR(HexStringToInt("0x100000000"));

  // HexStringToInt32.
  TEST_STATUSOR(HexStringToInt32(
      BitsetToHexString<32>(std::numeric_limits<int32_t>::max())));
  TEST_STATUSOR(HexStringToInt32(
      BitsetToHexString<64>(std::numeric_limits<int64_t>::max())));
  TEST_STATUSOR(HexStringToInt32(
      BitsetToHexString<32>(std::numeric_limits<int32_t>::min())));
  TEST_STATUSOR(HexStringToInt32(
      BitsetToHexString<64>(std::numeric_limits<int64_t>::min())));

  // HexStringToInt64.
  TEST_STATUSOR(HexStringToInt64(
      BitsetToHexString<32>(std::numeric_limits<int32_t>::max())));
  TEST_STATUSOR(HexStringToInt64(
      BitsetToHexString<64>(std::numeric_limits<int64_t>::max())));
  TEST_STATUSOR(HexStringToInt64(
      BitsetToHexString<32>(std::numeric_limits<int32_t>::min())));
  TEST_STATUSOR(HexStringToInt64(
      BitsetToHexString<64>(std::numeric_limits<int64_t>::min())));

  // HexStringToUint32.
  TEST_STATUSOR(HexStringToUint32("0x0000000000000000000000000001"));
  TEST_STATUSOR(HexStringToUint32("0xffffffff"));
  TEST_STATUSOR(HexStringToUint32("0x0ffffffff"));
  TEST_STATUSOR(HexStringToUint32("0x1ffffffff"));

  // HexStringToUint64.
  TEST_STATUSOR(HexStringToUint64("0xffffffffffffffff"));
  TEST_STATUSOR(HexStringToUint64("0x0ffffffffffffffff"));
  TEST_STATUSOR(HexStringToUint64("0x1ffffffffffffffff"));
}
