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

#include "p4_infra/string_encodings/byte_string.h"

#include <bitset>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <string>
#include <utility>
#include <vector>

#include "absl/strings/escaping.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "p4_infra/string_encodings/safe.h"

namespace string_encodings {
namespace {

using ::gutil::IsOk;
using ::gutil::IsOkAndHolds;
using ::testing::Eq;
using ::testing::Not;

std::vector<std::pair<std::bitset<9>, std::string>>
BitsetsAndPaddedByteStrings() {
  return {
      {{0x00'00}, SafeString({0x00, 0x00})},
      {{0x00'01}, SafeString({0x00, 0x01})},
      {{0x01'cd}, SafeString({0x01, 0xcd})},
      {{0x00'23}, SafeString({0x00, 0x23})},
  };
}

std::vector<std::pair<std::bitset<9>, std::string>>
BitsetsAndP4RuntimeByteStrings() {
  return {
      {{0x00'00}, SafeString({0x00})},
      {{0x00'01}, SafeString({0x01})},
      {{0x01'cd}, SafeString({0x01, 0xcd})},
      {{0x00'23}, SafeString({0x23})},
  };
}

TEST(ByteStringTest, BitsetToPaddedByteStringCorrect) {
  for (const auto& [bitset, byte_str] : BitsetsAndPaddedByteStrings()) {
    EXPECT_EQ(BitsetToPaddedByteString(bitset), byte_str);
  }
}

TEST(ByteStringTest, BitsetToP4RuntimeByteStringCorrect) {
  for (const auto& [bitset, byte_str] : BitsetsAndP4RuntimeByteStrings()) {
    EXPECT_EQ(BitsetToP4RuntimeByteString(bitset), byte_str);
  }
}

TEST(ByteStringTest, ByteStringToBitsetCorrect) {
  // The empty string is rejected.
  EXPECT_THAT(ByteStringToBitset<9>(""), Not(IsOk()));

  // P4Runtime byte strings are accepted.
  for (const auto& [bitset, byte_str] : BitsetsAndP4RuntimeByteStrings()) {
    EXPECT_THAT(ByteStringToBitset<9>(byte_str), IsOkAndHolds(Eq(bitset)));
  }

  // Padded byte strings are accepted.
  for (const auto& [bitset, byte_str] : BitsetsAndPaddedByteStrings()) {
    EXPECT_THAT(ByteStringToBitset<9>(byte_str), IsOkAndHolds(Eq(bitset)));

    // Missing bytes are okay -- they will be assumed to be zero.
    EXPECT_THAT(ByteStringToBitset<200>(byte_str),
                IsOkAndHolds(Eq(std::bitset<200>(bitset.to_ulong()))));

    // Extra bytes are also okay if they are zero.
    const std::vector<std::string> zero_prefixes = {SafeString({0}),
                                                    SafeString({0, 0})};
    for (const auto& prefix : zero_prefixes) {
      EXPECT_THAT(ByteStringToBitset<9>(prefix + byte_str),
                  IsOkAndHolds(Eq(bitset)));
    }

    // Extra bytes are *not* okay if they are non-zero.
    const std::vector<std::string> nonzero_prefixes = {
        SafeString({1}), SafeString({2}), SafeString({3}), SafeString({100}),
        SafeString({1, 0})};
    for (const auto& prefix : nonzero_prefixes) {
      EXPECT_THAT(ByteStringToBitset<9>(prefix + byte_str), Not(IsOk()));
    }
  }

  // Extra nonzero bits are never okay.
  EXPECT_THAT(ByteStringToBitset<1>(SafeString({0b01})), IsOk());
  EXPECT_THAT(ByteStringToBitset<1>(SafeString({0b10})), Not(IsOk()));
  EXPECT_THAT(ByteStringToBitset<1>(SafeString({0, 0b01})), IsOk());
  EXPECT_THAT(ByteStringToBitset<1>(SafeString({0, 0b10})), Not(IsOk()));
  EXPECT_THAT(ByteStringToBitset<1>(SafeString({0, 0, 0b01})), IsOk());
  EXPECT_THAT(ByteStringToBitset<1>(SafeString({0, 0, 0b10})), Not(IsOk()));
  EXPECT_THAT(ByteStringToBitset<2>(SafeString({0, 0, 0b010})), IsOk());
  EXPECT_THAT(ByteStringToBitset<2>(SafeString({0, 0, 0b100})), Not(IsOk()));
}

TEST(ByteStringTest, BitsetToPaddedByteString_Regression_2020_12_02) {
  const auto bitset = ~std::bitset<128>();
  BitsetToPaddedByteString(bitset);  // No crash.
}

TEST(GetBitwidthOfByteString, EmptyStringHasWidthZero) {
  EXPECT_EQ(GetBitwidthOfByteString(""), 0);
}

TEST(GetBitwidthOfByteString, AllSingleByteStringsHaveExpectedBitwidth) {
  for (int i = 0; i < 255; ++i) {
    std::string bytes = "0";
    std::memcpy(bytes.data(), &i, 1);
    EXPECT_EQ(GetBitwidthOfByteString(bytes),
              i == 0 ? 1 : std::floor(1 + std::log2(i)))
        << "for bytes == int " << i;
  }
}

TEST(GetBitwidthOfByteString, TrailingPaddingIncreasesBitwdith) {
  EXPECT_EQ(GetBitwidthOfByteString(SafeString({'\x01'})), 1);
  EXPECT_EQ(GetBitwidthOfByteString(SafeString({'\x01', '\x00'})), 9);
  EXPECT_EQ(GetBitwidthOfByteString(SafeString({'\x01', '\x00', '\x00'})), 17);
}

TEST(GetBitwidthOfByteString, LeadingPaddingDoesNotAffectBitwidth) {
  EXPECT_EQ(GetBitwidthOfByteString(SafeString({'\x01'})), 1);
  EXPECT_EQ(GetBitwidthOfByteString(SafeString({'\x00', '\x01'})), 1);
  EXPECT_EQ(GetBitwidthOfByteString(SafeString({'\x00', '\x00', '\x01'})), 1);
}

}  // namespace
}  // namespace string_encodings
