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

#include "p4_infra/p4_pdpi/string_encodings/bit_string.h"

#include "absl/status/status.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status_matchers.h"

namespace pdpi {

using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::testing::Eq;

TEST(ReadableByteStringTest, OfByteStringWorks) {
  BitString test = BitString::OfByteString("\x01\x2a\xff");

  EXPECT_THAT(test.ToByteString(), IsOkAndHolds("\x01\x2a\xff"));
  EXPECT_THAT(test.ToHexString(), IsOkAndHolds("0x012aff"));
}

// Valid inputs are non-negative and within the size of the byte string.
TEST(ReadableByteStringTest, PeekHexStringWorksWithValidInputs) {
  BitString test = BitString::OfByteString("\xff\xff\xff\xff\xff");
  EXPECT_THAT(test.PeekHexString(1), IsOkAndHolds("0x1"));
  EXPECT_THAT(test.PeekHexString(5), IsOkAndHolds("0x1f"));
  EXPECT_THAT(test.PeekHexString(9), IsOkAndHolds("0x1ff"));
}

// If input is negative, return invalid argument error.
TEST(ReadableByteStringTest, PeekHexStringErrorWithNegativeInputs) {
  BitString test = BitString::OfByteString("\xff\xff\xff\xff\xff");
  EXPECT_THAT(
      test.PeekHexString(-1),
      StatusIs(absl::StatusCode::kInvalidArgument, "Cannot peek -1 bits."));
}

// If input is greater than the size of the byte string, return failed
// precondition error.
TEST(ReadableByteStringTest, PeekHexStringErrorWhenInputGreaterThanSize) {
  BitString test = BitString::OfByteString("\xff\xff\xff\xff\xff");
  EXPECT_THAT(test.PeekHexString(100),
              StatusIs(absl::StatusCode::kFailedPrecondition,
                       "Only 40 bits left, but attempted to peek 100 bits."));
}

TEST(ReadableByteStringTest, ConsumeHexStringWorksWithVailidInputs) {
  BitString test = BitString::OfByteString("\xff\xff\xff\xff\xff");
  EXPECT_THAT(test.ConsumeHexString(1), IsOkAndHolds("0x1"));
  EXPECT_THAT(test.ConsumeHexString(5), IsOkAndHolds("0x1f"));
  EXPECT_THAT(test.ConsumeHexString(9), IsOkAndHolds("0x1ff"));
}

TEST(ReadableByteStringTest, ConsumeHexStringErrorWithNegativeInput) {
  BitString test = BitString::OfByteString("\xff\xff\xff\xff\xff");
  EXPECT_THAT(
      test.ConsumeHexString(-1),
      StatusIs(absl::StatusCode::kInvalidArgument, "Cannot consume -1 bits."));
}

TEST(ReadableByteStringTest, ConsumeHexStringErrorWhenInputGreaterThanSize) {
  BitString test = BitString::OfByteString("\xff\xff\xff\xff\xff");
  EXPECT_THAT(
      test.ConsumeHexString(100),
      StatusIs(absl::StatusCode::kFailedPrecondition,
               "Only 40 bits left, but attempted to consume 100 bits."));
}

TEST(ReadableByteStringTest, ConsumeBitsetWorks) {
  BitString test = BitString::OfByteString("\x12\x34");
  EXPECT_THAT(test.ConsumeBitset<16>(),
              IsOkAndHolds(Eq(std::bitset<16>(0x1234))));
}

TEST(ReadableByteStringTest, ConsumeBitsetErrorWhenInputGreaterThanSize) {
  BitString test = BitString::OfByteString("\xff\xff\xff\xff\xff");
  EXPECT_THAT(
      test.ConsumeBitset<100>(),
      StatusIs(absl::StatusCode::kFailedPrecondition,
               "Only 40 bits left, but attempted to consume 100 bits."));
}

}  // namespace pdpi
