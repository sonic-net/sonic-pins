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
#include "p4_pdpi/string_encodings/bit_string.h"

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"

namespace pdpi {

using ::gutil::IsOkAndHolds;
using ::testing::Eq;

// TODO: Consider adding more coverage (though the clients of this
// library have excellent coverage).

TEST(ReadableByteStringTest, OfByteStringWorks) {
  BitString test = BitString::OfByteString("\x01\x2a\xff");

  EXPECT_THAT(test.ToByteString(), IsOkAndHolds("\x01\x2a\xff"));
  EXPECT_THAT(test.ToHexString(), IsOkAndHolds("0x012aff"));
}

TEST(ReadableByteStringTest, ConsumeHexStringWorks) {
  BitString test = BitString::OfByteString("\xff\xff\xff\xff\xff");
  EXPECT_THAT(test.ConsumeHexString(1), IsOkAndHolds("0x1"));
  EXPECT_THAT(test.ConsumeHexString(5), IsOkAndHolds("0x1f"));
  EXPECT_THAT(test.ConsumeHexString(9), IsOkAndHolds("0x1ff"));
}

TEST(ReadableByteStringTest, ConsumeBitsetWorks) {
  BitString test = BitString::OfByteString("\x12\x34");
  EXPECT_THAT(test.ConsumeBitset<16>(),
              IsOkAndHolds(Eq(std::bitset<16>(0x1234))));
}

}  // namespace pdpi
