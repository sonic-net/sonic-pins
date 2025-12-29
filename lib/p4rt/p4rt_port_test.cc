/*
 * Copyright 2024 Google LLC
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
#include "lib/p4rt/p4rt_port.h"

#include <cstdint>
#include <limits>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"

namespace pins_test {
namespace {

using ::gutil::IsOk;
using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::testing::Eq;
using ::testing::Not;

TEST(P4rtPortId, DefaultConstructible) {
  EXPECT_EQ(P4rtPortId().GetOpenConfigEncoding(), 0);
  EXPECT_EQ(P4rtPortId().GetP4rtEncoding(), "0");
}

TEST(P4rtPortId, RoundtripsFromInt) {
  constexpr int kP4rtPortIdInt = 42;
  const std::string kP4rtPortIdString = "42";
  P4rtPortId port_id = P4rtPortId::MakeFromOpenConfigEncoding(kP4rtPortIdInt);
  EXPECT_EQ(port_id.GetOpenConfigEncoding(), kP4rtPortIdInt);
  EXPECT_EQ(port_id.GetP4rtEncoding(), kP4rtPortIdString);
  EXPECT_THAT(P4rtPortId::MakeFromP4rtEncoding(port_id.GetP4rtEncoding()),
              IsOkAndHolds(Eq(port_id)));
}

TEST(P4rtPortId, RoundtripsFromString) {
  constexpr int kP4rtPortIdInt = 42;
  const std::string kP4rtPortIdString = "42";
  ASSERT_OK_AND_ASSIGN(P4rtPortId port_id,
                       P4rtPortId::MakeFromP4rtEncoding(kP4rtPortIdString));
  EXPECT_EQ(port_id.GetOpenConfigEncoding(), kP4rtPortIdInt);
  EXPECT_EQ(port_id.GetP4rtEncoding(), kP4rtPortIdString);
  EXPECT_EQ(
      P4rtPortId::MakeFromOpenConfigEncoding(port_id.GetOpenConfigEncoding()),
      port_id);
}

TEST(P4rtPortId, MakeFromHexstringEncodingWorks) {
  constexpr int kP4rtPortIdInt = 42;
  const std::string kP4rtPortIdString = "42";
  const std::string kP4rtPortIdHexString = "0x2a";
  ASSERT_OK_AND_ASSIGN(
      P4rtPortId port_id,
      P4rtPortId::MakeFromHexstringEncoding(kP4rtPortIdHexString));
  EXPECT_EQ(port_id.GetOpenConfigEncoding(), kP4rtPortIdInt);
  EXPECT_EQ(port_id.GetP4rtEncoding(), kP4rtPortIdString);
}

TEST(P4rtPortId, GetBmv2P4rtEncodingWorksForPortsFittingIn9Bits) {
  EXPECT_THAT(P4rtPortId::MakeFromOpenConfigEncoding(0).GetBmv2P4rtEncoding(),
              IsOkAndHolds(Eq(std::string(1, '\0'))));

  EXPECT_THAT(P4rtPortId::MakeFromOpenConfigEncoding(1).GetBmv2P4rtEncoding(),
              IsOkAndHolds(Eq("\x01")));

  EXPECT_THAT(
      P4rtPortId::MakeFromOpenConfigEncoding(0x2a).GetBmv2P4rtEncoding(),
      IsOkAndHolds(Eq("\x2a")));

  EXPECT_THAT(
      P4rtPortId::MakeFromOpenConfigEncoding(0x01ff).GetBmv2P4rtEncoding(),
      IsOkAndHolds(Eq("\x01\xff")));
}

TEST(P4rtPortId, GetBmv2P4rtEncodingFailsForPortsNotFittingIn9Bits) {
  EXPECT_THAT(
      P4rtPortId::MakeFromOpenConfigEncoding(0x0200).GetBmv2P4rtEncoding(),
      StatusIs(absl::StatusCode::kFailedPrecondition));

  EXPECT_THAT(P4rtPortId::MakeFromOpenConfigEncoding(
                  std::numeric_limits<uint32_t>::max())
                  .GetBmv2P4rtEncoding(),
              StatusIs(absl::StatusCode::kFailedPrecondition));
}

TEST(P4rtPortId, PointwiseIntEquivalence) {
  const std::vector<uint32_t> kP4rtPortIdIntSpan = {42, 3, 500};
  std::vector<P4rtPortId> port_ids_from_vector_function =
      P4rtPortId::MakeVectorFromOpenConfigEncodings(kP4rtPortIdIntSpan);
  std::vector<P4rtPortId> port_ids_from_single_function;
  for (uint32_t port_id : kP4rtPortIdIntSpan) {
    port_ids_from_single_function.push_back(
        P4rtPortId::MakeFromOpenConfigEncoding(port_id));
  }
  EXPECT_EQ(port_ids_from_vector_function, port_ids_from_single_function);
}

TEST(P4rtPortId, PointwiseStringEquivalence) {
  const std::vector<std::string> kP4rtPortIdStringSpan = {"42", "3", "500"};
  ASSERT_OK_AND_ASSIGN(
      std::vector<P4rtPortId> port_ids_from_vector_function,
      P4rtPortId::MakeVectorFromP4rtEncodings(kP4rtPortIdStringSpan));
  std::vector<P4rtPortId> port_ids_from_single_function;
  for (absl::string_view port_id_string : kP4rtPortIdStringSpan) {
    ASSERT_OK_AND_ASSIGN(P4rtPortId port_id,
                         P4rtPortId::MakeFromP4rtEncoding(port_id_string));
    port_ids_from_single_function.push_back(port_id);
  }
  EXPECT_EQ(port_ids_from_vector_function, port_ids_from_single_function);
}

TEST(P4rtPortId, InvalidFromString) {
  EXPECT_THAT(P4rtPortId::MakeFromP4rtEncoding("not a decimal string"),
              Not(IsOk()));
  EXPECT_THAT(P4rtPortId::MakeFromP4rtEncoding("-1"), Not(IsOk()));
  EXPECT_THAT(P4rtPortId::MakeFromP4rtEncoding("99999999999999999999999999999"),
              Not(IsOk()));
}

TEST(P4rtPortId, Comparisons) {
  P4rtPortId port_id_big = P4rtPortId::MakeFromOpenConfigEncoding(42);
  P4rtPortId port_id_medium = P4rtPortId::MakeFromOpenConfigEncoding(21);
  P4rtPortId port_id_small = P4rtPortId::MakeFromOpenConfigEncoding(1);
  EXPECT_LT(port_id_small, port_id_medium);
  EXPECT_LT(port_id_medium, port_id_big);
}

}  // namespace
}  // namespace pins_test
