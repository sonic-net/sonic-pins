// Copyright 2025 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "tests/forwarding/hash_statistics_util.h"

#include <string>
#include <vector>

#include "absl/log/log.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status_matchers.h"  // IWYU pragma: keep
#include "tests/forwarding/group_programming_util.h"

namespace pins_test {
namespace {

using ::testing::DoubleNear;
using ::testing::Ge;
using ::testing::Le;

Distribution ExpectedDistribution(const std::vector<pins::GroupMember> members,
                                  int packet_count) {
  Distribution distribution;
  int total_weight = 0;
  for (const auto& member : members) {
    total_weight += member.weight;
  }
  for (const auto& member : members) {
    distribution[member.port] = packet_count * member.weight / total_weight;
  }
  return distribution;
}

// Creates a distribution with the given % error for each member. May not
// exactly match the target packet count.
Distribution DistributionWithError(
    const std::vector<pins::GroupMember> members, int target_packet_count,
    double error) {
  Distribution distribution =
      ExpectedDistribution(members, target_packet_count);
  int sign = 1;
  for (const auto& [member, packets] : distribution) {
    distribution[member] = static_cast<int>(
        distribution[member] * (1 + sign * error) + /*rounding*/ 0.5);
    sign = -sign;  // Swap between add and delete to maintain size if possible.
  }
  return distribution;
}

int PacketCount(const Distribution& distribution) {
  double total_packets = 0;
  for (const auto& [member, packets] : distribution) {
    total_packets += packets;
  }
  return total_packets;
}

TEST(PercentErrorTestPacketCount, IncreasesWithTotalWeight) {
  EXPECT_GT(PercentErrorTestPacketCount(100), PercentErrorTestPacketCount(10));
}

TEST(PercentErrorTestPacketCount, IsWithinRange) {
  // The general formula is 100 * total_weight:
  // Minimum packets (1,000) @ 10 packets.
  // Maximum packets (10,000) @ 100 packets.
  for (int total_weight : {1, 5, 9, 10, 11, 55, 99, 100, 101, 555}) {
    EXPECT_THAT(PercentErrorTestPacketCount(total_weight), Ge(1000))
        << " for total weight: " << total_weight;
    EXPECT_THAT(PercentErrorTestPacketCount(total_weight), Le(10000))
        << " for total weight: " << total_weight;
  }
}

MATCHER_P(IsAMultipleOf, divisor, "") {
  *result_listener << "where the remainder is " << (arg % divisor);
  return (arg % divisor) == 0;
}

TEST(PercentErrorTestPacketCount, IsAMultipleOfTotalWeight) {
  // The general formula is 100 * total_weight:
  // Minimum packets (1,000) @ 10 packets.
  // Maximum packets (10,000) @ 100 packets.
  for (int total_weight : {1, 5, 9, 10, 11, 55, 99, 100, 101, 555}) {
    EXPECT_THAT(PercentErrorTestPacketCount(total_weight),
                IsAMultipleOf(total_weight))
        << " for total weight: " << total_weight;
  }
}

TEST(ChiSquaredTestPacketCount, IncreasesWithMembers) {
  constexpr double kConfidence = 0.9;
  constexpr double kAverageError = 0.1;
  EXPECT_GT(
      ChiSquaredTestPacketCount(/*members=*/100, kConfidence, kAverageError),
      ChiSquaredTestPacketCount(/*members=*/10, kConfidence, kAverageError));
}

TEST(ChiSquaredTestPacketCount, IncreasesWithTighterPercentError) {
  constexpr double kMembers = 9;
  constexpr double kConfidence = 0.9;
  EXPECT_GT(
      ChiSquaredTestPacketCount(kMembers, kConfidence, /*average_error=*/0.2),
      ChiSquaredTestPacketCount(kMembers, kConfidence, /*average_error=*/0.8));
}

TEST(ChiSquaredTestPacketCount, IncreasesWithLowerTargetConfidence) {
  constexpr double kMembers = 9;
  constexpr double kAverageError = 0.1;
  EXPECT_GT(ChiSquaredTestPacketCount(kMembers, /*target_confidence=*/0.8,
                                      kAverageError),
            ChiSquaredTestPacketCount(kMembers, /*target_confidence=*/0.9,
                                      kAverageError));
}

class DistributionTest
    : public testing::TestWithParam<std::vector<pins::GroupMember>> {};

TEST_P(DistributionTest, ChiSquaredTestPacketCountUsesAverageErrorAsThreshold) {
  constexpr double kConfidence = 0.9;
  constexpr double kAverageError = 0.1;

  const std::vector<pins::GroupMember>& members = GetParam();
  std::vector<int> weights(members.size());
  for (const auto& member : members) weights[member.port - 1] = member.weight;
  std::string description =
      absl::StrCat("Weights: ", absl::StrJoin(weights, "|"));
  LOG(INFO) << description;
  SCOPED_TRACE(description);

  const int packet_count =
      ChiSquaredTestPacketCount(members.size(), kConfidence, kAverageError);

  Distribution expected_distribution =
      ExpectedDistribution(members, packet_count);
  Distribution actual_distribution =
      DistributionWithError(members, packet_count, kAverageError);

  EXPECT_THAT(
      CalculateChiSquaredResult(expected_distribution, actual_distribution)
          .p_value,
      DoubleNear(kConfidence, 0.07));
}

TEST_P(DistributionTest, CalculateAveragePercentErrorIsAccurate) {
  constexpr double kAverageError = 0.1;

  const std::vector<pins::GroupMember>& members = GetParam();

  std::vector<int> weights(members.size());
  for (const auto& member : members) weights[member.port - 1] = member.weight;
  std::string description =
      absl::StrCat("Weights: ", absl::StrJoin(weights, "|"));
  LOG(INFO) << description;
  SCOPED_TRACE(description);

  Distribution expected_distribution =
      ExpectedDistribution(members, 1000 * members.size());
  Distribution actual_distribution =
      DistributionWithError(members, 1000 * members.size(), kAverageError);

  EXPECT_THAT(
      CalculateAveragePercentError(expected_distribution, actual_distribution),
      DoubleNear(kAverageError, 0.003));
}

TEST_P(DistributionTest,
       ExpectDistributionPassesForChiSquaredValuesWithinThreshold) {
  constexpr double kActualError = 0.08;
  constexpr double kConfidence = 0.9;
  constexpr double kTargetError = 0.1;

  const std::vector<pins::GroupMember>& members = GetParam();

  std::vector<int> weights(members.size());
  for (const auto& member : members) weights[member.port - 1] = member.weight;
  std::string description =
      absl::StrCat("Weights: ", absl::StrJoin(weights, "|"));
  LOG(INFO) << description;
  SCOPED_TRACE(description);

  double target_packet_count =
      ChiSquaredTestPacketCount(members.size(), kConfidence, kTargetError);
  Distribution actual_distribution =
      DistributionWithError(members, target_packet_count, kActualError);
  EXPECT_OK(TestDistribution(members, actual_distribution, kConfidence,
                             PacketCount(actual_distribution),
                             Statistic::kChiSquared));
}

TEST_P(DistributionTest,
       ExpectDistributionFailsForChiSquaredValuesOutsideThreshold) {
  constexpr double kActualError = 0.2;
  constexpr double kConfidence = 0.9;
  constexpr double kTargetError = 0.1;

  const std::vector<pins::GroupMember>& members = GetParam();

  std::vector<int> weights(members.size());
  for (const auto& member : members) weights[member.port - 1] = member.weight;
  std::string description =
      absl::StrCat("Weights: ", absl::StrJoin(weights, "|"));
  LOG(INFO) << description;
  SCOPED_TRACE(description);

  double target_packet_count =
      ChiSquaredTestPacketCount(members.size(), kConfidence, kTargetError);
  Distribution actual_distribution =
      DistributionWithError(members, target_packet_count, kActualError);
  EXPECT_FALSE(TestDistribution(members, actual_distribution, kConfidence,
                                PacketCount(actual_distribution),
                                Statistic::kChiSquared)
                   .ok());
}

TEST_P(DistributionTest,
       ExpectDistributionPassesForPercentErrorValuesWithinThreshold) {
  constexpr double kActualError = 0.08;
  constexpr double kTargetError = 0.1;
  constexpr double kConfidence = 1 - kTargetError;

  const std::vector<pins::GroupMember>& members = GetParam();

  std::vector<int> weights(members.size());
  for (const auto& member : members) weights[member.port - 1] = member.weight;
  std::string description =
      absl::StrCat("Weights: ", absl::StrJoin(weights, "|"));
  LOG(INFO) << description;
  SCOPED_TRACE(description);

  double target_packet_count = 1000 * members.size();
  Distribution actual_distribution =
      DistributionWithError(members, target_packet_count, kActualError);
  EXPECT_OK(TestDistribution(members, actual_distribution, kConfidence,
                             PacketCount(actual_distribution),
                             Statistic::kPercentError));
}

TEST_P(DistributionTest,
       ExpectDistributionFailsForPercentErrorValuesOutsideThreshold) {
  constexpr double kActualError = 0.12;
  constexpr double kTargetError = 0.1;
  constexpr double kConfidence = 1 - kTargetError;

  const std::vector<pins::GroupMember>& members = GetParam();

  std::vector<int> weights(members.size());
  for (const auto& member : members) weights[member.port - 1] = member.weight;
  std::string description =
      absl::StrCat("Weights: ", absl::StrJoin(weights, "|"));
  LOG(INFO) << description;
  SCOPED_TRACE(description);

  double target_packet_count = 1000 * members.size();
  Distribution actual_distribution =
      DistributionWithError(members, target_packet_count, kActualError);
  EXPECT_FALSE(TestDistribution(members, actual_distribution, kConfidence,
                                PacketCount(actual_distribution),
                                Statistic::kPercentError)
                   .ok());
}

std::vector<std::vector<pins::GroupMember>> TestDistributions() {
  return {
      {
          {.weight = 1, .port = 1},
          {.weight = 2, .port = 2},
          {.weight = 3, .port = 3},
          {.weight = 1, .port = 4},
          {.weight = 5, .port = 5},
          {.weight = 4, .port = 6},
      },
      {
          {.weight = 1, .port = 1},
          {.weight = 1, .port = 2},
          {.weight = 1, .port = 3},
          {.weight = 1, .port = 4},
          {.weight = 1, .port = 5},
          {.weight = 1, .port = 6},
      },
  };
}

INSTANTIATE_TEST_SUITE_P(HashStats, DistributionTest,
                         testing::ValuesIn(TestDistributions()));

}  // namespace
}  // namespace pins_test
