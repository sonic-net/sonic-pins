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

#ifndef PINS_TESTS_FORWARDING_HASH_STATISTICS_UTIL_H_
#define PINS_TESTS_FORWARDING_HASH_STATISTICS_UTIL_H_

#include "absl/container/btree_map.h"
#include "absl/status/status.h"
#include "tests/forwarding/group_programming_util.h"

namespace pins_test {

// Statistical tests available for validating expected distributions.
enum class Statistic {
  kChiSquared,    // Chi-squared goodness of fit.
  kPercentError,  // Average percent error threshold.
};

// Represents the result of a chi-squared evaluation between two distributions.
struct ChiSquaredResult {
  double p_value;
  double chi_squared;
};

using Distribution = absl::btree_map<int /*member*/, double /*packets*/>;

// Chi-Squared test limits become tighter as the number of samples (packets)
// increases. This function helps target the sample count to a desired pass/fail
// threshold.
//
// Calculate the test packet count to make average_error the boundary for a
// chi-squared goodness-of-fit test.
// If the observed distribution, with N total packets, has an average error of
// average_error in each bucket (i.e. expected_packets * average_error), the
// p-value of the test will match the target confidence.
int ChiSquaredTestPacketCount(int members, double target_confidence,
                              double average_error);

// Return enough packets to generally hit all the weights multiple times.
// Bound the packets between 1k-10k to make sure we have enough differences and
// we don't take too much time. Always returns a multiple of total_weight.
int PercentErrorTestPacketCount(int total_weight);

// Calculate the chi_squared statistics for goodness of fit between the expected
// and actual distributions.
ChiSquaredResult CalculateChiSquaredResult(
    const Distribution& expected_distribution,
    const Distribution& actual_distribution);

// Calculate the percent error between the actual and expected distributions.
double CalculateAveragePercentError(const Distribution& expected_distribution,
                                    const Distribution& actual_distribution);

// Runs the specified statistical test to verify that the received packets match
// the expected member weights. Populates the calculated confidence and returns
// an error if the statistical test failed.
//
// Confidence is the threshold for declaring success / failure.
// * For ChiSquared tests, success is measured by confidence < p_value
// * For PercentError tests, success is when 1 - confidence > percent error
absl::Status TestDistribution(const std::vector<pins::GroupMember> &members,
                              const Distribution &results,
                              double target_confidence, int expected_packets,
                              Statistic statistic, double &actual_confidence);

// Same as above but does not return the calculated confidence.
inline absl::Status
TestDistribution(const std::vector<pins::GroupMember> &members,
                 const Distribution &results, double target_confidence,
                 int expected_packets, Statistic statistic) {
  double actual_confidence;
  return TestDistribution(members, results, target_confidence, expected_packets,
                          statistic, actual_confidence);
}

}  // namespace pins_test

#endif  // PINS_TESTS_FORWARDING_HASH_STATISTICS_UTIL_H_
