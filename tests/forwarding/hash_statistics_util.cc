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

#include <cmath>
#include <string>
#include <vector>

#include "absl/container/btree_map.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_join.h"
#include "absl/strings/substitute.h"
#include "boost/math/distributions/chi_squared.hpp"  // IWYU pragma: keep
#include "gutil/gutil/collections.h"
#include "gutil/gutil/status.h"
#include "tests/forwarding/group_programming_util.h"

namespace pins_test {
namespace {

// Describe the distribution test result in the following format:
//     Port:     1    2    3    4    ...
// ---------
//   Weight:     1    8    4    2    ...
// Expected:   100  800  400  200    ...
//   Actual:   102  798  405  195    ...
std::string DescribeResults(const std::vector<pins::GroupMember>& members,
                            const Distribution& expected_packets_per_port,
                            const Distribution& received_packets_per_port) {
  absl::btree_map<int, int> weight_map;
  for (const auto& member : members) {
    weight_map[member.port] = member.weight;
  }

  std::vector<std::string> ports, weights, expected, actual;
  for (const auto& [port, expected_count] : expected_packets_per_port) {
    ports.push_back(absl::StrFormat("%4d", port));
    weights.push_back(
        absl::StrFormat("%4d", gutil::FindOrDefault(weight_map, port, 0)));
    expected.push_back(absl::StrFormat("%4d", std::lround(expected_count)));
    actual.push_back(absl::StrFormat(
        "%4d",
        std::lround(gutil::FindOrDefault(received_packets_per_port, port, 0))));
  }
  return absl::Substitute(
      R"(
    Port: $0
---------
  Weight: $1
Expected: $2
  Actual: $3
)",
      absl::StrJoin(ports, " "), absl::StrJoin(weights, " "),
      absl::StrJoin(expected, " "), absl::StrJoin(actual, " "));
}

}  // namespace

// The formula for chi_squared is calculation is:
//   Sum of [ (observed - expected) ^ 2 / expected ] for each bucket.
//
// When introducing the average error, we have the following extra properties:
//   * observed_n - expected_n = expected_n * avg_err
//   * Sum[expected_n] = packets
//
// Then, we can do the following reduction:
//   Sum[(observed - expected)^2 / expected]_n = chi_squared
//   Sum[(avg_err * expected_n)^2 / expected_n] = chi_squared
//   Sum[avg_err^2 * expected_n) = chi_squared
//   avg_err^2 * Sum[expected_n] = chi_squared
//   avg_err^2 * packets = chi_squared
//   packets = chi_squared / avg_err^2
//
// Any distribution with a larger chi_squared value is expected to fail.
int ChiSquaredTestPacketCount(int members, double target_confidence,
                              double average_error) {
  const int degrees_of_freedom = members - 1;
  double chi_squared_limit = boost::math::quantile(
      boost::math::chi_squared(degrees_of_freedom), 1 - target_confidence);
  return chi_squared_limit / average_error / average_error + /*rounding*/ 0.5;
}

int PercentErrorTestPacketCount(int total_weight) {
  int packet_count = 100 * total_weight;
  // Choose the first multiple of packet_count > 1,000
  if (packet_count < 1000)
    return 1000 - 1000 % total_weight + total_weight;
  // Choose the last multiple of packet_count < 10,000
  if (packet_count > 10000)
    return 10000 - 10000 % total_weight;
  return packet_count;
}

ChiSquaredResult CalculateChiSquaredResult(
    const Distribution& expected_distribution,
    const Distribution& actual_distribution) {
  double chi_squared = 0;
  for (const auto& [bucket, expected_count] : expected_distribution) {
    int actual_count = gutil::FindOrDefault(actual_distribution, bucket, 0);
    if (actual_count == 0) {
      LOG(WARNING) << "No packets were found for bucket: " << bucket;
    }
    double delta = actual_count - expected_count;
    chi_squared += delta * delta / expected_count;
  }
  const int degrees_of_freedom = expected_distribution.size() - 1;
  double p_value =
      1.0 - (boost::math::cdf(boost::math::chi_squared(degrees_of_freedom),
                              chi_squared));
  return {.p_value = p_value, .chi_squared = chi_squared};
}

double CalculateAveragePercentError(const Distribution& expected_distribution,
                                    const Distribution& actual_distribution) {
  double total_percent_error = 0;
  for (const auto& [bucket, expected_count] : expected_distribution) {
    int actual_count = gutil::FindOrDefault(actual_distribution, bucket, 0);
    if (actual_count == 0) {
      LOG(WARNING) << "No packets were found for bucket: " << bucket;
    }
    double delta = actual_count > expected_count
                       ? actual_count - expected_count
                       : expected_count - actual_count;
    total_percent_error += delta / expected_count;
  }
  return total_percent_error / expected_distribution.size();
}

absl::Status TestDistribution(const std::vector<pins::GroupMember> &members,
                              const Distribution &results,
                              double target_confidence, int expected_packets,
                              Statistic statistic, double &actual_confidence) {
  int total_weight = 0;
  for (const auto& member : members) {
    total_weight += member.weight;
  }
  Distribution expected_distribution;
  for (const auto& member : members) {
    expected_distribution[member.port] =
        static_cast<double>(expected_packets) * member.weight / total_weight;
  }

  std::string description =
      DescribeResults(members, expected_distribution, results);
  LOG(INFO) << description;

  int actual_packets = 0;
  for (const auto& [member, packets] : results) {
    actual_packets += packets;
  }
  if (actual_packets != expected_packets) {
    return gutil::InternalErrorBuilder()
           << "Number of received packets (" << actual_packets
           << ") does not match the expected packets (" << expected_packets
           << ").";
  }

  switch (statistic) {
    case Statistic::kChiSquared: {
      auto [p_value, chi_squared] =
          CalculateChiSquaredResult(expected_distribution, results);
      actual_confidence = p_value;
      LOG(INFO) << absl::StrCat("p-value: ", p_value,
                                " | chi^2: ", chi_squared);
      if (p_value <= target_confidence) {
        return gutil::InternalErrorBuilder()
               << "We have less than "
               << absl::StreamFormat("%3f%%", target_confidence * 100)
               << " confidence that the actual distribution matches the "
                  "expected "
               << "distribution. "
               << "p_value: " << p_value << " chi^2: " << chi_squared << "\n"
               << description;
      }
    } break;
    case Statistic::kPercentError: {
      double percent_error =
          CalculateAveragePercentError(expected_distribution, results);
      actual_confidence = 1 - percent_error;
      LOG(INFO) << absl::StreamFormat("Average percent error: %3.4f%%",
                                      percent_error * 100);
      double error_threshold = 1 - target_confidence;
      if (percent_error > error_threshold) {
        return gutil::InternalErrorBuilder()
               << absl::StreamFormat(
                      "Average percent error (%3.4f%%) is higher than the "
                      "limit "
                      "(%3f%%).\n",
                      percent_error * 100, error_threshold * 100)
               << description;
      }
    } break;
    default:
      return absl::InvalidArgumentError("Received unsupported statistic");
  }
  return absl::OkStatus();
}

}  // namespace pins_test
