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

#include "dvaas/dvaas_detective.h"

#include <algorithm>
#include <string>
#include <variant>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/types/variant.h"
#include "dvaas/dvaas_detective.pb.h"
#include "dvaas/test_vector.pb.h"
#include "gutil/overload.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"

namespace dvaas {
namespace dvaas_internal {

namespace {

std::string DetectiveClusterToString(const DetectiveCluster& cluster,
                                     float total_predicted_outcomes) {
  bool passed = cluster.predicted_outcome();
  return absl::Substitute(
      "* $0 -> $1\n"
      "  * accuracy: $2%, with $3 exceptions that $4 instead\n"
      "  * coverage: $5%, accounting for $6/$7 $8 test vectors\n",
      cluster.defining_property(), passed ? "pass" : "fail",
      cluster.accuracy_of_predicted_outcome() * 100,
      passed ? cluster.failing_tests() : cluster.passing_tests(),
      passed ? "fail" : "pass", cluster.coverage_for_predicted_outcome() * 100,
      passed ? cluster.passing_tests() : cluster.failing_tests(),
      total_predicted_outcomes, passed ? "passing" : "failing");
}

}  // namespace

std::string FeatureValueToString(const FeatureValue& value) {
  return absl::visit(
      gutil::Overload{
          [](const NumericalValue& num) { return absl::StrCat(num); },
          [](const CategoricalValue& str) { return str; }},
      value);
}

absl::flat_hash_map<std::string, FeatureValue> TestOutcomeToFeatureMap(
    const PacketTestOutcome& test_outcome) {
  absl::flat_hash_map<std::string, FeatureValue> result;

  // Feature extraction is scoped to ensure the extraction of one set of
  // features is independent of the extraction of another set. If this function
  // becomes too large, scoped blocks should be refactored into functions.
  {
    int num_expected_output_packets = 0;
    int num_expected_packet_ins = 0;
    for (const auto& output :
         test_outcome.test_run().test_vector().acceptable_outputs()) {
      num_expected_output_packets =
          std::max(num_expected_output_packets, output.packets_size());
      num_expected_packet_ins =
          std::max(num_expected_packet_ins, output.packet_ins_size());
    }
    result["# expected output packets"] =
        static_cast<float>(num_expected_output_packets);
    result["# expected punted packets"] =
        static_cast<float>(num_expected_packet_ins);
  }

  result["# acceptable behaviors according to P4 simulation"] =
      static_cast<float>(
          test_outcome.test_run().test_vector().acceptable_outputs_size());
  result["test result"] =
      test_outcome.test_result().has_failure() ? "fail" : "pass";

  return result;
}

std::string DetectiveExplanationToString(
    const DetectiveExplanation& explanation) {
  std::vector<int> passing_indices;
  std::vector<int> failing_indices;
  float total_passing_outcomes = 0;
  float total_failing_outcomes = 0;
  for (int i = 0; i < explanation.clusters_size(); ++i) {
    const DetectiveCluster& cluster = explanation.clusters(i);
    if (explanation.clusters(i).predicted_outcome()) {
      passing_indices.push_back(i);
    } else {
      failing_indices.push_back(i);
    }
    total_passing_outcomes += cluster.passing_tests();
    total_failing_outcomes += cluster.failing_tests();
  }

  std::string result;
  // Reserve string size with a rough estimate to avoid unnecessary copying
  // during append operations.
  result.reserve(250 * explanation.clusters_size());

  float unaccounted_passing_outcomes = total_passing_outcomes;
  float unaccounted_passing_coverage = 1.0;
  result.append(
      "DVaaS Detective: Found the following pattern(s) among passing test "
      "vectors:\n");
  for (auto passing_index : passing_indices) {
    const DetectiveCluster& cluster = explanation.clusters(passing_index);
    result.append(DetectiveClusterToString(explanation.clusters(passing_index),
                                           total_passing_outcomes));
    unaccounted_passing_outcomes -= cluster.passing_tests();
    unaccounted_passing_coverage -= cluster.coverage_for_predicted_outcome();
  }
  result.append(unaccounted_passing_coverage == 0
                    ? "* All passing test vectors accounted for\n"
                    : absl::Substitute(
                          "* $0 passing test vectors unaccounted for ($1%)\n",
                          unaccounted_passing_outcomes,
                          unaccounted_passing_coverage * 100));

  float unaccounted_failing_outcomes = total_failing_outcomes;
  float unaccounted_failing_coverage = 1.0;
  result.append(
      "\nDVaaS Detective: Found the following pattern(s) among failing test "
      "vectors:\n");
  for (auto failing_index : failing_indices) {
    const DetectiveCluster& cluster = explanation.clusters(failing_index);
    result.append(DetectiveClusterToString(explanation.clusters(failing_index),
                                           total_failing_outcomes));
    unaccounted_failing_outcomes -= cluster.failing_tests();
    unaccounted_failing_coverage -= cluster.coverage_for_predicted_outcome();
  }
  result.append(unaccounted_failing_coverage == 0
                    ? "* All failing test vectors accounted for\n"
                    : absl::Substitute(
                          "* $0 failing test vectors unaccounted for ($1%)\n",
                          unaccounted_failing_outcomes,
                          unaccounted_failing_coverage * 100));

  return result;
}

}  // namespace dvaas_internal
}  // namespace dvaas
