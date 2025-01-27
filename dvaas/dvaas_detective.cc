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
#include <cstdio>
#include <fstream>
#include <optional>
#include <string>
#include <variant>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/types/variant.h"
#include "dvaas/dvaas_detective.pb.h"
#include "dvaas/test_vector.pb.h"
#include "gutil/gutil/overload.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status.h"
#include "p4_infra/p4_pdpi/netaddr/ipv4_address.h"
#include "p4_infra/p4_pdpi/netaddr/ipv6_address.h"
#include "p4_infra/p4_pdpi/netaddr/mac_address.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_infra/p4_pdpi/string_encodings/hex_string.h"
#include "yggdrasil_decision_forests/dataset/data_spec.h"
#include "yggdrasil_decision_forests/dataset/data_spec.pb.h"
#include "yggdrasil_decision_forests/model/decision_tree/decision_tree.h"
#include "yggdrasil_decision_forests/model/decision_tree/decision_tree.pb.h"
#include "yggdrasil_decision_forests/model/random_forest/random_forest.h"
#include "yggdrasil_decision_forests/utils/distribution.pb.h"

namespace dvaas {
namespace dvaas_internal {

namespace ydf = ::yggdrasil_decision_forests;
using ydf::model::random_forest::RandomForestModel;

namespace {

using ydf::dataset::proto::DataSpecification;

// In order to train our model, we must specify a label. For the most part, a
// label is just another categorical feature, except the model classifies data
// based on that feature. For example:
//  - Categorical feature F can have value X, Y, or Z
//  - Feature F is designated as the label
//  - Therefore, the model classifies data as either X, Y, or Z
// Our code mostly treats the label like any other feature, but with a fixed
// feature name and values defined by the constants below.
constexpr absl::string_view kTestResultFeatureName = "test result";
constexpr absl::string_view kPassTestResultFeatureValue = "pass";
constexpr absl::string_view kFailTestResultFeatureValue = "fail";

// Feature names used by DVaaS Detective.
constexpr absl::string_view kExpectedOutputPacketsFeatureName =
    "# expected output packets";
constexpr absl::string_view kExpectedPuntedPacketsFeatureName =
    "# expected punted packets";
constexpr absl::string_view kAcceptableBehaviorsFeatureName =
    "# acceptable switch behaviors according to P4 simulation";

std::string DetectiveClusterToString(const DetectiveCluster& cluster,
                                     float total_predicted_outcomes) {
  bool passed = cluster.predicted_outcome_is_pass();
  return absl::StrFormat(
      "* %s -> %s\n"
      "  * accuracy: %.0f%%, %.0f out of %.0f test vectors that match the "
      "conditions %s (remaining %.0f %s instead)\n"
      "  * coverage: %.0f%%, accounting for %.0f out of %.0f %s test vectors\n",
      cluster.defining_property().empty() ? "<no conditions>"
                                          : cluster.defining_property(),
      passed ? "pass" : "fail", cluster.accuracy_of_predicted_outcome() * 100,
      passed ? cluster.passing_tests() : cluster.failing_tests(),
      cluster.passing_tests() + cluster.failing_tests(),
      passed ? "pass" : "fail",
      passed ? cluster.failing_tests() : cluster.passing_tests(),
      passed ? "fail" : "pass", cluster.coverage_for_predicted_outcome() * 100,
      passed ? cluster.passing_tests() : cluster.failing_tests(),
      total_predicted_outcomes, passed ? "passing" : "failing");
}

// Return a `DetectiveCluster` created from leaf `node`:
//  - `criteria` is list of branching decisions made at internal nodes (e.g.
//    {"var X >= 12", "var Y < 2"}) corresponding to the path from root to
//    `node`.
//  - `data_spec` contains information for interpreting `node`.
absl::StatusOr<DetectiveCluster> MakeCluster(
    const std::vector<std::string>& criteria,
    const ydf::model::decision_tree::proto::Node& node,
    const DataSpecification& data_spec) {
  DetectiveCluster cluster;
  cluster.set_defining_property(absl::StrJoin(criteria, " && "));

  // `node` contains a distribution over the possible outcomes (i.e. pass or
  // fail). We need to know the index of the pass and fail outcomes in the
  // distribution in order to interpret the outcome of `node`. It's possible
  // that the distribution does not contain a pass or fail outcome, in which
  // case we set the corresponding index to nullopt.
  std::optional<int> pass_index;
  std::optional<int> fail_index;
  for (const ydf::dataset::proto::Column& column : data_spec.columns()) {
    if (column.name() != kTestResultFeatureName) continue;

    for (const auto& [name, info] : column.categorical().items()) {
      if (name == kPassTestResultFeatureValue) {
        pass_index = info.index();
      }
      if (name == kFailTestResultFeatureValue) {
        fail_index = info.index();
      }
    }
  }
  if (!pass_index.has_value() && !fail_index.has_value()) {
    return absl::InternalError(
        absl::StrCat("Node has neither passing nor failing tests: ",
                     gutil::PrintTextProto(node)));
  }

  // Outcome is the output of the model (i.e. for data X, we predict outcome Y).
  // For a `node`, the outcome is the top value in the `node`'s distribution.
  // We expect the outcome to be either pass or fail.
  int outcome_value_index = node.classifier().top_value();
  if (pass_index.has_value() && outcome_value_index == *pass_index) {
    cluster.set_predicted_outcome_is_pass(true);
  } else if (fail_index.has_value() && outcome_value_index == *fail_index) {
    cluster.set_predicted_outcome_is_pass(false);
  } else {
    return absl::InternalError(absl::StrCat("Node has unexpected outcome: ",
                                            gutil::PrintTextProto(node)));
  }
  cluster.set_passing_tests(
      pass_index.has_value()
          ? node.classifier().distribution().counts(*pass_index)
          : 0);
  cluster.set_failing_tests(
      fail_index.has_value()
          ? node.classifier().distribution().counts(*fail_index)
          : 0);
  cluster.set_accuracy_of_predicted_outcome(
      node.classifier().distribution().counts(outcome_value_index) /
      node.classifier().distribution().sum());
  return cluster;
}

// Recursively extract `DetectiveCluster`s from `node`.
//  - `data_spec` contains information about the features used in the model.
//  - `criteria` is used to keep track of the path from the root to `node`.
//  - `clusters` are appended when leaf nodes are reached.
absl::Status ExtractClustersRecursivey(
    const ydf::model::decision_tree::NodeWithChildren& node,
    const DataSpecification& data_spec, std::vector<std::string> criteria,
    std::vector<DetectiveCluster>& clusters) {
  using ydf::model::decision_tree::proto::Condition;
  using ydf::model::decision_tree::proto::NodeCondition;

  if (node.IsLeaf()) {
    ASSIGN_OR_RETURN(clusters.emplace_back(),
                     MakeCluster(criteria, node.node(), data_spec));
    return absl::OkStatus();
  }

  // Create criteria for branches of this node.
  NodeCondition condition = node.node().condition();
  const absl::string_view attribute_name =
      data_spec.columns(node.node().condition().attribute()).name();
  std::string pos_criteria;
  std::string neg_criteria;
  switch (condition.condition().type_case()) {
    // Condition for numerical features.
    case Condition::kHigherCondition: {
      float threshold = condition.condition().higher_condition().threshold();
      pos_criteria = absl::StrCat(attribute_name, " >= ", threshold);
      neg_criteria = absl::StrCat(attribute_name, " < ", threshold);
      break;
    }
    // Condition for categorical features.
    case Condition::kContainsCondition:
    // Condition for boolean features.
    case Condition::kTrueValueCondition:
    // Other conditions we are not currently interested in.
    case Condition::kNaCondition:
    case Condition::kContainsBitmapCondition:
    case Condition::kDiscretizedHigherCondition:
    case Condition::kObliqueCondition:
    default:
      return absl::InternalError(absl::StrCat(
          "Unsupported condition type: ", gutil::PrintTextProto(condition)));
  };

  // Positive branch.
  criteria.push_back(pos_criteria);
  RETURN_IF_ERROR(ExtractClustersRecursivey(*node.pos_child(), data_spec,
                                            criteria, clusters));
  criteria.pop_back();

  // Negative branch.
  criteria.push_back(neg_criteria);
  return ExtractClustersRecursivey(*node.neg_child(), data_spec, criteria,
                                   clusters);
}

}  // namespace

std::string FeatureValueToString(const FeatureValue& value) {
  return absl::visit(
      gutil::Overload{
          [](const NumericalValue& num) { return absl::StrCat(num); },
          [](const CategoricalValue& str) { return str; }},
      value);
}

std::vector<absl::string_view> GetListOfFeatureNames() {
  return {
      kExpectedOutputPacketsFeatureName,
      kExpectedPuntedPacketsFeatureName,
      kAcceptableBehaviorsFeatureName,
      kTestResultFeatureName,
  };
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
    result[kExpectedOutputPacketsFeatureName] =
        static_cast<float>(num_expected_output_packets);
    result[kExpectedPuntedPacketsFeatureName] =
        static_cast<float>(num_expected_packet_ins);
  }

  result[kAcceptableBehaviorsFeatureName] = static_cast<float>(
      test_outcome.test_run().test_vector().acceptable_outputs_size());
  result[kTestResultFeatureName] =
      test_outcome.test_result().has_failure()
          ? std::string(kFailTestResultFeatureValue)
          : std::string(kPassTestResultFeatureValue);

  return result;
}

absl::StatusOr<std::string> WriteTempCsvFileFromPacketTestOutcomes(
    const PacketTestOutcomes& test_outcomes) {
  // Create CSV rows.
  std::vector<absl::string_view> ordered_feature_names =
      GetListOfFeatureNames();
  std::vector<std::string> csv_rows;
  csv_rows.reserve(1 + test_outcomes.outcomes_size());
  csv_rows.push_back(absl::StrJoin(ordered_feature_names, ","));
  for (const auto& test_outcome : test_outcomes.outcomes()) {
    absl::flat_hash_map<std::string, FeatureValue> feature_map =
        TestOutcomeToFeatureMap(test_outcome);
    std::vector<std::string> ordered_feature_values;
    ordered_feature_values.reserve(ordered_feature_names.size());
    for (const auto& feature_name : ordered_feature_names) {
      ordered_feature_values.push_back(
          FeatureValueToString(feature_map[feature_name]));
    }
    csv_rows.push_back(absl::StrJoin(ordered_feature_values, ","));
  }

  // Write CSV file.
  char* tmp_file = std::tmpnam(nullptr);
  if (tmp_file == nullptr) {
    return absl::InternalError("Failed to create temporary file.");
  }
  std::ofstream(tmp_file) << absl::StrJoin(csv_rows, "\n");
  return tmp_file;
}

absl::StatusOr<DetectiveExplanation> ExtractExplanationFromModel(
    const RandomForestModel& rf_model) {
  if (rf_model.NumTrees() != 1) {
    return absl::UnimplementedError(
        absl::StrCat("We only support explanation extraction for models with "
                     "exactly one tree. Model has ",
                     rf_model.NumTrees(), " trees."));
  }

  // Extract clusters from the decision tree.
  std::vector<DetectiveCluster> clusters;
  RETURN_IF_ERROR(ExtractClustersRecursivey(
      rf_model.decision_trees().at(0)->root(), rf_model.data_spec(),
      /*criteria=*/{}, clusters));

  // Initialize explanation and add coverage information.
  DetectiveExplanation explanation;
  *explanation.mutable_clusters() = {clusters.begin(), clusters.end()};
  float total_passing = 0;
  float total_failing = 0;
  for (const auto& [name, info] :
       rf_model.LabelColumnSpec().categorical().items()) {
    if (name == kPassTestResultFeatureValue) {
      total_passing = info.count();
    }
    if (name == kFailTestResultFeatureValue) {
      total_failing = info.count();
    }
  }
  for (DetectiveCluster& cluster : *explanation.mutable_clusters()) {
    if (cluster.predicted_outcome_is_pass() && total_passing != 0) {
      cluster.set_coverage_for_predicted_outcome(cluster.passing_tests() /
                                                 total_passing);
    }
    if (!cluster.predicted_outcome_is_pass() && total_failing != 0) {
      cluster.set_coverage_for_predicted_outcome(cluster.failing_tests() /
                                                 total_failing);
    }
  }
  return explanation;
}

std::string DetectiveExplanationToString(
    const DetectiveExplanation& explanation) {
  std::vector<int> passing_indices;
  std::vector<int> failing_indices;
  float total_passing_outcomes = 0;
  float total_failing_outcomes = 0;
  for (int i = 0; i < explanation.clusters_size(); ++i) {
    const DetectiveCluster& cluster = explanation.clusters(i);
    if (explanation.clusters(i).predicted_outcome_is_pass()) {
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
