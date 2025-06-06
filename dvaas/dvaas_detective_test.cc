// NOTE: This test is a golden test (go/golden-test-with-coverage), NOT a
// typical unit test. Although this test may contain ASSERT and EXPECT
// statements to check certain properties, such statements are not required. The
// primary purpose of this test is to print golden output to a golden file. Any
// changes to the golden output will require the golden file to be updated.
// Golden file changes will be reviewed during CL review.

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

#include <fstream>
#include <iostream>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "dvaas/dvaas_detective.pb.h"
#include "dvaas/test_vector.pb.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "p4_infra/packetlib/packetlib.pb.h"
#include "yggdrasil_decision_forests/dataset/data_spec.pb.h"
#include "yggdrasil_decision_forests/model/decision_tree/decision_tree.h"
#include "yggdrasil_decision_forests/model/random_forest/random_forest.h"

namespace dvaas {
namespace dvaas_internal {
namespace {

namespace ydf = ::yggdrasil_decision_forests;

// Returns a random forest model with the following single decision tree:
//  ? expected(output packets) >= 1.5 # root non-leaf
//  |
//  +- T -> [fail : 0 passes, 5 fails] # multicast leaf
//  |
//  +- F -> ? [expected(packet-ins) >= 0.5] # unicast non-leaf
//          |
//          +- T -> [fail : 0 passes, 5 fails] # unicast w/ punt leaf
//          |
//          +- F -> [pass : 5 passes, 0 fails] # unicast w/o punt leaf
std::unique_ptr<ydf::model::random_forest::RandomForestModel>
CreateSkeletonRandomForestModel() {
  using ydf::model::decision_tree::NodeWithChildren;

  std::unique_ptr<ydf::model::random_forest::RandomForestModel> rf_model =
      std::make_unique<ydf::model::random_forest::RandomForestModel>();
  rf_model->set_data_spec(
      gutil::ParseProtoOrDie<ydf::dataset::proto::DataSpecification>(R"pb(
        columns { type: NUMERICAL name: "expected(output packets)" }
        columns { type: NUMERICAL name: "expected(packet-ins)" }
        columns {
          type: CATEGORICAL
          name: "test result"
          categorical {
            items {
              key: "<OOD>"
              value { index: 0 }
            }
            items {
              key: "pass"
              value { index: 1 count: 5 }
            }
            items {
              key: "fail"
              value { index: 2 count: 10 }
            }
          }
        }
      )pb"));
  rf_model->set_label_col_idx(2);

  std::unique_ptr<ydf::model::decision_tree::DecisionTree> tree =
      std::make_unique<ydf::model::decision_tree::DecisionTree>();
  {
    tree->CreateRoot();
    NodeWithChildren* root = tree->mutable_root();
    *root->mutable_node() =
        gutil::ParseProtoOrDie<ydf::model::decision_tree::proto::Node>(R"pb(
          condition {
            attribute: 0  # expected(output packets)
            condition { higher_condition { threshold: 1.5 } }
          }
        )pb");
    root->CreateChildren();
    NodeWithChildren* multicast_leaf_node = root->mutable_pos_child();
    *multicast_leaf_node->mutable_node() =
        gutil::ParseProtoOrDie<ydf::model::decision_tree::proto::Node>(R"pb(
          classifier {
            top_value: 2  # fail
            distribution {
              counts: 0  # <OOD>
              counts: 0  # passes
              counts: 5  # fails
              sum: 5
            }
          }
        )pb");
    NodeWithChildren* unicast_internal_node = root->mutable_neg_child();
    *unicast_internal_node->mutable_node() =
        gutil::ParseProtoOrDie<ydf::model::decision_tree::proto::Node>(R"pb(
          condition {
            attribute: 1  # expected(packet-ins)
            condition { higher_condition { threshold: 0.5 } }
          }
        )pb");
    unicast_internal_node->CreateChildren();
    NodeWithChildren* unicast_without_punt_leaf_node =
        unicast_internal_node->mutable_neg_child();
    *unicast_without_punt_leaf_node->mutable_node() =
        gutil::ParseProtoOrDie<ydf::model::decision_tree::proto::Node>(R"pb(
          classifier {
            top_value: 1  # pass
            distribution {
              counts: 0  # <OOD>
              counts: 5  # passes
              counts: 0  # fails
              sum: 5
            }
          }
        )pb");
    NodeWithChildren* unicast_with_punt_leaf_node =
        unicast_internal_node->mutable_pos_child();
    *unicast_with_punt_leaf_node->mutable_node() =
        gutil::ParseProtoOrDie<ydf::model::decision_tree::proto::Node>(R"pb(
          classifier {
            top_value: 2  # fail
            distribution {
              counts: 0  # <OOD>
              counts: 0  # passes
              counts: 5  # fails
              sum: 5
            }
          }
        )pb");
  }
  rf_model->AddTree(std::move(tree));
  return rf_model;
}

void ExtractExplanationFromModelTest() {
  // Print header.
  std::cout << std::string(80, '=') << "\n"
            << "ExtractExplanationFromModel Test\n"
            << std::string(80, '=') << "\n";
  // Print input.
  std::cout
      << "-- Input: RandomForestWithSingleTree  ----------------------------\n"
         "? [expected(output packets) >= 1.5] # root non-leaf\n"
         "|\n"
         "+- T -> [fail : 0 passes, 5 fails] # multicast leaf\n"
         "|\n"
         "+- F -> ? [expected(packet-ins) >= 0.5] # unicast non-leaf\n"
         "        |\n"
         "        +- T -> [fail : 0 passes, 5 fails] # unicast w/ punt leaf\n"
         "        |\n"
         "        +- F -> [pass : 5 passes, 0 fails] # unicast w/o punt leaf\n";

  std::unique_ptr<ydf::model::random_forest::RandomForestModel> rf_model =
      CreateSkeletonRandomForestModel();
  ASSERT_OK_AND_ASSIGN(DetectiveExplanation explanation,
                       ExtractExplanationFromModel(*rf_model));
  std::cout << "-- Output: DetectiveExplanation proto ----------------------\n";
  std::cout << gutil::PrintTextProto(explanation);
}

void DetectiveExplanationToStringTest() {
  std::vector<DetectiveExplanation> explanations = {
      gutil::ParseProtoOrDie<DetectiveExplanation>(
          R"pb(
            clusters {
              defining_property: "input ttl < 2"
              predicted_outcome_is_pass: true
              passing_tests: 50
              failing_tests: 50
              accuracy_of_predicted_outcome: .5
              coverage_for_predicted_outcome: 1
            }
          )pb"),
      gutil::ParseProtoOrDie<DetectiveExplanation>(
          R"pb(
            clusters {
              defining_property: "input ttl < 2"
              predicted_outcome_is_pass: false
              passing_tests: 50
              failing_tests: 50
              accuracy_of_predicted_outcome: .5
              coverage_for_predicted_outcome: 1
            }
          )pb"),
      gutil::ParseProtoOrDie<DetectiveExplanation>(
          R"pb(
            clusters {
              defining_property: "input ttl < 2"
              predicted_outcome_is_pass: true
              passing_tests: 25
              failing_tests: 25
              accuracy_of_predicted_outcome: .5
              coverage_for_predicted_outcome: .5
            }
            clusters {
              defining_property: "input ttl >= 2"
              predicted_outcome_is_pass: false
              passing_tests: 25
              failing_tests: 25
              accuracy_of_predicted_outcome: .5
              coverage_for_predicted_outcome: .5
            }
          )pb"),
      gutil::ParseProtoOrDie<DetectiveExplanation>(
          R"pb(
            clusters {
              defining_property: "expected(output packets) < 2"
              predicted_outcome_is_pass: true
              passing_tests: 1220
              failing_tests: 0
              accuracy_of_predicted_outcome: 1
              coverage_for_predicted_outcome: .82
            }
            clusters {
              defining_property: "expected(packet-ins) < 1"
              predicted_outcome_is_pass: true
              passing_tests: 256
              failing_tests: 0
              accuracy_of_predicted_outcome: 1
              coverage_for_predicted_outcome: .17
            }
            clusters {
              defining_property: "expected(output packets) >= 2 && expected(packet-ins) >= 1"
              predicted_outcome_is_pass: false
              passing_tests: 12
              failing_tests: 30
              accuracy_of_predicted_outcome: .6
              coverage_for_predicted_outcome: 1
            }
          )pb")};

  for (const auto& explanation : explanations) {
    // Print header.
    std::cout << std::string(80, '=') << "\n"
              << "DVaaS DetectiveExplanationToString Test\n"
              << std::string(80, '=') << "\n";

    // Print input.
    std::cout << "-- Input: DetectiveExplanation proto "
                 "-----------------------------\n";
    std::cout << gutil::PrintTextProto(explanation);

    // Print output.
    std::cout << "-- Output: DVAAS Detective String "
                 "--------------------------------\n";
    std::cout << DetectiveExplanationToString(explanation) << "\n";
  }
}

PacketTestOutcomes TestOutcomeToFeatureMapTestCases() {
  return gutil::ParseProtoOrDie<PacketTestOutcomes>(R"pb(
    # Passing with 1 punt and 1 output packet
    outcomes {
      test_run {
        test_vector {
          input {}
          acceptable_outputs {
            packets {}
            packet_ins {}
          }
        }
        actual_output {}
      }
      test_result {}
    }
    # Failing multicast
    outcomes {
      test_run {
        test_vector {
          input {}
          acceptable_outputs {
            packets {}
            packets {}
            packets {}
            packets {}
          }
        }
        actual_output {}
      }
      test_result { failure {} }
    }
    # Pasing WCMP
    outcomes {
      test_run {
        test_vector {
          input {}
          acceptable_outputs {}
          acceptable_outputs {}
          acceptable_outputs {}
          acceptable_outputs {}
          acceptable_outputs {}
        }
        actual_output {}
      }
      test_result {}
    }
    # Pasing WCMP with varying number packets and packet-ins.
    outcomes {
      test_run {
        test_vector {
          input {}
          acceptable_outputs {
            packets {}
            packet_ins {}
            packet_ins {}
          }
          acceptable_outputs {
            packets {}
            packets {}
            packets {}
            packet_ins {}
          }
        }
        actual_output {}
      }
      test_result {}
    }
  )pb");
}

void TestOutcomeToFeatureMapTest(const PacketTestOutcome& test_outcome) {
  // Print header.
  std::cout << std::string(80, '=') << "\n"
            << "TestOutcomeToFeatureMap Test\n"
            << std::string(80, '=') << "\n";

  // Print input.
  std::cout
      << "-- Input: PacketTestOutcome proto --------------------------------\n";
  std::cout << gutil::PrintTextProto(test_outcome);

  // Print output.
  std::cout
      << "-- Output: Feature Map -------------------------------------------\n";
  // Sort map for determinism.
  absl::flat_hash_map<std::string, FeatureValue> feature_map =
      TestOutcomeToFeatureMap(test_outcome);
  // Check that GetListOfFeatureNames() is consistent with
  // TestOutcomeToFeatureMap() and use GetListOfFeatureNames() to print in a
  // deterministic order.
  ASSERT_EQ(feature_map.size(), GetListOfFeatureNames().size());
  for (const auto& feature_name : GetListOfFeatureNames()) {
    ASSERT_TRUE(feature_map.contains(feature_name));
    std::cout << feature_name << ": "
              << FeatureValueToString(feature_map.at(feature_name)) << "\n";
  }
  std::cout << "\n";
}

void WriteCsvFileFromPacketTestOutcomesTest() {
  PacketTestOutcomes test_outcomes = TestOutcomeToFeatureMapTestCases();
  // Create and write to temporary file
  ASSERT_OK_AND_ASSIGN(std::string csv_file_path,
                       WriteTempCsvFileFromPacketTestOutcomes(test_outcomes));

  // Print header.
  std::cout << std::string(80, '=') << "\n"
            << "WriteCsvFileFromPacketTestOutcomes Test\n"
            << std::string(80, '=') << "\n";

  // Print input.
  std::cout
      << "-- Input: PacketTestOutcomes proto -------------------------------\n";
  std::cout << gutil::PrintTextProto(test_outcomes);

  // Print output.
  std::cout
      << "-- Output: Contents of CSV file ----------------------------------\n";
  std::ifstream csv_ifstream(csv_file_path);
  ASSERT_TRUE(csv_ifstream.is_open());
  std::string csv_row;
  while (std::getline(csv_ifstream, csv_row)) {
    std::cout << csv_row << "\n";
  }
  csv_ifstream.close();
}

// This test is a golden test and not a typical unit test. The TEST unit serves
// as an entry point for calling functions that produce golden output. Different
// functions produce different portions of the golden output. All golden
// functions are called from a single TEST unit to avoid non-determinism in the
// output.
TEST(DvaasDetectiveTest, GoldenTest) {
  PacketTestOutcomes test_outcomes = TestOutcomeToFeatureMapTestCases();
  for (const auto& test_outcome : test_outcomes.outcomes()) {
    TestOutcomeToFeatureMapTest(test_outcome);
  }

  WriteCsvFileFromPacketTestOutcomesTest();

  ExtractExplanationFromModelTest();

  DetectiveExplanationToStringTest();
}

// Support for multiple trees is not implemented.
TEST(DvaasDetectiveTest, DoesNotSupportModelsWithMultipleTrees) {
  std::unique_ptr<ydf::model::random_forest::RandomForestModel>
      rf_model_with_multiple_trees = CreateSkeletonRandomForestModel();
  rf_model_with_multiple_trees->AddTree(
      std::make_unique<ydf::model::decision_tree::DecisionTree>());
  EXPECT_THAT(ExtractExplanationFromModel(*rf_model_with_multiple_trees),
              gutil::StatusIs(absl::StatusCode::kUnimplemented));
}

}  // namespace
}  // namespace dvaas_internal
}  // namespace dvaas
