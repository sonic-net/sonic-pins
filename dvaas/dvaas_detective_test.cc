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

#include <iostream>
#include <string>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "dvaas/dvaas_detective.pb.h"
#include "dvaas/test_vector.pb.h"
#include "gtest/gtest.h"
#include "gutil/proto.h"
#include "gutil/testing.h"
#include "p4_pdpi/internal/ordered_map.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"

namespace dvaas {
namespace dvaas_internal {
namespace {

void DetectiveExplanationToStringTest() {
  std::vector<DetectiveExplanation> explanations = {
      gutil::ParseProtoOrDie<DetectiveExplanation>(
          R"pb(
            clusters {
              defining_property: "input ttl < 2"
              predicted_outcome: true
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
              predicted_outcome: false
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
              predicted_outcome: true
              passing_tests: 25
              failing_tests: 25
              accuracy_of_predicted_outcome: .5
              coverage_for_predicted_outcome: .5
            }
            clusters {
              defining_property: "input ttl >= 2"
              predicted_outcome: false
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
              predicted_outcome: true
              passing_tests: 1220
              failing_tests: 0
              accuracy_of_predicted_outcome: 1
              coverage_for_predicted_outcome: .82
            }
            clusters {
              defining_property: "expected(packet-ins) < 1"
              predicted_outcome: true
              passing_tests: 256
              failing_tests: 0
              accuracy_of_predicted_outcome: 1
              coverage_for_predicted_outcome: .17
            }
            clusters {
              defining_property: "expected(output packets) >= 2 && expected(packet-ins) >= 1"
              predicted_outcome: false
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
  for (const auto& [key, value] : Ordered(feature_map)) {
    std::cout << key << ": " << FeatureValueToString(value) << "\n";
  }
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

  DetectiveExplanationToStringTest();
}

}  // namespace
}  // namespace dvaas_internal
}  // namespace dvaas
