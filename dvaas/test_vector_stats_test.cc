// Copyright 2024 Google LLC
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

#include "dvaas/test_vector_stats.h"

#include <iostream>

#include "dvaas/test_vector.pb.h"
#include "gtest/gtest.h"
#include "gutil/gutil/testing.h"

namespace dvaas {
namespace {

PacketTestOutcomes GetPacketTestOutcomes() {
  return gutil::ParseProtoOrDie<PacketTestOutcomes>(R"pb(
    # Correct drop.
    outcomes {
      test_run {
        test_vector {
          input {}
          # Deterministic drop.
          acceptable_outputs {
            packets: []
            packet_ins: []
          }
        }
        actual_output {
          packets: []
          packet_ins: []
        }
      }
      # Passed.
      test_result {}
    }

    # Incorrect forward.
    outcomes {
      test_run {
        test_vector {
          input {}
          # Deterministic forward.
          acceptable_outputs {
            packets {}
            packet_ins: []
          }
        }
        actual_output {
          packets {}
          packet_ins: []
        }
      }
      # Failed.
      test_result {
        failure { minimization_analysis { reproducibility_rate: 0.0 } }
      }
    }

    # Correct forward.
    outcomes {
      test_run {
        test_vector {
          input {}
          # Deterministic forward.
          acceptable_outputs {
            packets {}
            packet_ins: []
          }
        }
        actual_output {
          packets {}
          packet_ins: []
        }
      }
      # Passed.
      test_result {}
    }

    # Correct multi forward.
    outcomes {
      test_run {
        test_vector {
          input {}
          # Deterministic multi forward.
          acceptable_outputs {
            packets {}
            packets {}
            packets {}
            packet_ins: []
          }
        }
        actual_output {
          packets {}
          packets {}
          packets {}
          packet_ins: []
        }
      }
      # Passed.
      test_result {}
    }

    # Incorrect punt.
    outcomes {
      test_run {
        test_vector {
          input {}
          # Deterministic trap.
          acceptable_outputs {
            packets: []
            packet_ins {}
          }
        }
        actual_output {
          packets: []
          packet_ins: {}
        }
      }
      # Failed.
      test_result {
        failure { minimization_analysis { reproducibility_rate: 0.0 } }
      }
    }

    # Incorrect punt with no reproducibility rate.
    outcomes {
      test_run {
        test_vector {
          input {}
          # Deterministic trap.
          acceptable_outputs {
            packets: []
            packet_ins {}
          }
        }
        actual_output {
          packets: []
          packet_ins: {}
        }
      }
      # Failed.
      test_result { failure {} }
    }

    # Correct forward & copy.
    outcomes {
      test_run {
        test_vector {
          input {}
          # Deterministic forward & copy.
          acceptable_outputs {
            packets {}
            packet_ins {}
          }
        }
        actual_output {
          packets {}
          packet_ins: {}
        }
      }
      # Passed.
      test_result {
          # No reproducibility rate is given.
      }
    }
  )pb");
}

TEST(TestVectorStatsGoldenTest,
     ComputeTestVectorStatsAndExplainTestVectorStats) {
  PacketTestOutcomes outcomes = GetPacketTestOutcomes();
  TestVectorStats stats = ComputeTestVectorStats(outcomes);
  std::cout << ExplainTestVectorStats(stats);
}

TEST(TestVectorStatsGoldenTest, ReproducibilityRateScenarios) {
  PacketTestOutcomes outcomes = GetPacketTestOutcomes();
  outcomes.mutable_outcomes(1)
      ->mutable_test_result()
      ->mutable_failure()
      ->mutable_minimization_analysis()
      ->set_reproducibility_rate(1.0);
  outcomes.mutable_outcomes(4)
      ->mutable_test_result()
      ->mutable_failure()
      ->mutable_minimization_analysis()
      ->set_reproducibility_rate(1.0);
  TestVectorStats stats = ComputeTestVectorStats(outcomes);
  std::cout << ExplainTestVectorStats(stats);

  outcomes.mutable_outcomes(4)
      ->mutable_test_result()
      ->mutable_failure()
      ->mutable_minimization_analysis()
      ->set_reproducibility_rate(0.0);
  stats = ComputeTestVectorStats(outcomes);
  std::cout << ExplainTestVectorStats(stats);
}

TEST(TestVectorStatsGoldenTest,
     ComputeTestVectorStatsPerLabelAndExplainPerLabelStats) {
  auto outcomes = gutil::ParseProtoOrDie<PacketTestOutcomes>(R"pb(
    outcomes {
      test_run {
        test_vector {
          input {}
          acceptable_outputs {
            packets {}
            packet_ins: []
          }
        }
        actual_output {
          packets {}
          packet_ins: []
        }
        labels { labels: "label_1" }
      }
      test_result {}
    }
    outcomes {
      test_run {
        test_vector {
          input {}
          acceptable_outputs {
            packets {}
            packet_ins: []
          }
        }
        actual_output {
          packets {}
          packet_ins: []
        }
        labels { labels: "label_1" labels: "label_2" }
      }
      test_result {}
    }
    outcomes {
      test_run {
        test_vector {
          input {}
          acceptable_outputs {
            packets {}
            packet_ins: []
          }
        }
        actual_output {
          packets {}
          packet_ins: []
        }
        labels { labels: "label_2" }
      }
      test_result { failure {} }
    }
    outcomes {
      test_run {
        test_vector {
          input {}
          acceptable_outputs {
            packets {}
            packet_ins: []
          }
        }
        actual_output {
          packets {}
          packet_ins: []
        }
      }
    }
  )pb");
  std::cout << "-- ExplainPerLabelStats test ------------------------------\n"
            << ExplainPerLabelStats(ComputeTestVectorStatsPerLabel(outcomes))
            << "\n\n";
}

}  // namespace
}  // namespace dvaas
