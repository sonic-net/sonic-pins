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

    # Unexpected drop instead of forward.
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
          packets: []
          packet_ins: []
        }
      }
      # Failed.
      test_result { failure {} }
    }

    # Non-deterministic number of expected punts.
    outcomes {
      test_run {
        test_vector {
          input {}
          # Non-deterministic punt.
          acceptable_outputs {
            packets: []
            packet_ins: []
          }
          acceptable_outputs {
            packets: []
            packet_ins: {}
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
  )pb");
}

TEST(TestVectorStatsGoldenTest,
     ComputeTestVectorStatsAndExplainTestVectorStats) {
  PacketTestOutcomes outcomes = GetPacketTestOutcomes();
  TestVectorStats stats = ComputeTestVectorStats(outcomes);
  std::cout << "-- ExplainTestVectorStats test ------------------------------\n"
            << ExplainTestVectorStats(stats) << "\n\n";
}

}  // namespace
}  // namespace dvaas
