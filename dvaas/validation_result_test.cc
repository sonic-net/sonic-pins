#include "dvaas/validation_result.h"

#include <string>

#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "dvaas/test_vector.pb.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"

namespace dvaas {
namespace {

using ::testing::Not;

PacketTestOutcomes GetPacketTestOutcomes() {
  return gutil::ParseProtoOrDie<PacketTestOutcomes>(R"pb(
    outcomes {
      test_run {
        test_vector {
          acceptable_outputs {
            packets {
              port: "1"
              parsed { payload: "" }
            }
          }
        }
        actual_output {
          packets {
            port: "1"
            parsed { payload: "new-payload" }
          }
        }
        labels { labels: "failing" }
      }
      test_result { failure { description: "failure due to payload" } }
    }
    outcomes {
      test_run {
        test_vector {
          acceptable_outputs {
            packets {
              port: "2"
              parsed { payload: "matching-payload" }
            }
          }
        }
        actual_output {
          packets {
            port: "2"
            parsed { payload: "matching-payload" }
          }
        }
        labels { labels: "passing" }
      }
    }
    outcomes {
      test_run {
        test_vector {
          acceptable_outputs {
            packets {
              port: "2"
              parsed { payload: "matching-payload" }
            }
          }
        }
        actual_output {
          packets {
            port: "2"
            parsed { payload: "matching-payload" }
          }
        }
      }
    }
    outcomes {
      test_run {
        test_vector {
          acceptable_outputs {
            packets {
              port: "2"
              parsed { payload: "matching-payload" }
            }
          }
        }
        actual_output {
          packets {
            port: "2"
            parsed { payload: "matching-payload" }
          }
        }
      }
    }
  )pb");
}

TEST(ValidationResultTest, HasSuccessRateOfAtLeast100PercentWithLabels) {
  auto packet_test_outcomes = GetPacketTestOutcomes();
  PacketSynthesisResult packet_synthesis_result;
  ValidationResult validation_result(packet_test_outcomes,
                                     packet_synthesis_result);

  absl::flat_hash_set<std::string> included_labels_set = {"passing"};
  absl::flat_hash_set<std::string> excluded_labels_set = {"failing"};

  EXPECT_THAT(validation_result.HasSuccessRateOfAtLeast(0.76),
              Not(absl::OkStatus()));
  EXPECT_OK(validation_result.HasSuccessRateOfAtLeastForGivenLabels(
      1.0, included_labels_set));
  EXPECT_OK(validation_result.HasSuccessRateOfAtLeastWithoutGivenLabels(
      1.0, excluded_labels_set));
}

}  // namespace
}  // namespace dvaas
