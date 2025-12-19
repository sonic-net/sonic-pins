#include "dvaas/validation_result.h"

#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "dvaas/test_vector.pb.h"
#include "gmock/gmock.h"
#include "gutil/proto_matchers.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"

namespace dvaas {
namespace {

using ::gutil::EqualsProto;
using ::gutil::Partially;
using ::testing::HasSubstr;
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
            packet_trace {
              bmv2_textual_log: "bmv2_textual_log"
              events { mark_to_drop { source_location: "source_location" } }
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

TEST(ValidationResultTest, CheckTraceDetails) {
  auto packet_test_outcomes = GetPacketTestOutcomes();
  PacketSynthesisResult packet_synthesis_result;
  ValidationResult validation_result(packet_test_outcomes,
                                     packet_synthesis_result);

  EXPECT_OK(validation_result.HasSuccessRateOfAtLeastForGivenLabels(
      1.0, {"passing"}));
  EXPECT_OK(validation_result.HasSuccessRateOfAtLeastWithoutGivenLabels(
      1.0, {"failing"}));
}

TEST(ValidationResultTest, CheckTraceIsPartOfFailureMessage) {
  auto packet_test_outcomes = GetPacketTestOutcomes();
  PacketSynthesisResult packet_synthesis_result;
  ValidationResult validation_result(packet_test_outcomes,
                                     packet_synthesis_result);
  absl::Status status = validation_result.HasSuccessRateOfAtLeast(0.76);
  EXPECT_THAT(status, Not(absl::OkStatus()));
  EXPECT_THAT(status.message(),
              HasSubstr("Primitive: 'mark_to_drop' (source_location)"));
}

TEST(ValidationResultTest, CheckReturnedResultExcludingLabels) {
  auto packet_test_outcomes = GetPacketTestOutcomes();
  PacketSynthesisResult packet_synthesis_result;
  ValidationResult validation_result(packet_test_outcomes,
                                     packet_synthesis_result);
  // The first outcome is failing, so should be excluded.
  // The second outcome has the passing label, so should be included.
  // The third and fourth outcomes have no labels, so should be included.
  EXPECT_THAT(
      validation_result.ExcludingLabels({"failing"}).GetRawPacketTestOutcomes(),
      Partially(EqualsProto(
          R"pb(outcomes { test_run { labels { labels: "passing" } } }
               outcomes {}
               outcomes {})pb")));
}

}  // namespace
}  // namespace dvaas
