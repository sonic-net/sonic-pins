#include "dvaas/packet_trace.h"

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/test_artifact_writer.h"
#include "gutil/gutil/testing.h"

namespace {

using ::gutil::IsOk;
using ::gutil::StatusIs;

class DummyArtifactWriter : public gutil::TestArtifactWriter {
  absl::Status StoreTestArtifact(absl::string_view filename,
                                 absl::string_view contents) override {
    return absl::OkStatus();
  }

  absl::Status AppendToTestArtifact(absl::string_view filename,
                                    absl::string_view contents) override {
    return absl::OkStatus();
  }
};

TEST(StorePacketTraceTextualBmv2LogAsTestArtifact, IsOk) {
  dvaas::PacketTestOutcome test_outcome = gutil::ParseProtoOrDie<
      dvaas::PacketTestOutcome>(R"pb(
    test_result { failure { description: "Test failed" } }
    test_run {
      test_vector {
        input {
          type: DATAPLANE
          packet {
            port: "29"
            parsed { payload: "test packet #1: Dummy payload" }
            hex: "021a0ad0628b3647086f88a186dd668000000025112020000000000000000000000000000000280003f0c20008000000000000002000000003ea0025371274657374207061636b65742023313a2044756d6d79207061796c6f6164"
          }
        }
        acceptable_outputs {
          packet_trace {
            bmv2_textual_log: "BMv2 textual log"
            events { packet_replication { number_of_packets_replicated: 1 } }
          }
        }
      }
    }
  )pb");
  DummyArtifactWriter dvaas_test_artifact_writer;
  EXPECT_THAT(dvaas::StorePacketTraceTextualBmv2LogAsTestArtifact(
                  test_outcome, dvaas_test_artifact_writer),
              IsOk());
}

TEST(StorePacketTraceTextualBmv2LogAsTestArtifact,
     NoFullTraceInAcceptableOutputsFails) {
  dvaas::PacketTestOutcome test_outcome = gutil::ParseProtoOrDie<
      dvaas::PacketTestOutcome>(R"pb(
    test_result { failure { description: "Test failed" } }
    test_run {
      test_vector {
        input {
          type: DATAPLANE
          packet {
            port: "29"
            parsed { payload: "test packet #1: Dummy payload" }
            hex: "021a0ad0628b3647086f88a186dd668000000025112020000000000000000000000000000000280003f0c20008000000000000002000000003ea0025371274657374207061636b65742023313a2044756d6d79207061796c6f6164"
          }
        }
        acceptable_outputs {
          packet_trace {
            events { packet_replication { number_of_packets_replicated: 1 } }
          }
        }
      }
    }
  )pb");
  DummyArtifactWriter dvaas_test_artifact_writer;
  EXPECT_THAT(dvaas::StorePacketTraceTextualBmv2LogAsTestArtifact(
                  test_outcome, dvaas_test_artifact_writer),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

}  // namespace
