#include "dvaas/dataplane_validation.h"

#include <string>
#include <vector>

#include "absl/container/btree_map.h"
#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "dvaas/packet_trace.pb.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "gutil/test_artifact_writer.h"
#include "gutil/testing.h"

namespace dvaas {
namespace {

using ::gutil::IsOk;

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

TEST(AttachPacketTraceTest, IsOk) {
  PacketTestOutcome failed_packet_test;
  *failed_packet_test.mutable_test_result()->mutable_failure() =
      gutil::ParseProtoOrDie<PacketTestValidationResult::Failure>(R"pb(
        description: "Test failed"
      )pb");
  *failed_packet_test.mutable_test_run()
       ->mutable_test_vector() = gutil::ParseProtoOrDie<PacketTestVector>(R"pb(
    input {
      type: DATAPLANE
      packet {
        port: "29"
        parsed {
          headers {
            ethernet_header {
              ethernet_destination: "02:1a:0a:d0:62:8b"
              ethernet_source: "36:47:08:6f:88:a1"
              ethertype: "0x86dd"
            }
          }
          headers {
            ipv6_header {
              version: "0x6"
              dscp: "0x1a"
              ecn: "0x0"
              flow_label: "0x00000"
              payload_length: "0x0025"
              next_header: "0x11"
              hop_limit: "0x20"
              ipv6_source: "2000::"
              ipv6_destination: "2800:3f0:c200:800::2000"
            }
          }
          headers {
            udp_header {
              source_port: "0x0000"
              destination_port: "0x03ea"
              length: "0x0025"
              checksum: "0x3712"
            }
          }
          payload: "test packet #1: Dummy payload"
        }
        hex: "021a0ad0628b3647086f88a186dd668000000025112020000000000000000000000000000000280003f0c20008000000000000002000000003ea0025371274657374207061636b65742023313a2044756d6d79207061796c6f6164"
      }
    }
  )pb");
  std::string packet_hex =
      failed_packet_test.test_run().test_vector().input().packet().hex();
  auto packet_trace = gutil::ParseProtoOrDie<PacketTrace>(R"pb(
    bmv2_textual_log: "BMv2 textual log"
    events { packet_replication { number_of_packets_replicated: 1 } }
  )pb");
  absl::btree_map<std::string, std::vector<PacketTrace>> packet_traces;
  packet_traces[packet_hex] = {packet_trace};
  DummyArtifactWriter dvaas_test_artifact_writer;
  EXPECT_THAT(AttachPacketTrace(failed_packet_test, packet_traces,
                                dvaas_test_artifact_writer),
              IsOk());
}

}  // namespace
}  // namespace dvaas
