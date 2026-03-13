// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "dvaas/test_vector.h"

#include <string>

#include "absl/status/status.h"
#include "dvaas/test_vector.pb.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "p4_infra/packetlib/bit_widths.h"
#include "p4_infra/packetlib/packetlib.h"
#include "p4_infra/packetlib/packetlib.pb.h"

namespace dvaas {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::testing::Eq;
using ::testing::Ge;
using ::testing::HasSubstr;

constexpr int kMinNumBytesInPayload = packetlib::kMinNumBytesInEthernetPayload;

TEST(MakeTestPacketTag, WorksWithEmptyDescription) {
  EXPECT_THAT(MakeTestPacketTagFromUniqueId(1, "").length(),
              Ge(kMinNumBytesInPayload));
}

TEST(MakeTestPacketTag, YieldsPaddedTestPacketTag) {
  EXPECT_THAT(MakeTestPacketTagFromUniqueId(1, "some description").length(),
              Ge(kMinNumBytesInPayload));
}

TEST(MakeTestPacketTag, YieldsPaddedTestPacketTagWithDescription) {
  const std::string kDescription = "dummy description.";
  std::string payload = MakeTestPacketTagFromUniqueId(5, kDescription);
  EXPECT_THAT(payload.length(), Ge(kMinNumBytesInPayload));
  EXPECT_THAT(payload, HasSubstr(kDescription));
}

TEST(MakeTestPacketTag, YieldsNonPaddedTestPacketTagWithDescription) {
  const std::string kDescription = "exact dummy description size";
  std::string payload = MakeTestPacketTagFromUniqueId(123, kDescription);
  EXPECT_THAT(payload.length(), Ge(kMinNumBytesInPayload));
  EXPECT_THAT(payload, HasSubstr(kDescription));
}

TEST(MakeTestPacketTag, YieldsTestPacketTagWithLongDescription) {
  const std::string kDescription = "the test packet can have a description.";
  std::string payload = MakeTestPacketTagFromUniqueId(7, kDescription);
  EXPECT_THAT(payload.length(), Ge(kMinNumBytesInPayload));
  EXPECT_THAT(payload, HasSubstr(kDescription));
}

TEST(MakeTestPacketTag, RoundTripsWithExtractTestPacketTag) {
  for (int test_packet_id : {0, 1, 2, 42, 1234}) {
    ASSERT_THAT(ExtractIdFromTaggedPacket(MakeTestPacketTagFromUniqueId(
                    test_packet_id, "some description")),
                IsOkAndHolds(Eq(test_packet_id)));
  }
}

TEST(MakeTestPacketTag,
     RoundTripsWithExtractTestPacketTagWithDifferentSizedDescriptions) {
  constexpr int kPacketTag = 10;
  for (int description_size : {0, 1, 2, 42, 1234}) {
    EXPECT_THAT(ExtractIdFromTaggedPacket(MakeTestPacketTagFromUniqueId(
                    kPacketTag, std::string(description_size, '!'))),
                IsOkAndHolds(Eq(kPacketTag)));
  }
}

TEST(UpdateTestPacketTag, UpdateTestTagIsNoOpForExistingId) {
  constexpr int kId = 42;
  packetlib::Packet packet;
  packet.set_payload(MakeTestPacketTagFromUniqueId(kId, "my test packet"));
  PacketTestVector packet_test_vector;
  *packet_test_vector.mutable_input()->mutable_packet()->mutable_parsed() =
      packet;
  ASSERT_OK(UpdateTestTag(packet_test_vector, kId));
  EXPECT_THAT(packet_test_vector.input().packet().parsed(),
              EqualsProto(packet));
}

TEST(UpdateTestPacketTag, YieldsValidPacketTestVectorWithUpdatedTag) {
  auto test_vector = gutil::ParseProtoOrDie<PacketTestVector>(R"pb(
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
    acceptable_outputs {
      packets {
        port: "12"
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
      packets {
        port: "12"
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
      packet_ins {
        metadata {
          name: "ingress_port"
          value { str: "9" }
        }
        metadata {
          name: "target_egress_port"
          value { str: "6" }
        }
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
      packet_ins {
        metadata {
          name: "ingress_port"
          value { str: "9" }
        }
        metadata {
          name: "target_egress_port"
          value { str: "6" }
        }
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
  PacketTestVector updated_test_vector = test_vector;
  int kNewTag = 2000000;
  ASSERT_OK(UpdateTestTag(test_vector, kNewTag));

  // Check if all the tags were updated, including the hex and payload.
  ASSERT_OK(packetlib::ValidatePacket(test_vector.input().packet().parsed()));
  ASSERT_OK_AND_ASSIGN(
      std::string raw_input_packet,
      packetlib::RawSerializePacket(test_vector.input().packet().parsed()));
  ASSERT_THAT(ExtractIdFromTaggedPacket(raw_input_packet),
              IsOkAndHolds(Eq(kNewTag)));
  ASSERT_NE(test_vector.input().packet().hex(),
            updated_test_vector.input().packet().hex());
  for (int i = 0; i < test_vector.acceptable_outputs().size(); ++i) {
    const SwitchOutput& acceptable_outputs = test_vector.acceptable_outputs(i);
    for (int j = 0; j < acceptable_outputs.packets().size(); ++j) {
      const Packet& packet = acceptable_outputs.packets(j);
      ASSERT_OK(packetlib::ValidatePacket(packet.parsed()));
      ASSERT_OK_AND_ASSIGN(std::string raw_output_packet,
                           packetlib::RawSerializePacket(packet.parsed()));
      ASSERT_THAT(ExtractIdFromTaggedPacket(raw_output_packet),
                  IsOkAndHolds(Eq(kNewTag)));
      ASSERT_NE(packet.hex(),
                updated_test_vector.acceptable_outputs(i).packets(j).hex());
    }
    for (int j = 0; j < acceptable_outputs.packet_ins().size(); ++j) {
      const PacketIn& packet_in = acceptable_outputs.packet_ins(j);
      ASSERT_OK(packetlib::ValidatePacket(packet_in.parsed()));
      ASSERT_OK_AND_ASSIGN(std::string raw_in_packet,
                           packetlib::RawSerializePacket(packet_in.parsed()));
      ASSERT_THAT(ExtractIdFromTaggedPacket(raw_in_packet),
                  IsOkAndHolds(Eq(kNewTag)));
      ASSERT_NE(packet_in.hex(),
                updated_test_vector.acceptable_outputs(i).packet_ins(j).hex());
    }
  }
}

TEST(UpdateTestPacketTag, FailsForPacketWithNoTag) {
  auto test_vector = gutil::ParseProtoOrDie<PacketTestVector>(R"pb(
    input {
      type: DATAPLANE
      packet { parsed { payload: "test packet" } }
    }
  )pb");
  EXPECT_THAT(UpdateTestTag(test_vector, /*new_tag=*/0),
              gutil::StatusIs(absl::StatusCode::kInvalidArgument));
}

}  // namespace
}  // namespace dvaas
