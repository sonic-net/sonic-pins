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

#include <optional>
#include <string>
#include <vector>

#include "absl/log/check.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/netaddr/mac_address.h"
#include "p4_pdpi/p4_runtime_matchers.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/p4_runtime_session_extras.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_pdpi/string_encodings/byte_string.h"
#include "platforms/networking/p4/p4_infra/bmv2/bmv2.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/test_tools/set_up_bmv2.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"
#include "tests/forwarding/packet_at_port.h"

namespace pins {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::orion::p4::test::Bmv2;
using ::pdpi::HasPacketIn;
using ::pdpi::ParsedPayloadIs;
using ::testing::ElementsAre;
using ::testing::IsEmpty;
using ::testing::SizeIs;
using ::testing::ValuesIn;

// Returns an Ipv6 packet.
packetlib::Packet GetIpv6Packet(absl::string_view ttl) {
  packetlib::Packet packet = gutil::ParseProtoOrDie<packetlib::Packet>(R"pb(
    headers {
      ethernet_header {
        ethernet_destination: "02:03:04:05:06:77"
        ethernet_source: "00:01:02:03:04:55"
        ethertype: "0x86dd"  # IPv6
      }
    }
    headers {
      ipv6_header {
        version: "0x6"
        dscp: "0x00"
        ecn: "0x0"
        flow_label: "0x12345"
        next_header: "0x11"  # UDP
        hop_limit: "0x22"
        ipv6_source: "2001::1"
        ipv6_destination: "2001::2"
      }
    }
    headers {
      udp_header {
        source_port: "0x0000"
        destination_port: "0x0000"
        length: "0x0013"
      }
    }
    payload: "ipv6 packet"
  )pb");
  packet.mutable_headers(1)->mutable_ipv6_header()->set_hop_limit(ttl);
  CHECK_OK(packetlib::PadPacketToMinimumSize(packet));
  CHECK_OK(packetlib::UpdateAllComputedFields(packet));
  return packet;
}

// Returns an Ipv4 packet.
packetlib::Packet GetIpv4Packet(absl::string_view ttl) {
  packetlib::Packet packet = gutil::ParseProtoOrDie<packetlib::Packet>(
      R"pb(
        headers {
          ethernet_header {
            ethernet_destination: "02:03:04:05:06:77"
            ethernet_source: "00:01:02:03:04:55"
            ethertype: "0x0800"
          }
        }
        headers {
          ipv4_header {
            version: "0x4"
            ihl: "0x5"
            dscp: "0x1c"
            ecn: "0x0"
            total_length: "0x002e"
            identification: "0x0000"
            flags: "0x0"
            fragment_offset: "0x0000"
            ttl: "0x22"
            protocol: "0x11"
            ipv4_source: "192.168.100.2"
            ipv4_destination: "192.168.100.1"
          }
        }
        headers {
          udp_header {
            source_port: "0x0000"
            destination_port: "0x0000"
            length: "0x001a"
          }
        }
        payload: "packet"
      )pb");
  packet.mutable_headers(1)->mutable_ipv4_header()->set_ttl(ttl);
  CHECK_OK(packetlib::PadPacketToMinimumSize(packet));
  CHECK_OK(packetlib::UpdateAllComputedFields(packet));
  return packet;
}
// Returns an Ip packet for given `ip_version` and `ttl`.
packetlib::Packet GetIpPacket(sai::IpVersion ip_version,
                              absl::string_view ttl) {
  switch (ip_version) {
    case sai::IpVersion::kIpv4:
      return GetIpv4Packet(ttl);
    case sai::IpVersion::kIpv6:
      return GetIpv6Packet(ttl);
    default:
      LOG(FATAL) << "Unsupported ip_version: "  // Crash ok
                 << static_cast<int>(ip_version);
  }
}

// Verifies that for each disable rewrite option in `rewrite_options`, if
// it is set to false, the field associated with that option is rewritten. Else,
// the field associated with that option remains the same for `input_packet` and
// `output_packet`.
// Note, this helper function assumes `input_packet` and `output_packet` both
// have headers that look like [Ethernet,IP{v4,v6}]
void VerifyOutputPacketIsRewritten(
    const packetlib::Packet& input_packet,
    const packetlib::Packet& output_packet,
    const sai::NexthopRewriteOptions& rewrite_options,
    const sai::IpVersion& ip_version) {
  ASSERT_TRUE(input_packet.headers(0).has_ethernet_header());
  ASSERT_TRUE(output_packet.headers(0).has_ethernet_header());

  if (rewrite_options.src_mac_rewrite.has_value()) {
    EXPECT_EQ(output_packet.headers(0).ethernet_header().ethernet_source(),
              rewrite_options.src_mac_rewrite->ToString());
  } else {
    EXPECT_EQ(output_packet.headers(0).ethernet_header().ethernet_source(),
              input_packet.headers(0).ethernet_header().ethernet_source());
  }

  if (rewrite_options.dst_mac_rewrite.has_value()) {
    EXPECT_EQ(output_packet.headers(0).ethernet_header().ethernet_destination(),
              rewrite_options.dst_mac_rewrite->ToString());
  } else {
    EXPECT_EQ(output_packet.headers(0).ethernet_header().ethernet_destination(),
              input_packet.headers(0).ethernet_header().ethernet_destination());
  }
  switch (ip_version) {
    case sai::IpVersion::kIpv4: {
      ASSERT_TRUE(input_packet.headers(1).has_ipv4_header());
      ASSERT_TRUE(output_packet.headers(1).has_ipv4_header());

      if (rewrite_options.disable_decrement_ttl) {
        EXPECT_EQ(input_packet.headers(1).ipv4_header().ttl(),
                  output_packet.headers(1).ipv4_header().ttl());
      } else {
        EXPECT_NE(input_packet.headers(1).ipv4_header().ttl(),
                  output_packet.headers(1).ipv4_header().ttl());
      }
      break;
    }
    case sai::IpVersion::kIpv6:
      ASSERT_TRUE(input_packet.headers(1).has_ipv6_header());
      ASSERT_TRUE(output_packet.headers(1).has_ipv6_header());

      if (rewrite_options.disable_decrement_ttl) {
        EXPECT_EQ(input_packet.headers(1).ipv6_header().hop_limit(),
                  output_packet.headers(1).ipv6_header().hop_limit());
      } else {
        EXPECT_NE(input_packet.headers(1).ipv6_header().hop_limit(),
                  output_packet.headers(1).ipv6_header().hop_limit());
      }
      break;
    case sai::IpVersion::kIpv4And6:
      FAIL() << "Unsupported ip_version: kIpv4And6";
      break;
  }
}

struct PacketRewritesTestParams {
  sai::NexthopRewriteOptions nexthop_rewrite_options;
  sai::IpVersion ip_version;
  sai::Instantiation instantiation;
};

template <typename Sink>
void AbslStringify(Sink& sink, const PacketRewritesTestParams& param) {
  const std::optional<netaddr::MacAddress>& src_rewrite =
      param.nexthop_rewrite_options.src_mac_rewrite;
  const std::optional<netaddr::MacAddress>& dst_rewrite =
      param.nexthop_rewrite_options.dst_mac_rewrite;
  absl::Format(&sink,
               "[disable_decrement_ttl: %v, src_mac_rewrite: %s, "
               "dst_mac_rewrite: %s, ip_version: %v, instantiation: "
               "%v]",
               param.nexthop_rewrite_options.disable_decrement_ttl,
               src_rewrite.has_value() ? src_rewrite->ToString() : "disabled",
               dst_rewrite.has_value() ? dst_rewrite->ToString() : "disabled",
               param.ip_version,
               sai::InstantiationToString(param.instantiation));
}

// Generates Cartesian product of NexthopRewriteOptions's TTL, SrcMac and DstMac
// rewrite options.
std::vector<sai::NexthopRewriteOptions>
CartesianProductOfNexthopRewriteOptions() {
  std::vector<sai::NexthopRewriteOptions> options;
  for (bool disable_decrement_ttl : {false, true}) {
    for (bool disable_src_mac_rewrite : {false, true}) {
      for (bool disable_dst_mac_rewrite : {false, true}) {
        options.push_back(sai::NexthopRewriteOptions{
            .disable_decrement_ttl = disable_decrement_ttl,
            .src_mac_rewrite =
                disable_src_mac_rewrite
                    ? std::nullopt
                    : std::make_optional(netaddr::MacAddress(1, 2, 3, 4, 5, 6)),
            .dst_mac_rewrite =
                disable_dst_mac_rewrite
                    ? std::nullopt
                    : std::make_optional(netaddr::MacAddress(4, 4, 4, 4, 4, 4)),
        });
      }
    }
  }
  return options;
}

// Generates Cartesian product of {`nexthop_rewrite_options` x IpVersions x
// SaiInstantiations}.
std::vector<PacketRewritesTestParams>
CartesianProductOfIpVersionsAndInstantiationsAndGivenRewriteOptions(
    const std::vector<sai::NexthopRewriteOptions>& nexthop_rewrite_options) {
  std::vector<PacketRewritesTestParams> params;
  for (const sai::NexthopRewriteOptions& rewrite_options :
       nexthop_rewrite_options) {
    for (sai::IpVersion ip_version : {
             sai::IpVersion::kIpv4,
             sai::IpVersion::kIpv6,
         }) {
      for (sai::Instantiation instantiation : sai::AllSaiInstantiations()) {
        params.push_back(PacketRewritesTestParams{
            .nexthop_rewrite_options = rewrite_options,
            .ip_version = ip_version,
            .instantiation = instantiation,
        });
      }
    }
  }
  return params;
}

constexpr int kBmv2PortBitwidth = 9;

class PacketRewritesTest
    : public testing::TestWithParam<PacketRewritesTestParams> {};

TEST_P(PacketRewritesTest, PacketsAreForwardedWithCorrectRewrites) {
  constexpr int kIngressPort = 2;
  constexpr int kEgressPort = 1;
  const sai::Instantiation instantiation = GetParam().instantiation;
  const sai::IpVersion ip_version = GetParam().ip_version;
  const sai::NexthopRewriteOptions rewrite_options =
      GetParam().nexthop_rewrite_options;

  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(instantiation));
  ASSERT_OK_AND_ASSIGN(
      std::vector<p4::v1::Entity> pi_entities,
      sai::EntryBuilder()
          .AddEntriesForwardingIpPacketsToGivenPort(
              pdpi::BitsetToP4RuntimeByteString<kBmv2PortBitwidth>(kEgressPort),
              ip_version, rewrite_options)
          .LogPdEntries()
          .GetDedupedPiEntities(
              sai::GetIrP4Info(instantiation),
              // TODO: Remove once `@unsupported` annotation is
              // removed from set_ip_nexthop_and_disable_rewrites.
              /*allow_unsupported=*/true));
  ASSERT_OK(pdpi::InstallPiEntities(bmv2.P4RuntimeSession(), pi_entities));

  // Use input packet with TTL !=0/1. TTL == 0/1 scenarios are tested in
  // another test below.
  packetlib::Packet input_packet = GetIpPacket(ip_version, /*ttl=*/"0x22");

  ASSERT_OK_AND_ASSIGN(std::string raw_input_packet,
                       packetlib::SerializePacket(input_packet));
  ASSERT_OK_AND_ASSIGN(std::vector<pins::PacketAtPort> output_packets,
                       bmv2.SendPacket(pins::PacketAtPort{
                           .port = kIngressPort,
                           .data = raw_input_packet,
                       }));
  ASSERT_THAT(output_packets, SizeIs(1));
  packetlib::Packet output_packet =
      packetlib::ParsePacket(output_packets[0].data);
  VerifyOutputPacketIsRewritten(input_packet, output_packet, rewrite_options,
                                ip_version);
}

INSTANTIATE_TEST_SUITE_P(
    CartesianProductOfRewriteOptionsAndInstantiationsAndIpVersions,
    PacketRewritesTest,
    ValuesIn(
        CartesianProductOfIpVersionsAndInstantiationsAndGivenRewriteOptions(
            CartesianProductOfNexthopRewriteOptions())));

class TtlRewriteTest : public testing::TestWithParam<PacketRewritesTestParams> {
};

// Test when TTL rewrite is disabled, packet with TTL == 1 is forwarded and
// packet with TTL == 0 is dropped.
TEST_P(TtlRewriteTest, PacketWithZeroOrOneTtlTest) {
  constexpr int kIngressPort = 2;
  constexpr int kEgressPort = 1;
  const sai::Instantiation instantiation = GetParam().instantiation;
  const sai::IpVersion ip_version = GetParam().ip_version;
  const sai::NexthopRewriteOptions rewrite_options =
      GetParam().nexthop_rewrite_options;

  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(instantiation));
  ASSERT_OK_AND_ASSIGN(
      std::vector<p4::v1::Entity> pi_entities,
      sai::EntryBuilder()
          .AddEntriesForwardingIpPacketsToGivenPort(
              pdpi::BitsetToP4RuntimeByteString<kBmv2PortBitwidth>(kEgressPort),
              ip_version, rewrite_options)
          .LogPdEntries()
          .GetDedupedPiEntities(
              sai::GetIrP4Info(instantiation),
              // TODO: Remove once `@unsupported` annotation is
              // removed from set_ip_nexthop_and_disable_rewrites.
              /*allow_unsupported=*/true));
  ASSERT_OK(pdpi::InstallPiEntities(bmv2.P4RuntimeSession(), pi_entities));

  // Input packet with TTL == 1 should be forwarded.
  packetlib::Packet input_packet = GetIpPacket(ip_version, /*ttl=*/"0x01");
  ASSERT_OK_AND_ASSIGN(std::string raw_input_packet,
                       packetlib::SerializePacket(input_packet));
  ASSERT_OK_AND_ASSIGN(std::vector<pins::PacketAtPort> output_packets,
                       bmv2.SendPacket(pins::PacketAtPort{
                           .port = kIngressPort,
                           .data = raw_input_packet,
                       }));
  ASSERT_THAT(output_packets, SizeIs(1));

  packetlib::Packet output_packet =
      packetlib::ParsePacket(output_packets[0].data);
  switch (ip_version) {
    case sai::IpVersion::kIpv4:
      EXPECT_EQ(output_packet.headers(1).ipv4_header().ttl(), "0x01");
      break;
    case sai::IpVersion::kIpv6:
      EXPECT_EQ(output_packet.headers(1).ipv6_header().hop_limit(), "0x01");
      break;
    default:
      FAIL() << "Unsupported ip_version: " << static_cast<int>(ip_version);
  }

  // Input packet with TTL == 0 should be dropped.
  input_packet = GetIpPacket(ip_version, /*ttl=*/"0x00");
  ASSERT_OK_AND_ASSIGN(raw_input_packet,
                       packetlib::SerializePacket(input_packet));
  EXPECT_THAT(bmv2.SendPacket(pins::PacketAtPort{
                  .port = kIngressPort,
                  .data = raw_input_packet,
              }),
              IsOkAndHolds(IsEmpty()));
}

INSTANTIATE_TEST_SUITE_P(
    CartesianProductOfInstantiationsAndIpVersions, TtlRewriteTest,
    ValuesIn(
        CartesianProductOfIpVersionsAndInstantiationsAndGivenRewriteOptions(
            {sai::NexthopRewriteOptions{.disable_decrement_ttl = true}})));

class TtlRewriteAndPuntTest
    : public testing::TestWithParam<PacketRewritesTestParams> {};

// When 0/1 ACL punt rules are present, packets with 0/1 TTL should be trapped
// instead of being dropped by packet_rewrites.
TEST_P(TtlRewriteAndPuntTest, ZeroAndOneTtlPacketsAreTrapped) {
  constexpr int kIngressPort = 2;
  const sai::Instantiation instantiation = GetParam().instantiation;
  const sai::IpVersion ip_version = GetParam().ip_version;

  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(instantiation));
  ASSERT_OK_AND_ASSIGN(
      std::vector<p4::v1::Entity> pi_entities,
      sai::EntryBuilder()
          .AddEntryPuntingPacketsWithTtlZeroAndOne()
          .LogPdEntries()
          .GetDedupedPiEntities(sai::GetIrP4Info(instantiation)));
  ASSERT_OK(pdpi::InstallPiEntities(bmv2.P4RuntimeSession(), pi_entities));

  // Input packet with TTL == 1 should be trapped.
  packetlib::Packet ttl_1_input_packet =
      GetIpPacket(ip_version, /*ttl=*/"0x01");
  ASSERT_OK_AND_ASSIGN(std::string raw_input_packet,
                       packetlib::SerializePacket(ttl_1_input_packet));
  EXPECT_THAT(bmv2.SendPacket(pins::PacketAtPort{
                  .port = kIngressPort,
                  .data = raw_input_packet,
              }),
              IsOkAndHolds(IsEmpty()));

  // Input packet with TTL == 0 should be trapped.
  packetlib::Packet ttl_0_input_packet =
      GetIpPacket(ip_version, /*ttl=*/"0x00");
  ASSERT_OK_AND_ASSIGN(raw_input_packet,
                       packetlib::SerializePacket(ttl_0_input_packet));
  EXPECT_THAT(bmv2.SendPacket(pins::PacketAtPort{
                  .port = kIngressPort,
                  .data = raw_input_packet,
              }),
              IsOkAndHolds(IsEmpty()));

  // Check trapped packets.
  EXPECT_THAT(
      bmv2.P4RuntimeSession().ReadStreamChannelResponsesAndFinish(),
      IsOkAndHolds(ElementsAre(
          HasPacketIn(ParsedPayloadIs(EqualsProto(ttl_1_input_packet))),
          HasPacketIn(ParsedPayloadIs(EqualsProto(ttl_0_input_packet))))));
}

INSTANTIATE_TEST_SUITE_P(
    CartesianProductOfInstantiationsAndIpVersions, TtlRewriteAndPuntTest,
    ValuesIn(
        CartesianProductOfIpVersionsAndInstantiationsAndGivenRewriteOptions(
            {sai::NexthopRewriteOptions{.disable_decrement_ttl = false}})));

}  // namespace
}  // namespace pins
