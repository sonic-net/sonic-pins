// Copyright 2023 Google LLC
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

#include <bitset>
#include <string>
#include <vector>

#include "absl/log/check.h"
#include "absl/log/log.h"
#include "absl/strings/str_cat.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_matchers.h"
#include "p4_infra/p4_pdpi/p4_runtime_session_extras.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib_matchers.h"
#include "p4_infra/p4_pdpi/string_encodings/byte_string.h"
#include "platforms/networking/p4/p4_infra/bmv2/bmv2.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/test_tools/set_up_bmv2.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"

namespace pins {
namespace {

using ::gutil::IsOkAndHolds;
using ::gutil::Partially;
using ::orion::p4::test::Bmv2;
using ::pdpi::HasPacketIn;
using ::pdpi::ParsedPayloadIs;
using ::testing::ElementsAre;
using ::testing::EqualsProto;
using ::testing::Key;
using ::testing::SizeIs;
using ::testing::UnorderedElementsAre;
using ::testing::Values;

constexpr int kV1modelPortBitwidth = 9;

// Returns an Ipv4 packet.
packetlib::Packet GetIpv4PacketOrDie() {
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
  CHECK_OK(packetlib::UpdateMissingComputedFields(packet));  // Crash ok
  CHECK_OK(packetlib::PadPacketToMinimumSize(packet));       // Crash ok
  return packet;
}

// Returns an Ipv6 packet.
packetlib::Packet GetIpv6PacketOrDie() {
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
  CHECK_OK(packetlib::UpdateMissingComputedFields(packet));  // Crash ok
  CHECK_OK(packetlib::PadPacketToMinimumSize(packet));       // Crash ok
  return packet;
}

packetlib::Packet GetIpPacketOrDie(sai::IpVersion ip_version) {
  packetlib::Packet packet;
  switch (ip_version) {
    case sai::IpVersion::kIpv4:
      packet = GetIpv4PacketOrDie();
      break;
    case sai::IpVersion::kIpv6:
      packet = GetIpv6PacketOrDie();
      break;
    default:
      LOG(FATAL) << " Unsupported ip_version: "  // Crash ok
                 << static_cast<int>(ip_version);
  }
  return packet;
}

std::string BMv2Port(int port) {
  return pdpi::BitsetToP4RuntimeByteString(
      std::bitset<kV1modelPortBitwidth>(port));
}

struct MirroringTestConstants {
  int ingress_port;
  int mirror_egress_port;
  sai::MarkToMirrorParams marked_to_mirror_params;
  sai::MirrorSessionParams mirror_session_params;
};

MirroringTestConstants GetMirroringTestConstants() {
  constexpr int kIngressPort = 6;
  constexpr int kMirrorEgressPort = 5;
  const std::string kMirrorSessionId = "mirror_session_id";
  return {
      .ingress_port = kIngressPort,
      .mirror_egress_port = kMirrorEgressPort,
      .marked_to_mirror_params =
          {
              .ingress_port = BMv2Port(kIngressPort),
              .mirror_session_id = kMirrorSessionId,
          },
      .mirror_session_params =
          {
              .mirror_session_id = kMirrorSessionId,
              .monitor_port = BMv2Port(kMirrorEgressPort),
              .monitor_backup_port = BMv2Port(kMirrorEgressPort),
              .mirror_encap_src_mac = "00:08:08:08:08:08",
              .mirror_encap_dst_mac = "01:09:09:09:09:09",
              .mirror_encap_vlan_id = "0x123",
              .mirror_encap_src_ip = "::1",
              .mirror_encap_dst_ip = "::2",
              .mirror_encap_udp_src_port = "0x1234",
              .mirror_encap_udp_dst_port = "0x1283",
          },
  };
}

// Asserts headers are IPFIX-extended conformant and verify headers fields are
// populated with values that match with `mirror_session_params` (such as IPV6
// header's dst ip value should be mirror_session_params.mirror_encap_dst_id) or
// match with hardcoded value in p4 modeling (such as IPV6's hop_limit of 16).
// Fields outside of P4-modeling's control, such as PSAMP header's
// observation_time are not checked.
void AssertPacketIsVlanTaggedAndIpfixEncappedWithMirrorSessionParams(
    const packetlib::Packet& packet,
    const sai::MirrorSessionParams& mirror_session_params) {
  using ::packetlib::HasHeaderCase;
  ASSERT_THAT(packet.headers(),
              ElementsAre(HasHeaderCase(packetlib::Header::kEthernetHeader),
                          HasHeaderCase(packetlib::Header::kVlanHeader),
                          HasHeaderCase(packetlib::Header::kIpv6Header),
                          HasHeaderCase(packetlib::Header::kUdpHeader),
                          HasHeaderCase(packetlib::Header::kIpfixHeader),
                          HasHeaderCase(packetlib::Header::kPsampHeader)));

  packetlib::Header ethernet_header;
  ethernet_header.mutable_ethernet_header()->set_ethertype("0x8100");
  ethernet_header.mutable_ethernet_header()->set_ethernet_destination(
      mirror_session_params.mirror_encap_dst_mac);
  ethernet_header.mutable_ethernet_header()->set_ethernet_source(
      mirror_session_params.mirror_encap_src_mac);

  packetlib::Header vlan_header;
  vlan_header.mutable_vlan_header()->set_priority_code_point("0x0");
  vlan_header.mutable_vlan_header()->set_drop_eligible_indicator("0x0");
  vlan_header.mutable_vlan_header()->set_vlan_identifier(
      mirror_session_params.mirror_encap_vlan_id);
  vlan_header.mutable_vlan_header()->set_ethertype("0x86dd");

  packetlib::Header ipv6_header;
  ipv6_header.mutable_ipv6_header()->set_dscp("0x00");
  ipv6_header.mutable_ipv6_header()->set_ecn("0x0");
  ipv6_header.mutable_ipv6_header()->set_flow_label("0x00000");
  ipv6_header.mutable_ipv6_header()->set_hop_limit("0x00");
  ipv6_header.mutable_ipv6_header()->set_version("0x6");
  // IP_PROTOCOL for UDP.
  ipv6_header.mutable_ipv6_header()->set_next_header("0x11");
  ipv6_header.mutable_ipv6_header()->set_ipv6_source(
      mirror_session_params.mirror_encap_src_ip);
  ipv6_header.mutable_ipv6_header()->set_ipv6_destination(
      mirror_session_params.mirror_encap_dst_ip);
  ASSERT_OK_AND_ASSIGN(const int packet_size,
                       packetlib::PacketSizeInBytes(packet));
  // Payload length field for both IP and UDP headers is the packet length
  // subtracted by the header length of IP header and of headers in front of IP
  // header (ETHERNET and VLAN).
  const int payload_length = packet_size - /*ETHERNET header bytes*/ 14 -
                             /*VLAN header bytes*/ 4 -
                             /*IPV6 header bytes*/ 40;

  ipv6_header.mutable_ipv6_header()->set_payload_length(
      packetlib::IpPayloadLength(payload_length));

  packetlib::Header udp_header;
  udp_header.mutable_udp_header()->set_source_port(
      mirror_session_params.mirror_encap_udp_src_port);
  udp_header.mutable_udp_header()->set_destination_port(
      mirror_session_params.mirror_encap_udp_dst_port);
  // UDP checksum for mirrored packets is set to 0.
  udp_header.mutable_udp_header()->set_checksum("0x0000");
  udp_header.mutable_udp_header()->set_length(
      packetlib::IpPayloadLength(payload_length));
  ASSERT_THAT(
      packet.headers(),
      ElementsAre(EqualsProto(ethernet_header), EqualsProto(vlan_header),
                  EqualsProto(ipv6_header), EqualsProto(udp_header),
                  // Use Partially matchers to only check the presence
                  // of IPFIX and PSAMP headers since P4 modeling
                  // doesn't populate any of the field within these two
                  // headers. P4BAR also will not check IPFIX and PSAMP
                  // headers too. See b/318753700 for details.
                  Partially(EqualsProto(R"pb(ipfix_header {})pb")),
                  Partially(EqualsProto(R"pb(psamp_header {})pb"))));
}

// Test fixture to verify packets are mirrored and encapped.
class MirrorAndEncapTest : public ::testing::TestWithParam<sai::IpVersion> {};

TEST_P(MirrorAndEncapTest, OnePacketEmittedWhenPacketIsMirroredAndDropped) {
  constexpr sai::Instantiation kInstantiation =
      sai::Instantiation::kExperimentalTor;
  const sai::IpVersion ip_version = GetParam();
  const MirroringTestConstants mirroring_test_params =
      GetMirroringTestConstants();
  SCOPED_TRACE(absl::StrCat(
      "MirrorAndEncapTest for OnePacketEmittedWhenPacketIsMirroredAndDropped. "
      "IP version: ",
      ip_version));

  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  ASSERT_OK(sai::EntryBuilder()
                .AddMarkToMirrorAclEntry(
                    mirroring_test_params.marked_to_mirror_params)
                .AddMirrorSessionTableEntry(
                    mirroring_test_params.mirror_session_params)
                .InstallDedupedEntities(sai::GetIrP4Info(kInstantiation),
                                        bmv2.P4RuntimeSession()));

  packetlib::Packet input_packet = GetIpPacketOrDie(ip_version);
  ASSERT_OK_AND_ASSIGN(
      const auto outputs,
      bmv2.SendPacket(mirroring_test_params.ingress_port, input_packet));
  ASSERT_THAT(outputs, UnorderedElementsAre(
                           Key(mirroring_test_params.mirror_egress_port)));
  ASSERT_THAT(outputs.at(mirroring_test_params.mirror_egress_port).packets(),
              SizeIs(1));
  packetlib::Packet mirrored_packet =
      outputs.at(mirroring_test_params.mirror_egress_port).packets(0);

  AssertPacketIsVlanTaggedAndIpfixEncappedWithMirrorSessionParams(
      mirrored_packet, mirroring_test_params.mirror_session_params);
  ASSERT_THAT(packetlib::ParsePacket(mirrored_packet.payload()),
              EqualsProto(input_packet));
}

TEST_P(MirrorAndEncapTest,
       TwoPacketsEmittedWhenAPacketHitsMirroringEntryAndIsForwarded) {
  constexpr sai::Instantiation kInstantiation =
      sai::Instantiation::kExperimentalTor;
  const sai::IpVersion ip_version = GetParam();
  const MirroringTestConstants mirroring_test_params =
      GetMirroringTestConstants();
  constexpr int kForwardEgressPort = 9;
  SCOPED_TRACE(
      absl::StrCat("MirrorAndEncapTest for "
                   "TwoPacketsEmittedWhenAPacketHitsMirroringEntryAndIsForwarde"
                   "d. IP version: ",
                   ip_version));
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  ASSERT_OK(sai::EntryBuilder()
                .AddEntriesForwardingIpPacketsToGivenPort(
                    BMv2Port(kForwardEgressPort))
                .AddMarkToMirrorAclEntry(
                    mirroring_test_params.marked_to_mirror_params)
                .AddMirrorSessionTableEntry(
                    mirroring_test_params.mirror_session_params)
                .InstallDedupedEntities(sai::GetIrP4Info(kInstantiation),
                                        bmv2.P4RuntimeSession()));

  packetlib::Packet input_packet = GetIpPacketOrDie(ip_version);
  ASSERT_OK_AND_ASSIGN(
      const auto outputs,
      bmv2.SendPacket(mirroring_test_params.ingress_port, input_packet));

  ASSERT_THAT(outputs, UnorderedElementsAre(
                           Key(mirroring_test_params.mirror_egress_port),
                           Key(kForwardEgressPort)));
  ASSERT_THAT(outputs.at(mirroring_test_params.mirror_egress_port).packets(),
              SizeIs(1));
  ASSERT_THAT(outputs.at(kForwardEgressPort).packets(), SizeIs(1));

  packetlib::Packet mirrored_packet =
      outputs.at(mirroring_test_params.mirror_egress_port).packets(0);
  AssertPacketIsVlanTaggedAndIpfixEncappedWithMirrorSessionParams(
      mirrored_packet, mirroring_test_params.mirror_session_params);
  ASSERT_THAT(packetlib::ParsePacket(mirrored_packet.payload()),
              EqualsProto(input_packet));
}

TEST_P(
    MirrorAndEncapTest,
    ThreePacketsEmittedWhenAPacketHitsMirroringEntryAndIsForwardedAndPunted) {
  constexpr sai::Instantiation kInstantiation =
      sai::Instantiation::kExperimentalTor;
  const sai::IpVersion ip_version = GetParam();
  const MirroringTestConstants mirroring_test_params =
      GetMirroringTestConstants();
  constexpr int kForwardEgressPort = 19;

  SCOPED_TRACE(
      absl::StrCat("MirrorAndEncapTest for "
                   "ThreePacketsEmittedWhenAPacketHitsMirroringEntryAndIsForwar"
                   "dedAndPunted. IP version: ",
                   ip_version));

  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));
  ASSERT_OK(sai::EntryBuilder()
                .AddEntriesForwardingIpPacketsToGivenPort(
                    BMv2Port(kForwardEgressPort))
                .AddMarkToMirrorAclEntry(
                    mirroring_test_params.marked_to_mirror_params)
                .AddMirrorSessionTableEntry(
                    mirroring_test_params.mirror_session_params)
                .AddEntryPuntingAllPackets(sai::PuntAction::kCopy)
                .InstallDedupedEntities(sai::GetIrP4Info(kInstantiation),
                                        bmv2.P4RuntimeSession()));

  packetlib::Packet input_packet = GetIpPacketOrDie(ip_version);
  ASSERT_OK_AND_ASSIGN(
      const auto outputs,
      bmv2.SendPacket(mirroring_test_params.ingress_port, input_packet));
  ASSERT_THAT(outputs, UnorderedElementsAre(
                           Key(mirroring_test_params.mirror_egress_port),
                           Key(kForwardEgressPort)));
  ASSERT_THAT(outputs.at(mirroring_test_params.mirror_egress_port).packets(),
              SizeIs(1));
  ASSERT_THAT(outputs.at(kForwardEgressPort).packets(), SizeIs(1));

  const packetlib::Packet mirrored_packet =
      outputs.at(mirroring_test_params.mirror_egress_port).packets(0);

  AssertPacketIsVlanTaggedAndIpfixEncappedWithMirrorSessionParams(
      mirrored_packet, mirroring_test_params.mirror_session_params);
  ASSERT_THAT(packetlib::ParsePacket(mirrored_packet.payload()),
              EqualsProto(input_packet));

  EXPECT_THAT(bmv2.P4RuntimeSession().ReadStreamChannelResponsesAndFinish(),
              IsOkAndHolds(ElementsAre(
                  HasPacketIn(ParsedPayloadIs(EqualsProto(input_packet))))));
}

// Tests that a packet that is mirrored is encapsulated but doesn't go through
// any other tables in the egress pipeline.
// The test installs a egress drop rule that matches all IP packets. The test
// would fail if the mirrored packet goes through the egress pipeline and gets
// dropped.
TEST_P(MirrorAndEncapTest, MirroredPacketSkipsEgressPipeline) {
  constexpr sai::Instantiation kInstantiation =
      sai::Instantiation::kExperimentalTor;
  const sai::IpVersion ip_version = GetParam();
  const MirroringTestConstants mirroring_test_params =
      GetMirroringTestConstants();
  constexpr int kForwardEgressPort = 9;
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  ASSERT_OK(sai::EntryBuilder()
                .AddEntriesForwardingIpPacketsToGivenPort(
                    BMv2Port(kForwardEgressPort))
                .AddMarkToMirrorAclEntry(
                    mirroring_test_params.marked_to_mirror_params)
                .AddMirrorSessionTableEntry(
                    mirroring_test_params.mirror_session_params)
                .AddEgressAclDroppingIpPackets()
                .InstallDedupedEntities(sai::GetIrP4Info(kInstantiation),
                                        bmv2.P4RuntimeSession()));

  packetlib::Packet input_packet = GetIpPacketOrDie(ip_version);
  ASSERT_OK_AND_ASSIGN(
      const auto outputs,
      bmv2.SendPacket(mirroring_test_params.ingress_port, input_packet));

  ASSERT_THAT(outputs, UnorderedElementsAre(
                           Key(mirroring_test_params.mirror_egress_port)));
  ASSERT_THAT(outputs.at(mirroring_test_params.mirror_egress_port).packets(),
              SizeIs(1));

  packetlib::Packet mirrored_packet =
      outputs.at(mirroring_test_params.mirror_egress_port).packets(0);
  AssertPacketIsVlanTaggedAndIpfixEncappedWithMirrorSessionParams(
      mirrored_packet, mirroring_test_params.mirror_session_params);
  // The encapsulated packet should be the same as the input packet.
  ASSERT_THAT(packetlib::ParsePacket(mirrored_packet.payload()),
              EqualsProto(input_packet));
}

INSTANTIATE_TEST_SUITE_P(DifferentIpVersions, MirrorAndEncapTest,
                         Values(sai::IpVersion::kIpv4, sai::IpVersion::kIpv6));

}  // namespace
}  // namespace pins
