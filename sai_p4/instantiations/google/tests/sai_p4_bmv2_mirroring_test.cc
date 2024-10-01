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

#include <bitset>
#include <string>
#include <vector>

#include "absl/log/check.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/p4_runtime_matchers.h"
#include "p4_pdpi/p4_runtime_session_extras.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_pdpi/string_encodings/byte_string.h"
#include "platforms/networking/p4/p4_infra/bmv2/bmv2.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/test_tools/set_up_bmv2.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"

namespace pins {
namespace {

using ::gutil::IsOkAndHolds;
using ::orion::p4::test::Bmv2;
using ::pdpi::HasPacketIn;
using ::pdpi::ParsedPayloadIs;
using ::testing::ElementsAre;
using ::testing::EqualsProto;
using ::testing::Pair;
using ::testing::Property;
using ::testing::SizeIs;
using ::testing::UnorderedElementsAre;
using ::testing::Values;

constexpr int kV1modelPortBitwidth = 9;

// Returns an Ipv4 packet.
packetlib::Packet GetIpv4Packet() {
  return gutil::ParseProtoOrDie<packetlib::Packet>(
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
}

// Returns an Ipv6 packet.
packetlib::Packet GetIpv6Packet() {
  return gutil::ParseProtoOrDie<packetlib::Packet>(R"pb(
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
}

packetlib::Packet GetIpPacket(sai::IpVersion ip_version) {
  packetlib::Packet packet;
  switch (ip_version) {
    case sai::IpVersion::kIpv4:
      packet = GetIpv4Packet();
      break;
    case sai::IpVersion::kIpv6:
      packet = GetIpv6Packet();
      break;
    default:
      LOG(FATAL) << " Unsupported ip_version: "  // Crash ok
                 << static_cast<int>(ip_version);
  }

  CHECK_OK(packetlib::UpdateMissingComputedFields(packet));  // Crash ok
  CHECK_OK(packetlib::PadPacketToMinimumSize(packet));       // Crash ok
  return packet;
}

std::string BMv2Port(int port) {
  return pdpi::BitsetToP4RuntimeByteString(
      std::bitset<kV1modelPortBitwidth>(port));
}

struct MirroringTestParams {
  int ingress_port;
  int mirror_egress_port;
  sai::MarkToMirrorParams marked_to_mirror_params;
  sai::MirrorSessionParams mirror_session_params;
};

MirroringTestParams GetDefaultMirroringTestParams() {
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
              .mirror_egress_port = BMv2Port(kMirrorEgressPort),
          },
  };
}

class MirroringTest : public ::testing::TestWithParam<sai::IpVersion> {};

TEST_P(MirroringTest, OnePacketEmittedWhenPacketIsMirroredAndDropped) {
  constexpr sai::Instantiation kInstantiation = GetParam();
  const sai::IpVersion ip_version = GetParam();
  MirroringTestParams mirroring_test_params = GetDefaultMirroringTestParams();

  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  ASSERT_OK_AND_ASSIGN(
      std::vector<p4::v1::Entity> pi_entities,
      sai::EntryBuilder()
          .AddMarkToMirrorAclEntry(
              mirroring_test_params.marked_to_mirror_params)
          .AddMirrorSessionTableEntry(
              mirroring_test_params.mirror_session_params)
          // TODO: Remove unsupported once the
          // switch supports mirroring-related tables.
          .GetDedupedPiEntities(sai::GetIrP4Info(kInstantiation),
                                /*allow_unsupported=*/true));
  ASSERT_OK(pdpi::InstallPiEntities(bmv2.P4RuntimeSession(), pi_entities));

  EXPECT_THAT(bmv2.SendPacket(mirroring_test_params.ingress_port,
                              GetIpPacket(ip_version)),
              IsOkAndHolds(UnorderedElementsAre(
                  Pair(mirroring_test_params.mirror_egress_port,
                       Property(&packetlib::Packets::packets, SizeIs(1))))));
}

TEST_P(MirroringTest,
       TwoPacketsEmittedWhenAPacketHitsMirroringEntryAndIsForwarded) {
  constexpr sai::Instantiation kInstantiation = GetParam(); 
  const sai::IpVersion ip_version = GetParam();
  const MirroringTestParams mirroring_test_params =
      GetDefaultMirroringTestParams();
  constexpr int kForwardEgressPort = 9;

  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  ASSERT_OK_AND_ASSIGN(
      std::vector<p4::v1::Entity> pi_entities,
      sai::EntryBuilder()
          .AddEntriesForwardingIpPacketsToGivenPort(
              BMv2Port(kForwardEgressPort))
          .AddMarkToMirrorAclEntry(
              mirroring_test_params.marked_to_mirror_params)
          .AddMirrorSessionTableEntry(
              mirroring_test_params.mirror_session_params)
          // TODO: Remove unsupported once the
          // switch supports mirroring-related tables.
          .GetDedupedPiEntities(sai::GetIrP4Info(kInstantiation),
                                /*allow_unsupported=*/true));

  ASSERT_OK(pdpi::InstallPiEntities(bmv2.P4RuntimeSession(), pi_entities));
  EXPECT_THAT(bmv2.SendPacket(mirroring_test_params.ingress_port,
                              GetIpPacket(ip_version)),
              IsOkAndHolds(UnorderedElementsAre(
                  Pair(mirroring_test_params.mirror_egress_port,
                       Property(&packetlib::Packets::packets, SizeIs(1))),
                  Pair(kForwardEgressPort,
                       Property(&packetlib::Packets::packets, SizeIs(1))))));
}

TEST_P(
    MirroringTest,
    ThreePacketsEmittedWhenAPacketHitsMirroringEntryAndIsForwardedAndPunted) {
  constexpr sai::Instantiation kInstantiation = GetParam(); 
  const sai::IpVersion ip_version = GetParam();
  const MirroringTestParams mirroring_test_params =
      GetDefaultMirroringTestParams();
  constexpr int kForwardEgressPort = 19;

  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  ASSERT_OK_AND_ASSIGN(
      std::vector<p4::v1::Entity> pi_entities,
      sai::EntryBuilder()
          .AddEntriesForwardingIpPacketsToGivenPort(
              BMv2Port(kForwardEgressPort))
          .AddMarkToMirrorAclEntry(
              mirroring_test_params.marked_to_mirror_params)
          .AddMirrorSessionTableEntry(
              mirroring_test_params.mirror_session_params)
          .AddEntryPuntingAllPackets(sai::PuntAction::kCopy)
          // TODO: Remove unsupported once the
          // switch supports mirroring-related tables.
          .GetDedupedPiEntities(sai::GetIrP4Info(kInstantiation),
                                /*allow_unsupported=*/true));
  ASSERT_OK(pdpi::InstallPiEntities(bmv2.P4RuntimeSession(), pi_entities));

  packetlib::Packet input_packet = GetIpPacket(ip_version);
  EXPECT_THAT(bmv2.SendPacket(mirroring_test_params.ingress_port, input_packet),
              IsOkAndHolds(UnorderedElementsAre(
                  Pair(mirroring_test_params.mirror_egress_port,
                       Property(&packetlib::Packets::packets, SizeIs(1))),
                  Pair(kForwardEgressPort,
                       Property(&packetlib::Packets::packets, SizeIs(1))))));

  EXPECT_THAT(bmv2.P4RuntimeSession().ReadStreamChannelResponsesAndFinish(),
              IsOkAndHolds(ElementsAre(
                  HasPacketIn(ParsedPayloadIs(EqualsProto(input_packet))))));
}

INSTANTIATE_TEST_SUITE_P(DifferentIpVersions, MirroringTest,
                         Values(sai::IpVersion::kIpv4, sai::IpVersion::kIpv6));

}  // namespace
}  // namespace pins
