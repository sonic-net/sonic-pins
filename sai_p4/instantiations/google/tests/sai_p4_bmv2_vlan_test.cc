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

#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/log/check.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "gutil/testing.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_pdpi/packetlib/packetlib_matchers.h"
#include "p4_pdpi/pd.h"
#include "p4_pdpi/translation_options.h"
#include "platforms/networking/p4/p4_infra/bmv2/bmv2.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "sai_p4/instantiations/google/test_tools/set_up_bmv2.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"

namespace pins {
namespace {

using ::orion::p4::test::Bmv2;
using ::packetlib::HasHeaderCase;
using ::testing::_;
using ::testing::ElementsAre;
using ::testing::IsEmpty;
using ::testing::Pair;

using PacketsByPort = absl::flat_hash_map<int, packetlib::Packets>;
using VlanTest = testing::TestWithParam<sai::Instantiation>;

constexpr int kIngressPort = 42;
constexpr int kEgressPort = 1;
constexpr absl::string_view kEgressPortProto = "\001";

void PreparePacketOrDie(packetlib::Packet& packet) {
  CHECK_OK(packetlib::PadPacketToMinimumSize(packet).status());  // Crash OK.
  CHECK_OK(
      packetlib::UpdateMissingComputedFields(packet).status());  // Crash OK.
}

packetlib::Packet GetIpv4PacketOrDie() {
  auto packet = gutil::ParseProtoOrDie<packetlib::Packet>(R"pb(
    headers {
      ethernet_header {
        ethernet_destination: "02:03:04:05:06:07"
        ethernet_source: "00:01:02:03:04:05"
        ethertype: "0x0800"  # IPv4
      }
    }
    headers {
      ipv4_header {
        version: "0x4"
        ihl: "0x5"
        dscp: "0x1c"
        ecn: "0x0"
        identification: "0x0000"
        flags: "0x0"
        fragment_offset: "0x0000"
        ttl: "0x20"
        protocol: "0xfe"
        ipv4_source: "192.168.100.2"
        ipv4_destination: "192.168.100.1"
      }
    }
    payload: "Untagged IPv4 packet."
  )pb");
  PreparePacketOrDie(packet);
  return packet;
}

packetlib::Packet GetVlanIpv4PacketOrDie(absl::string_view vid_hexstr) {
  auto packet = gutil::ParseProtoOrDie<packetlib::Packet>(R"pb(
    headers {
      ethernet_header {
        ethernet_destination: "02:03:04:05:06:07"
        ethernet_source: "00:01:02:03:04:05"
        ethertype: "0x8100"  # VLAN
      }
    }
    headers {
      vlan_header {
        priority_code_point: "0x0",
        drop_eligible_indicator: "0x0",
        vlan_identifier: "0x0",
        ethertype: "0x0800"  # IPv4
      }
    }
    headers {
      ipv4_header {
        version: "0x4"
        ihl: "0x5"
        dscp: "0x1c"
        ecn: "0x0"
        identification: "0x0000"
        flags: "0x0"
        fragment_offset: "0x0000"
        ttl: "0x20"
        protocol: "0xfe"
        ipv4_source: "192.168.100.2"
        ipv4_destination: "192.168.100.1"
      }
    }
    payload: "VLAN tagged IPv4 packet."
  )pb");
  packet.mutable_headers()
      ->Mutable(1)
      ->mutable_vlan_header()
      ->set_vlan_identifier(vid_hexstr);
  PreparePacketOrDie(packet);
  return packet;
}

absl::Status InstallEntries(Bmv2& bmv2, pdpi::IrP4Info ir_p4info,
                            sai::TableEntries entries,
                            pdpi::TranslationOptions options = {}) {
  ASSIGN_OR_RETURN(
      std::vector<p4::v1::Entity> pi_entries,
      pdpi::PdTableEntriesToPiEntities(ir_p4info, entries,
                                       // TODO: Remove once switch
                                       // stack supports VLAN features.
                                       {.allow_unsupported = true}));

  return pdpi::InstallPiEntities(&bmv2.P4RuntimeSession(), ir_p4info,
                                 pi_entries);
}

TEST_P(VlanTest, VlanPacketWithNonReservedVidGetsDroppedByDefault) {
  const sai::Instantiation kInstantiation = GetParam();
  const pdpi::IrP4Info kIrP4Info = sai::GetIrP4Info(kInstantiation);
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  // Install entries to forward all IP packets.
  ASSERT_OK(InstallEntries(
      bmv2, kIrP4Info,
      sai::PdEntryBuilder()
          .AddEntriesForwardingIpPacketsToGivenPort(kEgressPortProto)
          .GetDedupedEntries()));

  // Inject VLAN tagged IPv4 test packet.
  ASSERT_OK_AND_ASSIGN(
      PacketsByPort output_by_port,
      bmv2.SendPacket(kIngressPort, GetVlanIpv4PacketOrDie(
                                        /*vid_hexstr=*/"0x002")));

  // The packet must be dropped.
  ASSERT_THAT(output_by_port, IsEmpty());
}

TEST_P(VlanTest, VlanPacketWithVid4095GetsForwardedWithoutVlanTagByDefault) {
  const sai::Instantiation kInstantiation = GetParam();
  const pdpi::IrP4Info kIrP4Info = sai::GetIrP4Info(kInstantiation);
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  // Install entries to forward all IP packets.
  ASSERT_OK(InstallEntries(
      bmv2, kIrP4Info,
      sai::PdEntryBuilder()
          .AddEntriesForwardingIpPacketsToGivenPort(kEgressPortProto)
          .GetDedupedEntries()));

  // Inject VLAN tagged IPv4 test packet.
  ASSERT_OK_AND_ASSIGN(
      PacketsByPort output_by_port,
      bmv2.SendPacket(kIngressPort, GetVlanIpv4PacketOrDie(
                                        /*vid_hexstr=*/"0xFFF")));

  // The packet must be forwarded with no VLAN tag.
  ASSERT_EQ(output_by_port.size(), 1);
  ASSERT_THAT(output_by_port.at(kEgressPort).packets().at(0).headers(),
              ElementsAre(HasHeaderCase(packetlib::Header::kEthernetHeader),
                          HasHeaderCase(packetlib::Header::kIpv4Header)));
}

TEST_P(VlanTest, NonVlanPacketGetsForwardedByDefault) {
  const sai::Instantiation kInstantiation = GetParam();
  const pdpi::IrP4Info kIrP4Info = sai::GetIrP4Info(kInstantiation);
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  // Install entries to forward all IP packets.
  ASSERT_OK(InstallEntries(
      bmv2, kIrP4Info,
      sai::PdEntryBuilder()
          .AddEntriesForwardingIpPacketsToGivenPort(kEgressPortProto)
          .GetDedupedEntries()));

  // Inject IPv4 test packet.
  ASSERT_OK_AND_ASSIGN(PacketsByPort output_by_port,
                       bmv2.SendPacket(kIngressPort, GetIpv4PacketOrDie()));

  // The packet must be forwarded with no VLAN tag.
  ASSERT_EQ(output_by_port.size(), 1);
  ASSERT_THAT(output_by_port.at(kEgressPort).packets().at(0).headers(),
              ElementsAre(HasHeaderCase(packetlib::Header::kEthernetHeader),
                          HasHeaderCase(packetlib::Header::kIpv4Header)));
}

TEST_P(VlanTest,
       VlanPacketWithNonReservedVidGetsFowardedWhenVlanChecksDisabled) {
  const sai::Instantiation kInstantiation = GetParam();
  const pdpi::IrP4Info kIrP4Info = sai::GetIrP4Info(kInstantiation);
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  // Install entries to disable vlan checks and forward all IP packets
  ASSERT_OK(InstallEntries(
      bmv2, kIrP4Info,
      sai::PdEntryBuilder()
          .AddEntriesForwardingIpPacketsToGivenPort(kEgressPortProto)
          .AddDisableVlanChecksEntry()
          .GetDedupedEntries()));

  // Inject VLAN tagged IPv4 test packet.
  ASSERT_OK_AND_ASSIGN(
      PacketsByPort output_by_port,
      bmv2.SendPacket(kIngressPort, GetVlanIpv4PacketOrDie(
                                        /*vid_hexstr=*/"0x002")));

  // The packet must be forwarded.
  ASSERT_EQ(output_by_port.size(), 1);
  // TODO: Add the check when the logic is implemented.
  // // The VLAN header must be removed because default entries rewrite VLAN
  // // to 4095.
  // ASSERT_THAT(output_by_port.at(kEgressPort).packets().at(0).headers(),
  //             ElementsAre(HasHeaderCase(packetlib::Header::kEthernetHeader),
  //                         HasHeaderCase(packetlib::Header::kIpv4Header)));
}

TEST_P(VlanTest, NonVlanPacketGetsFowardedWhenVlanChecksDisabled) {
  const sai::Instantiation kInstantiation = GetParam();
  const pdpi::IrP4Info kIrP4Info = sai::GetIrP4Info(kInstantiation);
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  // Install entries to disable vlan checks and forward all IP packets
  ASSERT_OK(InstallEntries(
      bmv2, kIrP4Info,
      sai::PdEntryBuilder()
          .AddEntriesForwardingIpPacketsToGivenPort(kEgressPortProto)
          .AddDisableVlanChecksEntry()
          .GetDedupedEntries()));

  // Inject IPv4 test packet.
  ASSERT_OK_AND_ASSIGN(PacketsByPort output_by_port,
                       bmv2.SendPacket(kIngressPort, GetIpv4PacketOrDie()));

  // The packet must be forwarded with no VLAN tag.
  ASSERT_EQ(output_by_port.size(), 1);
  ASSERT_THAT(output_by_port.at(kEgressPort).packets().at(0).headers(),
              ElementsAre(HasHeaderCase(packetlib::Header::kEthernetHeader),
                          HasHeaderCase(packetlib::Header::kIpv4Header)));
}

sai::TableEntries EntriesOnlyFowardingPacketsMatchingVlanIdInAclPreIngress(
    absl::string_view vlan_id_hexstr, absl::string_view egress_port) {
  return sai::PdEntryBuilder()
      .AddDisableVlanChecksEntry()
      .AddEntrySettingVrfBasedOnVlanId(vlan_id_hexstr, "vrf-forward")
      .AddEntryAdmittingAllPacketsToL3()
      .AddDefaultRouteForwardingAllPacketsToGivenPort(
          egress_port, sai::IpVersion::kIpv4, "vrf-forward")
      .GetDedupedEntries();
}

INSTANTIATE_TEST_SUITE_P(
    VlanTest, VlanTest, testing::ValuesIn(sai::AllSaiInstantiations()),
    [&](const testing::TestParamInfo<sai::Instantiation>& info) {
      return InstantiationToString(info.param);
    });

}  // namespace
}  // namespace pins
