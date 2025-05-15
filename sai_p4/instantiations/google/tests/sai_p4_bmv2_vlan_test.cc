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

#include "absl/container/flat_hash_map.h"
#include "absl/log/check.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_matchers.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/p4_runtime_session_extras.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_pdpi/packetlib/packetlib_matchers.h"
#include "platforms/networking/p4/p4_infra/bmv2/bmv2.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/test_tools/set_up_bmv2.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"

namespace pins {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::orion::p4::test::Bmv2;
using ::packetlib::HasHeaderCase;
using ::pdpi::HasPacketIn;
using ::pdpi::ParsedPayloadIs;
using ::testing::ElementsAre;
using ::testing::Eq;
using ::testing::IsEmpty;
using ::testing::Key;
using ::testing::SizeIs;

using PacketsByPort = absl::flat_hash_map<int, packetlib::Packets>;
using VlanTest = testing::TestWithParam<sai::Instantiation>;

constexpr int kIngressPort = 2;
constexpr absl::string_view kIngressPortProto = "\002";
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

absl::Status InstallEntries(Bmv2& bmv2, const pdpi::IrP4Info& ir_p4info,
                            const sai::EntryBuilder& entry_builder) {
  return entry_builder.LogPdEntries().InstallDedupedEntities(
      ir_p4info, bmv2.P4RuntimeSession(),
      /*allow_unsupported=*/true);
}

TEST_P(VlanTest, VlanPacketWithNonReservedVidGetsDroppedByDefault) {
  const sai::Instantiation kInstantiation = GetParam();
  const pdpi::IrP4Info kIrP4Info = sai::GetIrP4Info(kInstantiation);
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  // Install entries to forward all IP packets.
  ASSERT_OK(InstallEntries(
      bmv2, kIrP4Info,
      sai::EntryBuilder().AddEntriesForwardingIpPacketsToGivenPort(
          kEgressPortProto)));

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
      sai::EntryBuilder().AddEntriesForwardingIpPacketsToGivenPort(
          kEgressPortProto)));

  // Inject VLAN tagged IPv4 test packet.
  ASSERT_OK_AND_ASSIGN(
      PacketsByPort output_by_port,
      bmv2.SendPacket(kIngressPort, GetVlanIpv4PacketOrDie(
                                        /*vid_hexstr=*/"0xFFF")));

  // The packet must be forwarded with no VLAN tag.
  ASSERT_THAT(output_by_port, ElementsAre(Key(kEgressPort)));
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
      sai::EntryBuilder().AddEntriesForwardingIpPacketsToGivenPort(
          kEgressPortProto)));

  // Inject IPv4 test packet.
  ASSERT_OK_AND_ASSIGN(PacketsByPort output_by_port,
                       bmv2.SendPacket(kIngressPort, GetIpv4PacketOrDie()));

  // The packet must be forwarded with no VLAN tag.
  ASSERT_THAT(output_by_port, ElementsAre(Key(kEgressPort)));
  ASSERT_THAT(output_by_port.at(kEgressPort).packets().at(0).headers(),
              ElementsAre(HasHeaderCase(packetlib::Header::kEthernetHeader),
                          HasHeaderCase(packetlib::Header::kIpv4Header)));
}

TEST_P(VlanTest,
       VlanPacketWithNonReservedVidGetsForwardedWhenVlanChecksDisabled) {
  const sai::Instantiation kInstantiation = GetParam();
  const pdpi::IrP4Info kIrP4Info = sai::GetIrP4Info(kInstantiation);
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  // Install entries to disable vlan checks and forward all IP packets.
  ASSERT_OK(InstallEntries(
      bmv2, kIrP4Info,
      sai::EntryBuilder()
          .AddEntriesForwardingIpPacketsToGivenPort(kEgressPortProto)
          .AddDisableVlanChecksEntry()));

  // Inject VLAN tagged IPv4 test packet.
  ASSERT_OK_AND_ASSIGN(
      PacketsByPort output_by_port,
      bmv2.SendPacket(kIngressPort, GetVlanIpv4PacketOrDie(
                                        /*vid_hexstr=*/"0x002")));

  // The packet must be forwarded.
  ASSERT_THAT(output_by_port, ElementsAre(Key(kEgressPort)));
  ASSERT_THAT(output_by_port.at(kEgressPort).packets().at(0).headers(),
              ElementsAre(HasHeaderCase(packetlib::Header::kEthernetHeader),
                          HasHeaderCase(packetlib::Header::kIpv4Header)));
}

TEST_P(VlanTest, NonVlanPacketGetsForwardedWhenVlanChecksDisabled) {
  const sai::Instantiation kInstantiation = GetParam();
  const pdpi::IrP4Info kIrP4Info = sai::GetIrP4Info(kInstantiation);
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  // Install entries to disable vlan checks and forward all IP packets.
  ASSERT_OK(InstallEntries(
      bmv2, kIrP4Info,
      sai::EntryBuilder()
          .AddEntriesForwardingIpPacketsToGivenPort(kEgressPortProto)
          .AddDisableVlanChecksEntry()));

  // Inject IPv4 test packet.
  ASSERT_OK_AND_ASSIGN(PacketsByPort output_by_port,
                       bmv2.SendPacket(kIngressPort, GetIpv4PacketOrDie()));

  // The packet must be forwarded with no VLAN tag.
  ASSERT_THAT(output_by_port, ElementsAre(Key(kEgressPort)));
  ASSERT_THAT(output_by_port.at(kEgressPort).packets().at(0).headers(),
              ElementsAre(HasHeaderCase(packetlib::Header::kEthernetHeader),
                          HasHeaderCase(packetlib::Header::kIpv4Header)));
}

absl::Status InstallEntriesOnlyForwardingPacketsMatchingVlanIdInAclPreIngress(
    Bmv2& bmv2, const pdpi::IrP4Info& ir_p4info,
    absl::string_view vlan_id_hexstr, absl::string_view egress_port) {
  return InstallEntries(
      bmv2, ir_p4info,
      sai::EntryBuilder()
          .AddDisableVlanChecksEntry()
          .AddEntrySettingVrfBasedOnVlanId(vlan_id_hexstr, "vrf-forward")
          .AddEntryAdmittingAllPacketsToL3()
          .AddDefaultRouteForwardingAllPacketsToGivenPort(
              egress_port, sai::IpVersion::kIpv4, "vrf-forward"));
}

absl::Status InstallEntriesForwardingAndRewritingVlanInRifTable(
    Bmv2& bmv2, const pdpi::IrP4Info& ir_p4info,
    std::optional<std::string> egress_rif_vlan, absl::string_view egress_port,
    bool disable_vlan_checks, bool disable_vlan_rewrite) {
  RETURN_IF_ERROR(
      InstallEntries(bmv2, ir_p4info,
                     sai::EntryBuilder()
                         .AddEntrySettingVrfForAllPackets("vrf-forward")
                         .AddEntryAdmittingAllPacketsToL3()
                         .AddDefaultRouteForwardingAllPacketsToGivenPort(
                             egress_port, sai::IpVersion::kIpv4, "vrf-forward",
                             sai::NexthopRewriteOptions{
                                 .disable_vlan_rewrite = disable_vlan_rewrite,
                                 .egress_rif_vlan = egress_rif_vlan,
                             })));

  if (disable_vlan_checks) {
    return InstallEntries(bmv2, ir_p4info,
                          sai::EntryBuilder().AddDisableVlanChecksEntry());
  }
  return absl::OkStatus();
}

TEST_P(VlanTest,
       SettingNonReservedVidInRifWithoutVlanChecksResultsInPacketWithThatId) {
  const sai::Instantiation kInstantiation = GetParam();
  const pdpi::IrP4Info kIrP4Info = sai::GetIrP4Info(kInstantiation);
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  const std::string kEgressVlan = "0x003";
  ASSERT_OK(InstallEntriesForwardingAndRewritingVlanInRifTable(
      bmv2, kIrP4Info, kEgressVlan, kEgressPortProto,
      /*disable_vlan_checks=*/true, /*disable_vlan_rewrite=*/false));

  {
    // Inject packet without a VLAN tag.
    ASSERT_OK_AND_ASSIGN(PacketsByPort output_by_port,
                         bmv2.SendPacket(kIngressPort, GetIpv4PacketOrDie()));
    // The packet must be forwarded with VLAN kEgressVlan.
    ASSERT_THAT(output_by_port, ElementsAre(Key(kEgressPort)));
    ASSERT_THAT(output_by_port.at(kEgressPort)
                    .packets()
                    .at(0)
                    .headers()
                    .at(1)
                    .vlan_header()
                    .vlan_identifier(),
                Eq(kEgressVlan));
  }
  {
    // Inject VLAN packet with VLAN 0x00b.
    ASSERT_OK_AND_ASSIGN(
        PacketsByPort output_by_port,
        bmv2.SendPacket(kIngressPort, GetVlanIpv4PacketOrDie(
                                          /*vid_hexstr=*/"0x00b")));
    // The packet must be forwarded with VLAN kEgressVlan.
    ASSERT_THAT(output_by_port, ElementsAre(Key(kEgressPort)));
    ASSERT_THAT(output_by_port.at(kEgressPort)
                    .packets()
                    .at(0)
                    .headers()
                    .at(1)
                    .vlan_header()
                    .vlan_identifier(),
                Eq(kEgressVlan));
  }
  {
    // Inject VLAN packet with VLAN 0xfff.
    ASSERT_OK_AND_ASSIGN(
        PacketsByPort output_by_port,
        bmv2.SendPacket(kIngressPort, GetVlanIpv4PacketOrDie(
                                          /*vid_hexstr=*/"0xfff")));
    // The packet must be forwarded with VLAN kEgressVlan.
    ASSERT_THAT(output_by_port, ElementsAre(Key(kEgressPort)));
    ASSERT_THAT(output_by_port.at(kEgressPort)
                    .packets()
                    .at(0)
                    .headers()
                    .at(1)
                    .vlan_header()
                    .vlan_identifier(),
                Eq(kEgressVlan));
  }
}

TEST_P(VlanTest, SettingNonReservedVidInRifWithVlanChecksResultsInDrop) {
  const sai::Instantiation kInstantiation = GetParam();
  const pdpi::IrP4Info kIrP4Info = sai::GetIrP4Info(kInstantiation);
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  const std::string kEgressVlan = "0x003";
  ASSERT_OK(InstallEntriesForwardingAndRewritingVlanInRifTable(
      bmv2, kIrP4Info, kEgressVlan, kEgressPortProto,
      /*disable_vlan_checks=*/false, /*disable_vlan_rewrite=*/false));

  {
    // Inject packet without a VLAN tag.
    ASSERT_OK_AND_ASSIGN(PacketsByPort output_by_port,
                         bmv2.SendPacket(kIngressPort, GetIpv4PacketOrDie()));
    // The packet must be dropped.
    ASSERT_THAT(output_by_port, IsEmpty());
  }
  {
    // Inject VLAN packet with VLAN 0x00b.
    ASSERT_OK_AND_ASSIGN(
        PacketsByPort output_by_port,
        bmv2.SendPacket(kIngressPort, GetVlanIpv4PacketOrDie(
                                          /*vid_hexstr=*/"0x00b")));
    // The packet must be dropped.
    ASSERT_THAT(output_by_port, IsEmpty());
  }
  {
    // Inject VLAN packet with VLAN 0xfff.
    ASSERT_OK_AND_ASSIGN(
        PacketsByPort output_by_port,
        bmv2.SendPacket(kIngressPort, GetVlanIpv4PacketOrDie(
                                          /*vid_hexstr=*/"0xfff")));
    // The packet must be dropped.
    ASSERT_THAT(output_by_port, IsEmpty());
  }
}

TEST_P(VlanTest, SettingVid4095InRifResultsOutputPacketWithNoVlanTag) {
  const sai::Instantiation kInstantiation = GetParam();
  const pdpi::IrP4Info kIrP4Info = sai::GetIrP4Info(kInstantiation);
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  const std::string kEgressVlan = "0xfff";
  ASSERT_OK(InstallEntriesForwardingAndRewritingVlanInRifTable(
      bmv2, kIrP4Info, kEgressVlan, kEgressPortProto,
      /*disable_vlan_checks=*/true, /*disable_vlan_rewrite=*/false));

  {
    // Inject packet without a VLAN tag.
    ASSERT_OK_AND_ASSIGN(PacketsByPort output_by_port,
                         bmv2.SendPacket(kIngressPort, GetIpv4PacketOrDie()));
    // The packet must be forwarded with no VLAN tag.
    ASSERT_THAT(output_by_port, ElementsAre(Key(kEgressPort)));
    ASSERT_THAT(output_by_port.at(kEgressPort).packets().at(0).headers(),
                ElementsAre(HasHeaderCase(packetlib::Header::kEthernetHeader),
                            HasHeaderCase(packetlib::Header::kIpv4Header)));
  }
  {
    // Inject VLAN packet with VLAN 0x00b.
    ASSERT_OK_AND_ASSIGN(
        PacketsByPort output_by_port,
        bmv2.SendPacket(kIngressPort, GetVlanIpv4PacketOrDie(
                                          /*vid_hexstr=*/"0x00b")));
    // The packet must be forwarded with no VLAN tag.
    ASSERT_THAT(output_by_port, ElementsAre(Key(kEgressPort)));
    ASSERT_THAT(output_by_port.at(kEgressPort).packets().at(0).headers(),
                ElementsAre(HasHeaderCase(packetlib::Header::kEthernetHeader),
                            HasHeaderCase(packetlib::Header::kIpv4Header)));
  }
  {
    // Inject VLAN packet with VLAN 0xfff.
    ASSERT_OK_AND_ASSIGN(
        PacketsByPort output_by_port,
        bmv2.SendPacket(kIngressPort, GetVlanIpv4PacketOrDie(
                                          /*vid_hexstr=*/"0xfff")));
    // The packet must be forwarded with no VLAN tag.
    ASSERT_THAT(output_by_port, ElementsAre(Key(kEgressPort)));
    ASSERT_THAT(output_by_port.at(kEgressPort).packets().at(0).headers(),
                ElementsAre(HasHeaderCase(packetlib::Header::kEthernetHeader),
                            HasHeaderCase(packetlib::Header::kIpv4Header)));
  }
}

TEST_P(VlanTest, IngressVidGetCarriedOverToEgressWhenVlanRewriteIsDisabled) {
  const sai::Instantiation kInstantiation = GetParam();
  const pdpi::IrP4Info kIrP4Info = sai::GetIrP4Info(kInstantiation);
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  ASSERT_OK(InstallEntriesForwardingAndRewritingVlanInRifTable(
      bmv2, kIrP4Info, /*egress_rif_vlan=*/std::nullopt, kEgressPortProto,
      /*disable_vlan_checks=*/true, /*disable_vlan_rewrite=*/true));
  {
    // Inject packet without a VLAN tag.
    ASSERT_OK_AND_ASSIGN(PacketsByPort output_by_port,
                         bmv2.SendPacket(kIngressPort, GetIpv4PacketOrDie()));
    // The packet must be forwarded with no VLAN tag.
    ASSERT_THAT(output_by_port, ElementsAre(Key(kEgressPort)));
    ASSERT_THAT(output_by_port.at(kEgressPort).packets().at(0).headers(),
                ElementsAre(HasHeaderCase(packetlib::Header::kEthernetHeader),
                            HasHeaderCase(packetlib::Header::kIpv4Header)));
  }
  {
    // Inject VLAN packet with VLAN 0x00b.
    ASSERT_OK_AND_ASSIGN(
        PacketsByPort output_by_port,
        bmv2.SendPacket(kIngressPort, GetVlanIpv4PacketOrDie(
                                          /*vid_hexstr=*/"0x00b")));
    // The packet must be forwarded with VLAN 0x00b.
    ASSERT_THAT(output_by_port, ElementsAre(Key(kEgressPort)));
    ASSERT_THAT(output_by_port.at(kEgressPort)
                    .packets()
                    .at(0)
                    .headers()
                    .at(1)
                    .vlan_header()
                    .vlan_identifier(),
                Eq("0x00b"));
  }
  {
    // Inject VLAN packet with VLAN 0xfff.
    ASSERT_OK_AND_ASSIGN(
        PacketsByPort output_by_port,
        bmv2.SendPacket(kIngressPort, GetVlanIpv4PacketOrDie(
                                          /*vid_hexstr=*/"0xfff")));
    // The packet must be forwarded with no VLAN tag.
    ASSERT_THAT(output_by_port, ElementsAre(Key(kEgressPort)));
    ASSERT_THAT(output_by_port.at(kEgressPort).packets().at(0).headers(),
                ElementsAre(HasHeaderCase(packetlib::Header::kEthernetHeader),
                            HasHeaderCase(packetlib::Header::kIpv4Header)));
  }
}

TEST_P(VlanTest,
       RifVlanRewriteIsNotEffectiveWhenVlanRewriteIsDisabledInNexthop) {
  const sai::Instantiation kInstantiation = GetParam();
  const pdpi::IrP4Info kIrP4Info = sai::GetIrP4Info(kInstantiation);
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  ASSERT_OK(InstallEntriesForwardingAndRewritingVlanInRifTable(
      bmv2, kIrP4Info, /*egress_rif_vlan=*/"0x00c", kEgressPortProto,
      /*disable_vlan_checks=*/true, /*disable_vlan_rewrite=*/true));

  {
    // Inject packet without a VLAN tag.
    ASSERT_OK_AND_ASSIGN(PacketsByPort output_by_port,
                         bmv2.SendPacket(kIngressPort, GetIpv4PacketOrDie()));
    // The packet must be forwarded with no VLAN tag.
    ASSERT_THAT(output_by_port, ElementsAre(Key(kEgressPort)));
    ASSERT_THAT(output_by_port.at(kEgressPort).packets().at(0).headers(),
                ElementsAre(HasHeaderCase(packetlib::Header::kEthernetHeader),
                            HasHeaderCase(packetlib::Header::kIpv4Header)));
  }
  {
    // Inject VLAN packet with VLAN 0x00b.
    ASSERT_OK_AND_ASSIGN(
        PacketsByPort output_by_port,
        bmv2.SendPacket(kIngressPort, GetVlanIpv4PacketOrDie(
                                          /*vid_hexstr=*/"0x00b")));
    // The packet must be forwarded with VLAN 0x00b.
    ASSERT_THAT(output_by_port, ElementsAre(Key(kEgressPort)));
    ASSERT_THAT(output_by_port.at(kEgressPort)
                    .packets()
                    .at(0)
                    .headers()
                    .at(1)
                    .vlan_header()
                    .vlan_identifier(),
                Eq("0x00b"));
  }
  {
    // Inject VLAN packet with VLAN 0xfff.
    ASSERT_OK_AND_ASSIGN(
        PacketsByPort output_by_port,
        bmv2.SendPacket(kIngressPort, GetVlanIpv4PacketOrDie(
                                          /*vid_hexstr=*/"0xfff")));
    // The packet must be forwarded with no VLAN tag.
    ASSERT_THAT(output_by_port, ElementsAre(Key(kEgressPort)));
    ASSERT_THAT(output_by_port.at(kEgressPort).packets().at(0).headers(),
                ElementsAre(HasHeaderCase(packetlib::Header::kEthernetHeader),
                            HasHeaderCase(packetlib::Header::kIpv4Header)));
  }
}

sai::TableEntries EntriesForwardingAndRewritingVlanInRifTable(
    absl::string_view vlan_id_hexstr, absl::string_view egress_port,
    bool disable_vlan_checks) {
  sai::TableEntries entries =
      sai::EntryBuilder()
          .AddEntrySettingVrfForAllPackets("vrf-forward")
          .AddEntryAdmittingAllPacketsToL3()
          .AddDefaultRouteForwardingAllPacketsToGivenPort(
              egress_port, sai::IpVersion::kIpv4, "vrf-forward",
              /*vlan_hexstr=*/vlan_id_hexstr)
          .GetDedupedEntries();
  if (disable_vlan_checks) {
    *entries.add_entries() = sai::EntryBuilder()
                                 .AddDisableVlanChecksEntry()
                                 .GetDedupedEntries()
                                 .entries()[0];
  }
  return entries;
}

TEST(VlanTest,
     SettingNonReservedVidInRifWithoutVlanChecksResultsInPacketWithThatId) {
  const sai::Instantiation kInstantiation = GetParam();
  const pdpi::IrP4Info kIrP4Info = sai::GetIrP4Info(kInstantiation);
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  constexpr absl::string_view kEgressVlan = "0x003";
  ASSERT_OK(InstallEntries(
      bmv2, kIrP4Info,
      EntriesForwardingAndRewritingVlanInRifTable(
          kEgressVlan, kEgressPortProto, 
          /*disable_vlan_checks=*/true, /*disable_vlan_rewrite=*/false)));
  {
    // Inject packet without a VLAN tag.
    ASSERT_OK_AND_ASSIGN(PacketsByPort output_by_port,
                         bmv2.SendPacket(kIngressPort, GetIpv4PacketOrDie()));
    // The packet must be forwarded with VLAN kEgressVlan.
    ASSERT_THAT(output_by_port, ElementsAre(Key(kEgressPort)));
    ASSERT_THAT(output_by_port.at(kEgressPort)
                    .packets()
                    .at(0)
                    .headers()
                    .at(1)
                    .vlan_header()
                    .vlan_identifier(),
                Eq(kEgressVlan));
  }
  {
    // Inject VLAN packet with VLAN 0x00b.
    ASSERT_OK_AND_ASSIGN(
        PacketsByPort output_by_port,
        bmv2.SendPacket(kIngressPort, GetVlanIpv4PacketOrDie(
                                          /*vid_hexstr=*/"0x00b")));
    // The packet must be forwarded with VLAN kEgressVlan.
    ASSERT_THAT(output_by_port, ElementsAre(Key(kEgressPort)));
    ASSERT_THAT(output_by_port.at(kEgressPort)
                    .packets()
                    .at(0)
                    .headers()
                    .at(1)
                    .vlan_header()
                    .vlan_identifier(),
                Eq(kEgressVlan));
  }
  {
    // Inject VLAN packet with VLAN 0xfff.
    ASSERT_OK_AND_ASSIGN(
        PacketsByPort output_by_port,
        bmv2.SendPacket(kIngressPort, GetVlanIpv4PacketOrDie(
                                          /*vid_hexstr=*/"0xfff")));
    // The packet must be forwarded with VLAN kEgressVlan.
    ASSERT_THAT(output_by_port, ElementsAre(Key(kEgressPort)));
    ASSERT_THAT(output_by_port.at(kEgressPort)
                    .packets()
                    .at(0)
                    .headers()
                    .at(1)
                    .vlan_header()
                    .vlan_identifier(),
                Eq(kEgressVlan));
  }
}

TEST(VlanTest, SettingNonReservedVidInRifWithVlanChecksResultsInDrop) {
  const sai::Instantiation kInstantiation = GetParam();
  const pdpi::IrP4Info kIrP4Info = sai::GetIrP4Info(kInstantiation);
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  constexpr absl::string_view kEgressVlan = "0x003";
  ASSERT_OK(InstallEntries(
      bmv2, kIrP4Info,
      EntriesForwardingAndRewritingVlanInRifTable(
          kEgressVlan, kEgressPortProto, 
          /*disable_vlan_checks=*/false, /*disable_vlan_rewrite=*/false)));
  {
    // Inject packet without a VLAN tag.
    ASSERT_OK_AND_ASSIGN(PacketsByPort output_by_port,
                         bmv2.SendPacket(kIngressPort, GetIpv4PacketOrDie()));
    // The packet must be dropped.
    ASSERT_THAT(output_by_port, IsEmpty());
  }
  {
    // Inject VLAN packet with VLAN 0x00b.
    ASSERT_OK_AND_ASSIGN(
        PacketsByPort output_by_port,
        bmv2.SendPacket(kIngressPort, GetVlanIpv4PacketOrDie(
                                          /*vid_hexstr=*/"0x00b")));
    // The packet must be dropped.
    ASSERT_THAT(output_by_port, IsEmpty());
  }
  {
    // Inject VLAN packet with VLAN 0xfff.
    ASSERT_OK_AND_ASSIGN(
        PacketsByPort output_by_port,
        bmv2.SendPacket(kIngressPort, GetVlanIpv4PacketOrDie(
                                          /*vid_hexstr=*/"0xfff")));
    // The packet must be dropped.
    ASSERT_THAT(output_by_port, IsEmpty());
  }
}

TEST(VlanTest, SettingVid4095InRifResultsOutputPacketWithNoVlanTag) {
  const sai::Instantiation kInstantiation = GetParam();
  const pdpi::IrP4Info kIrP4Info = sai::GetIrP4Info(kInstantiation);
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  const std::string kEgressVlan = "0xfff";
  ASSERT_OK(InstallEntries(
      bmv2, kIrP4Info,
      EntriesForwardingAndRewritingVlanInRifTable(
          kEgressVlan, kEgressPortProto,
          /*disable_vlan_checks=*/true, /*disable_vlan_rewrite=*/false)); 
  {
    // Inject packet without a VLAN tag.
    ASSERT_OK_AND_ASSIGN(PacketsByPort output_by_port,
                         bmv2.SendPacket(kIngressPort, GetIpv4PacketOrDie()));
    // The packet must be forwarded with no VLAN tag.
    ASSERT_THAT(output_by_port, ElementsAre(Key(kEgressPort)));
    ASSERT_THAT(output_by_port.at(kEgressPort).packets().at(0).headers(),
                ElementsAre(HasHeaderCase(packetlib::Header::kEthernetHeader),
                            HasHeaderCase(packetlib::Header::kIpv4Header)));
  }
  {
    // Inject VLAN packet with VLAN 0x00b.
    ASSERT_OK_AND_ASSIGN(
        PacketsByPort output_by_port,
        bmv2.SendPacket(kIngressPort, GetVlanIpv4PacketOrDie(
                                          /*vid_hexstr=*/"0x00b")));
    // The packet must be forwarded with no VLAN tag.
    ASSERT_THAT(output_by_port, ElementsAre(Key(kEgressPort)));
    ASSERT_THAT(output_by_port.at(kEgressPort).packets().at(0).headers(),
                ElementsAre(HasHeaderCase(packetlib::Header::kEthernetHeader),
                            HasHeaderCase(packetlib::Header::kIpv4Header)));
  }
  {
    // Inject VLAN packet with VLAN 0xfff.
    ASSERT_OK_AND_ASSIGN(
        PacketsByPort output_by_port,
        bmv2.SendPacket(kIngressPort, GetVlanIpv4PacketOrDie(
                                          /*vid_hexstr=*/"0xfff")));
    // The packet must be forwarded with no VLAN tag.
    ASSERT_THAT(output_by_port, ElementsAre(Key(kEgressPort)));
    ASSERT_THAT(output_by_port.at(kEgressPort).packets().at(0).headers(),
                ElementsAre(HasHeaderCase(packetlib::Header::kEthernetHeader),
                            HasHeaderCase(packetlib::Header::kIpv4Header)));
  }
}

// VLAN-tagged punt packets keep their VLAN tags regardless of their IDs.
TEST(ButerTorVlanTest, VlanPreservedForPuntedPackets) {
  const sai::Instantiation kInstantiation = sai::Instantiation::kTor;
  const pdpi::IrP4Info kIrP4Info = sai::GetIrP4Info(kInstantiation);
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));
  ASSERT_OK(sai::EntryBuilder()
                .AddEntryPuntingAllPackets(sai::PuntAction::kTrap)
                .InstallDedupedEntities(kIrP4Info, bmv2.P4RuntimeSession()));

  constexpr absl::string_view kNonReservedVlanId = "0x123";
  constexpr absl::string_view kReservedVlanId = "0xfff";

  ASSERT_OK(bmv2.SendPacket(kIngressPort,
                            GetVlanIpv4PacketOrDie(kNonReservedVlanId)));
  ASSERT_OK(
      bmv2.SendPacket(kIngressPort, GetVlanIpv4PacketOrDie(kReservedVlanId)));

  EXPECT_THAT(bmv2.P4RuntimeSession().ReadStreamChannelResponsesAndFinish(),
              IsOkAndHolds(ElementsAre(
                  HasPacketIn(ParsedPayloadIs(
                      EqualsProto(GetVlanIpv4PacketOrDie(kNonReservedVlanId)))),
                  HasPacketIn(ParsedPayloadIs(
                      EqualsProto(GetVlanIpv4PacketOrDie(kReservedVlanId)))))));
}

INSTANTIATE_TEST_SUITE_P(
    VlanTest, VlanTest, testing::ValuesIn(sai::AllSaiInstantiations()),
    [&](const testing::TestParamInfo<sai::Instantiation>& info) {
      return InstantiationToString(info.param);
    });

sai::MirrorSessionParams GetMirrorSessionParamsForTest() {
  return sai::MirrorSessionParams{
      .mirror_session_id = "mirror_session_id",
      .monitor_port = std::string(kEgressPortProto),
      .mirror_encap_src_mac = "00:08:08:08:08:08",
      .mirror_encap_dst_mac = "01:09:09:09:09:09",
      .mirror_encap_vlan_id = "0x123",
      .mirror_encap_src_ip = "::1",
      .mirror_encap_dst_ip = "::2",
      .mirror_encap_udp_src_port = "0x1234",
      .mirror_encap_udp_dst_port = "0x1283",
  };
}

// When VLAN checks are enabled, vlan-encapped mirror packets with non-reserved
// vlan id should not be mirrored.
// Only test ToR instantiation since only it supports
// acl_ingress_mirror_and_redirect_table.
TEST(MirrorVlanTest,
     IpfixEncappedMirroredPktWithNonReservedVidIsDroppedWhenVlanChecksEnabled) {
  const sai::Instantiation kInstantiation = sai::Instantiation::kTor;
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));
  sai::MirrorSessionParams mirror_session_params =
      GetMirrorSessionParamsForTest();
  // Encap the mirrored packet with non-reserved vlan id.
  mirror_session_params.mirror_encap_vlan_id = "0x123";

  ASSERT_OK(
      sai::EntryBuilder()
          .AddMirrorSessionTableEntry(mirror_session_params)
          .AddMarkToMirrorAclEntry(sai::MarkToMirrorParams{
              .ingress_port = std::string(kIngressPortProto),
              .mirror_session_id = mirror_session_params.mirror_session_id,
          })
          .InstallDedupedEntities(sai::GetIrP4Info(kInstantiation),
                                  bmv2.P4RuntimeSession(),
                                  /*allow_unsupported=*/true));
  packetlib::Packet input_packet = GetIpv4PacketOrDie();

  ASSERT_OK_AND_ASSIGN(auto outputs,
                       bmv2.SendPacket(kIngressPort, input_packet));
  ASSERT_THAT(outputs, IsEmpty());
}

// When VLAN checks are enabled, vlan-encapped mirror packets with reserved
// vlan id should be mirrored.
// Only test ToR instantiation since only it supports
// acl_ingress_mirror_and_redirect_table.
TEST(
    MirrorVlanTest,
    IpfixEncappedMirroredCopyWithVid4095EgressWithoutTagWhenVlanChecksEnabled) {
  const sai::Instantiation kInstantiation = sai::Instantiation::kTor;
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));
  sai::MirrorSessionParams mirror_session_params =
      GetMirrorSessionParamsForTest();
  // Encap the mirrored packet with reserved vlan id.
  mirror_session_params.mirror_encap_vlan_id = "0xfff";

  ASSERT_OK(
      sai::EntryBuilder()
          .AddMirrorSessionTableEntry(mirror_session_params)
          .AddMarkToMirrorAclEntry(sai::MarkToMirrorParams{
              .ingress_port = std::string(kIngressPortProto),
              .mirror_session_id = mirror_session_params.mirror_session_id,
          })
          .InstallDedupedEntities(sai::GetIrP4Info(kInstantiation),
                                  bmv2.P4RuntimeSession(),
                                  /*allow_unsupported=*/true));
  packetlib::Packet input_packet = GetIpv4PacketOrDie();

  ASSERT_OK_AND_ASSIGN(auto outputs,
                       bmv2.SendPacket(kIngressPort, input_packet));
  ASSERT_THAT(outputs, ElementsAre(Key(kEgressPort)));
  ASSERT_THAT(outputs[kEgressPort].packets(), SizeIs(1));
  EXPECT_THAT(outputs[kEgressPort]
                  .packets()
                  .at(0)
                  .headers()
                  .at(1)
                  .vlan_header()
                  .vlan_identifier(),
              Eq(mirror_session_params.mirror_encap_vlan_id));
}

// When VLAN checks are disabled, vlan-encapped mirror packets with VLAN ID are
// mirrored.
// Only test ToR instantiation since only it supports
// acl_ingress_mirror_and_redirect_table.
TEST(
    MirrorVlanTest,
    EncappedMirroredCopyWithNonReservedVidEgressWithTagWhenVlanChecksDisabled) {
  const sai::Instantiation kInstantiation = sai::Instantiation::kTor;
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  sai::MirrorSessionParams mirror_session_params =
      GetMirrorSessionParamsForTest();
  // Encap the mirrored packet with non-reserved vlan id.
  mirror_session_params.mirror_encap_vlan_id = "0x123";

  ASSERT_OK(sai::EntryBuilder()
                .AddDisableVlanChecksEntry()
                .AddMirrorSessionTableEntry(GetMirrorSessionParamsForTest())
                .AddMarkToMirrorAclEntry(sai::MarkToMirrorParams{
                    .ingress_port = std::string(kIngressPortProto),
                    .mirror_session_id =
                        GetMirrorSessionParamsForTest().mirror_session_id,
                })
                .InstallDedupedEntities(sai::GetIrP4Info(kInstantiation),
                                        bmv2.P4RuntimeSession(),
                                        /*allow_unsupported=*/true));
  packetlib::Packet input_packet = GetIpv4PacketOrDie();

  ASSERT_OK_AND_ASSIGN(auto outputs,
                       bmv2.SendPacket(kIngressPort, input_packet));
  ASSERT_THAT(outputs, ElementsAre(Key(kEgressPort)));
  ASSERT_THAT(outputs[kEgressPort].packets(), SizeIs(1));
  EXPECT_THAT(outputs[kEgressPort]
                  .packets()
                  .at(0)
                  .headers()
                  .at(1)
                  .vlan_header()
                  .vlan_identifier(),
              Eq(mirror_session_params.mirror_encap_vlan_id));
}
}  // namespace
}  // namespace pins
