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
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/netaddr/ipv4_address.h"
#include "p4_pdpi/netaddr/mac_address.h"
#include "p4_pdpi/p4_runtime_session_extras.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "platforms/networking/p4/p4_infra/bmv2/bmv2.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/test_tools/set_up_bmv2.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"

namespace pins {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::gutil::ProtoDiff;
using ::orion::p4::test::Bmv2;
using ::testing::ElementsAre;
using ::testing::Key;
using ::testing::SizeIs;
using ::testing::StrEq;
using ::testing::UnorderedElementsAre;

using PacketsByPort = absl::flat_hash_map<int, packetlib::Packets>;

void PreparePacketOrDie(packetlib::Packet& packet) {
  CHECK_OK(packetlib::PadPacketToMinimumSize(packet).status());  // Crash OK.
  CHECK_OK(
      packetlib::UpdateMissingComputedFields(packet).status());  // Crash OK.
}

packetlib::Packet GetIpv4PacketOrDie(
    netaddr::Ipv4Address ipv4_dst = netaddr::Ipv4Address(192, 168, 100, 1),
    netaddr::MacAddress mac_dst = netaddr::MacAddress(2, 3, 4, 5, 6, 7)) {
  auto packet = gutil::ParseProtoOrDie<packetlib::Packet>(R"pb(
    headers {
      ethernet_header {
        ethernet_destination: "filled in below"
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
        ipv4_destination: "filled in below"
      }
    }
    payload: "Untagged IPv4 packet."
  )pb");
  packet.mutable_headers(0)
      ->mutable_ethernet_header()
      ->set_ethernet_destination(mac_dst.ToString());
  packet.mutable_headers(1)->mutable_ipv4_header()->set_ipv4_destination(
      ipv4_dst.ToString());
  PreparePacketOrDie(packet);
  return packet;
}

TEST(RedirectTest, RedirectToNextHopOverridesLpmDecision) {
  const sai::Instantiation kInstantiation = GetParam();
  const pdpi::IrP4Info kIrP4Info = sai::GetIrP4Info(kInstantiation);
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  constexpr int kIngressPort = 42;
  constexpr int kEgressPort = 1;
  constexpr absl::string_view kEgressPortProto = "\001";

  constexpr int kRedirectIngressPort = 2;
  constexpr absl::string_view kRedirectIngressPortProto = "\002";
  constexpr int kRedirectEgressPort = 3;
  constexpr absl::string_view kRedirectEgressPortProto = "\003";

  constexpr absl::string_view kRedirectNexthopId = "redirect-nexthop";

  // Install entries to forwards all packets to kEgressPort and redirect
  // the ones with in_port kRedirectIngressPort to kRedirectEgressPort.
  ASSERT_OK_AND_ASSIGN(
      std::vector<p4::v1::Entity> pi_entities,
      sai::EntryBuilder()
          .AddEntriesForwardingIpPacketsToGivenPort(kEgressPortProto)
          .AddIngressAclEntryRedirectingToNexthop(
              kRedirectNexthopId,
              /*in_port_match=*/kRedirectIngressPortProto)
          .AddNexthopRifNeighborEntries(kRedirectNexthopId,
                                        kRedirectEgressPortProto)
          .LogPdEntries()
          .GetDedupedPiEntities(kIrP4Info, /*allow_unsupported=*/true));
  ASSERT_OK(pdpi::InstallPiEntities(bmv2.P4RuntimeSession(), pi_entities));

  {
    // Inject a test packet to kIngressPort.
    ASSERT_OK_AND_ASSIGN(PacketsByPort output_by_port,
                         bmv2.SendPacket(kIngressPort, GetIpv4PacketOrDie()));
    // The packet must be forwarded to kEgressPort
    ASSERT_THAT(output_by_port, ElementsAre(Key(kEgressPort)));
  }
  {
    // Inject a test packet to kRedirectIngressPort.
    ASSERT_OK_AND_ASSIGN(
        PacketsByPort output_by_port,
        bmv2.SendPacket(kRedirectIngressPort, GetIpv4PacketOrDie()));
    // The packet must be forwarded to kRedirectEgressPort.
    ASSERT_THAT(output_by_port, ElementsAre(Key(kRedirectEgressPort)));
  }
}

TEST(RedirectTest, RedirectToNextHopOverridesIpMulticastDecision) {
  const sai::Instantiation kInstantiation = GetParam();
  const pdpi::IrP4Info kIrP4Info = sai::GetIrP4Info(kInstantiation);
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  constexpr int kIngressPort = 42;
  constexpr int kMulticastEgressPort1 = 5;
  constexpr absl::string_view kMulticastEgressPort1Proto = "\005";
  constexpr int kMulticastEgressPort2 = 6;
  constexpr absl::string_view kMulticastEgressPort2Proto = "\006";

  constexpr int kRedirectIngressPort = 2;
  constexpr absl::string_view kRedirectIngressPortProto = "\002";
  constexpr int kRedirectEgressPort = 3;
  constexpr absl::string_view kRedirectEgressPortProto = "\003";

  constexpr absl::string_view kRedirectNexthopId = "redirect-nexthop";
  constexpr absl::string_view kVrf = "vrf";
  constexpr int kMulticastGroupId = 50;
  constexpr auto kDstIpv4 = netaddr::Ipv4Address(232, 1, 2, 3);
  // IPv4 multicast MAC address.
  constexpr auto kDstMac = netaddr::MacAddress(0x01, 0, 0x5e, 0x01, 0x02, 0x03);

  // Install entries to multicast packets destined to kDstIpv4 to
  // kMulticastEgressPort{1,2} and redirect the ones with in_port
  // kRedirectIngressPort to kRedirectEgressPort.
  ASSERT_OK_AND_ASSIGN(
      std::vector<p4::v1::Entity> pi_entities,
      sai::EntryBuilder()
          // Multicast entries.
          .AddVrfEntry(kVrf)
          .AddEntryAdmittingAllPacketsToL3()
          .AddEntrySettingVrfForAllPackets(kVrf)
          .AddMulticastRoute(kVrf, kDstIpv4, kMulticastGroupId)
          .AddMulticastGroupEntry(
              kMulticastGroupId,
              {
                  sai::Replica{.egress_port =
                                   std::string(kMulticastEgressPort1Proto)},
                  sai::Replica{.egress_port =
                                   std::string(kMulticastEgressPort2Proto)},
              })
          .AddMulticastRouterInterfaceEntry({
              .multicast_replica_port = std::string(kMulticastEgressPort1Proto),
          })
          .AddMulticastRouterInterfaceEntry({
              .multicast_replica_port = std::string(kMulticastEgressPort2Proto),
          })
          // Redirect entries.
          .AddIngressAclEntryRedirectingToNexthop(
              kRedirectNexthopId,
              /*in_port_match=*/kRedirectIngressPortProto)
          .AddNexthopRifNeighborEntries(kRedirectNexthopId,
                                        kRedirectEgressPortProto)
          .LogPdEntries()
          .GetDedupedPiEntities(kIrP4Info, /*allow_unsupported=*/true));
  ASSERT_OK(pdpi::InstallPiEntities(bmv2.P4RuntimeSession(), pi_entities));

  {
    // Inject a test packet destined to kDstIpv4 though kIngressPort.
    ASSERT_OK_AND_ASSIGN(
        PacketsByPort output_by_port,
        bmv2.SendPacket(kIngressPort, GetIpv4PacketOrDie(kDstIpv4, kDstMac)));
    // The packet must be multicast replicated to kMulticastEgressPort{1,2}.
    ASSERT_THAT(output_by_port,
                UnorderedElementsAre(Key(kMulticastEgressPort1),
                                     Key(kMulticastEgressPort2)));
  }
  {
    // Inject a test packet destined to kDstIpv4 though kRedirectIngressPort.
    ASSERT_OK_AND_ASSIGN(
        PacketsByPort output_by_port,
        bmv2.SendPacket(kRedirectIngressPort,
                        GetIpv4PacketOrDie(kDstIpv4, kDstMac)));
    // The packet must be forwarded to kRedirectEgressPort.
    ASSERT_THAT(output_by_port, ElementsAre(Key(kRedirectEgressPort)));
  }
}

TEST(RedirectTest, RedirectToMulticastGroupMulticastsPacket) {
  const sai::Instantiation kInstantiation = sai::Instantiation::kTor;
  const pdpi::IrP4Info kIrP4Info = sai::GetIrP4Info(kInstantiation);
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  ASSERT_OK_AND_ASSIGN(
      std::vector<p4::v1::Entity> pi_entities,
      sai::EntryBuilder()
          .AddIngressAclEntryRedirectingToMulticastGroup(42)
          .AddMulticastGroupEntry(42,
                                  {
                                      sai::Replica{.egress_port = "\1"},
                                      sai::Replica{.egress_port = "\2"},
                                  })
          .LogPdEntries()
          .GetDedupedPiEntities(kIrP4Info, /*allow_unsupported=*/true));
  ASSERT_OK(pdpi::InstallPiEntities(bmv2.P4RuntimeSession(), pi_entities));

  const packetlib::Packet input_packet = GetIpv4PacketOrDie();
  ASSERT_OK_AND_ASSIGN(PacketsByPort output_by_port,
                       bmv2.SendPacket(/*ingress_port=*/123, input_packet));
  ASSERT_THAT(output_by_port, UnorderedElementsAre(Key(1), Key(2)));
  ASSERT_THAT(output_by_port[1].packets(), SizeIs(1));
  ASSERT_THAT(output_by_port[2].packets(), SizeIs(1));
  EXPECT_THAT(output_by_port[1].packets(0),
              EqualsProto(output_by_port[2].packets(0)));
  EXPECT_THAT(ProtoDiff(input_packet, output_by_port[1].packets(0)),
              IsOkAndHolds(StrEq(
                  R"(modified: headers[1].ipv4_header.ttl: "0x20" -> "0x1f"
modified: headers[1].ipv4_header.checksum: "0x500e" -> "0x510e"
)")));
}

TEST(RedirectTest, RedirectToMulticastGroupOverridesMulticastTableAction) {
  const sai::Instantiation kInstantiation = sai::Instantiation::kTor;
  const pdpi::IrP4Info kIrP4Info = sai::GetIrP4Info(kInstantiation);
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  static constexpr int kDefaultIngressPort = 1;
  static constexpr int kOverrideIngressPort = 2;
  static constexpr absl::string_view kOverrideIngressPortStr = "\2";
  static constexpr int kDefaultMulticastGroupId = 1;
  static constexpr int kOverrideMulticastGroupId = 2;
  constexpr auto kDstIpv4 = netaddr::Ipv4Address(232, 1, 2, 3);
  // IPv4 multicast MAC address.
  constexpr auto kDstMac = netaddr::MacAddress(0x01, 0, 0x5e, 0x01, 0x02, 0x03);

  ASSERT_OK_AND_ASSIGN(
      std::vector<p4::v1::Entity> pi_entities,
      sai::EntryBuilder()
          .AddVrfEntry("vrf")
          .AddEntrySettingVrfForAllPackets("vrf")
          .AddEntryAdmittingAllPacketsToL3()
          .AddMulticastRoute("vrf", kDstIpv4, kDefaultMulticastGroupId)
          .AddIngressAclEntryRedirectingToMulticastGroup(
              kOverrideMulticastGroupId,
              sai::MirrorAndRedirectMatchFields{
                  .in_port = kOverrideIngressPortStr,
              })
          .AddMulticastGroupEntry(kDefaultMulticastGroupId,
                                  {
                                      sai::Replica{.egress_port = "\1"},
                                  })
          .AddMulticastGroupEntry(kOverrideMulticastGroupId,
                                  {
                                      sai::Replica{.egress_port = "\2"},
                                      sai::Replica{.egress_port = "\3"},
                                  })
          .LogPdEntries()
          .GetDedupedPiEntities(kIrP4Info, /*allow_unsupported=*/true));
  ASSERT_OK(pdpi::InstallPiEntities(bmv2.P4RuntimeSession(), pi_entities));

  const packetlib::Packet kInputPacket = GetIpv4PacketOrDie(kDstIpv4, kDstMac);
  ASSERT_THAT(bmv2.SendPacket(kDefaultIngressPort, kInputPacket),
              IsOkAndHolds(UnorderedElementsAre(Key(1))));
  ASSERT_THAT(bmv2.SendPacket(kOverrideIngressPort, kInputPacket),
              IsOkAndHolds(UnorderedElementsAre(Key(2), Key(3))));
}

}  // namespace
}  // namespace pins
