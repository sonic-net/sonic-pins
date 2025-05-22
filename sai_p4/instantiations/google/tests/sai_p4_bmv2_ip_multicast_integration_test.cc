// Tests that IP multicast functions as intended on BMv2.

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
#include <utility>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto.h"
#include "gutil/proto_matchers.h"
#include "gutil/proto_ordering.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/netaddr/ipv4_address.h"
#include "p4_pdpi/netaddr/ipv6_address.h"
#include "p4_pdpi/netaddr/mac_address.h"
#include "p4_pdpi/p4_runtime_session_extras.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_pdpi/string_encodings/hex_string.h"
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
using ::testing::IsEmpty;
using ::testing::Key;
using ::testing::Not;
using ::testing::SizeIs;
using ::testing::StrEq;
using ::testing::UnorderedElementsAre;

enum class DstIpKind {
  kUnicast,
  kMulticast,
};

// Returns a "source-specific multicast" address, see
// https://en.wikipedia.org/wiki/Multicast_address#IPv4
netaddr::Ipv4Address MulticastIpv4() {
  return netaddr::Ipv4Address(232, 1, 2, 3);
}

// "Source-specific multicast" address, see
// https://en.wikipedia.org/wiki/Multicast_address#IPv6
netaddr::Ipv6Address MulticastIpv6() {
  return netaddr::Ipv6Address::OfString("ff30::2").value();
}

// Adds a VLAN header with the given `vlan_id` to the given packet.
absl::Status AddVlanHeader(int vlan_id, packetlib::Packet& packet) {
  if (packet.headers_size() < 1 || !packet.headers(0).has_ethernet_header()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "expected packet starting with Ethernet header, but got "
           << absl::StrCat(packet);
  }
  packetlib::EthernetHeader& ethernet_header =
      *packet.mutable_headers(0)->mutable_ethernet_header();

  // Define VLAN header.
  packetlib::VlanHeader vlan_header;
  vlan_header.set_priority_code_point("0x0");
  vlan_header.set_drop_eligible_indicator("0x0");
  vlan_header.set_vlan_identifier(pdpi::BitsetToHexString<12>(vlan_id));
  vlan_header.set_ethertype(ethernet_header.ethertype());

  // Insert VLAN header at index 1.
  ethernet_header.set_ethertype("0x8100");
  {
    packetlib::Header next_header;
    *next_header.mutable_vlan_header() = std::move(vlan_header);
    for (int i = 1; i < packet.headers_size(); ++i) {
      next_header.Swap(packet.mutable_headers(i));
    }
    *packet.add_headers() = std::move(next_header);
  }

  return absl::OkStatus();
}

absl::StatusOr<packetlib::Packet> GetIpv4TestPacket(
    const netaddr::Ipv4Address& dst_ip, const std::optional<int>& vlan_id) {
  ASSIGN_OR_RETURN(auto packet, gutil::ParseTextProto<packetlib::Packet>(R"pb(
                     headers {
                       ethernet_header {
                         # IPv4 Multicast MAC.
                         ethernet_destination: "01:00:5e:05:06:07"
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
                         protocol: "0xfe"  # For experimental use.
                         ipv4_source: "192.168.100.2"
                         ipv4_destination: "TBD"
                       }
                     }
                     payload: "A beautiful IPv4 test packet with great payload."
                   )pb"));
  packet.mutable_headers(1)->mutable_ipv4_header()->set_ipv4_destination(
      dst_ip.ToString());
  if (vlan_id.has_value()) {
    RETURN_IF_ERROR(AddVlanHeader(*vlan_id, packet));
  }
  RETURN_IF_ERROR(packetlib::UpdateAllComputedFields(packet).status());
  RETURN_IF_ERROR(packetlib::ValidatePacket(packet));
  return packet;
}

absl::StatusOr<packetlib::Packet> GetIpv6TestPacket(
    const netaddr::Ipv6Address& dst_ip, const std::optional<int>& vlan_id) {
  ASSIGN_OR_RETURN(auto packet, gutil::ParseTextProto<packetlib::Packet>(R"pb(
                     headers {
                       ethernet_header {
                         # IPv6 Multicast MAC.
                         ethernet_destination: "33:33:04:05:06:07"
                         ethernet_source: "00:01:02:03:04:05"
                         ethertype: "0x86dd"  # IPv6
                       }
                     }
                     headers {
                       ipv6_header {
                         version: "0x6"
                         dscp: "0x00"
                         ecn: "0x0"
                         flow_label: "0x12345"
                         next_header: "0xfe"  # For experimental use.
                         hop_limit: "0x03"
                         ipv6_source: "2001::1"
                         ipv6_destination: "TBD"
                       }
                     }
                     payload: "A beautiful IPv6 test packet with great payload."
                   )pb"));
  packet.mutable_headers(1)->mutable_ipv6_header()->set_ipv6_destination(
      dst_ip.ToString());
  if (vlan_id.has_value()) {
    RETURN_IF_ERROR(AddVlanHeader(*vlan_id, packet));
  }
  RETURN_IF_ERROR(packetlib::UpdateAllComputedFields(packet).status());
  RETURN_IF_ERROR(packetlib::ValidatePacket(packet));
  return packet;
}

struct TestParams {
  sai::Instantiation instantiation;
  // If set, test packets will include a VLAN header with the given ID.
  std::optional<int> test_packet_vlan_id;
};

using IpMulticastTest = ::testing::TestWithParam<TestParams>;

TEST_P(IpMulticastTest, Ipv4PacketsGetMulticastedWithRewrittenSrcMacAndTtl) {
  const sai::Instantiation kInstantiation = GetParam().instantiation;
  const pdpi::IrP4Info kIrP4Info = sai::GetIrP4Info(kInstantiation);
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  // Install table entries.
  constexpr absl::string_view kVrf = "vrf";
  const netaddr::Ipv4Address kDstIp = MulticastIpv4();
  constexpr int kMulticastGroupId = 42;
  ASSERT_OK(sai::EntryBuilder()
                .AddVrfEntry(kVrf)
                .AddEntryAdmittingAllPacketsToL3()
                .AddEntrySettingVrfForAllPackets(kVrf)
                .AddMulticastRoute(kVrf, kDstIp, kMulticastGroupId)
                .AddMulticastGroupEntry(
                    kMulticastGroupId,
                    {
                        sai::Replica{.egress_port = "\1", .instance = 0},
                        sai::Replica{.egress_port = "\1", .instance = 1},
                        sai::Replica{.egress_port = "\1", .instance = 2},
                        sai::Replica{.egress_port = "\2", .instance = 0},
                    })
                .AddMulticastRouterInterfaceEntry({
                    .multicast_replica_port = "\1",
                    .multicast_replica_instance = 0,
                    .src_mac = netaddr::MacAddress(1, 0, 0, 0, 0, 0),
                })
                .AddMulticastRouterInterfaceEntry({
                    .multicast_replica_port = "\1",
                    .multicast_replica_instance = 1,
                    .src_mac = netaddr::MacAddress(1, 0, 0, 0, 0, 1),
                })
                .AddMulticastRouterInterfaceEntry({
                    .multicast_replica_port = "\1",
                    .multicast_replica_instance = 2,
                    .src_mac = netaddr::MacAddress(1, 0, 0, 0, 0, 2),
                })
                .AddMulticastRouterInterfaceEntry({
                    .multicast_replica_port = "\2",
                    .multicast_replica_instance = 0,
                    .src_mac = netaddr::MacAddress(2, 0, 0, 0, 0, 0x42),
                })
                // Technically only needed when `GetParam().test_packet_vlan_id`
                // is set.
                .AddDisableVlanChecksEntry()
                .LogPdEntries()
                .InstallDedupedEntities(kIrP4Info, bmv2.P4RuntimeSession()));

  // Send Ipv4 test packet and expect output packets on egress ports 1 and 2.
  ASSERT_OK_AND_ASSIGN(
      const packetlib::Packet ipv4_test_packet,
      GetIpv4TestPacket(kDstIp, GetParam().test_packet_vlan_id));
  constexpr int kArbitraryIngressPort = 24;
  ASSERT_OK_AND_ASSIGN(
      (absl::flat_hash_map<int, packetlib::Packets>
           output_packets_by_egress_port),
      bmv2.SendPacket(kArbitraryIngressPort, ipv4_test_packet));
  ASSERT_THAT(output_packets_by_egress_port,
              UnorderedElementsAre(Key(1), Key(2)));
  auto port1_output_packets = output_packets_by_egress_port[1].packets();
  auto port2_output_packets = output_packets_by_egress_port[2].packets();

  // Check that output packets at port 1 are as expected.
  ASSERT_THAT(port1_output_packets, SizeIs(3));
  gutil::InefficientProtoSort(port1_output_packets);
  EXPECT_THAT(
      gutil::ProtoDiff(ipv4_test_packet, port1_output_packets[0]),
      IsOkAndHolds(StrEq(
          GetParam().test_packet_vlan_id.has_value()
              ?
              R"(modified: headers[0].ethernet_header.ethernet_source: "00:01:02:03:04:05" -> "01:00:00:00:00:00"
modified: headers[2].ipv4_header.ttl: "0x20" -> "0x1f"
modified: headers[2].ipv4_header.checksum: "0x8a9d" -> "0x8b9d"
)"
              :
              R"(modified: headers[0].ethernet_header.ethernet_source: "00:01:02:03:04:05" -> "01:00:00:00:00:00"
modified: headers[1].ipv4_header.ttl: "0x20" -> "0x1f"
modified: headers[1].ipv4_header.checksum: "0x8a9d" -> "0x8b9d"
)")));
  // The multicast copies should differ only in their source mac.
  EXPECT_THAT(
      gutil::ProtoDiff(port1_output_packets[0], port1_output_packets[1]),
      IsOkAndHolds(StrEq(
          R"(modified: headers[0].ethernet_header.ethernet_source: "01:00:00:00:00:00" -> "01:00:00:00:00:01"
)")));
  EXPECT_THAT(
      gutil::ProtoDiff(port1_output_packets[0], port1_output_packets[2]),
      IsOkAndHolds(StrEq(
          R"(modified: headers[0].ethernet_header.ethernet_source: "01:00:00:00:00:00" -> "01:00:00:00:00:02"
)")));

  // Check that output packets at port 2 are as expected.
  ASSERT_THAT(port2_output_packets, SizeIs(1));
  EXPECT_THAT(
      gutil::ProtoDiff(port1_output_packets[0], port2_output_packets[0]),
      IsOkAndHolds(StrEq(
          R"(modified: headers[0].ethernet_header.ethernet_source: "01:00:00:00:00:00" -> "02:00:00:00:00:42"
)")));
}

TEST_P(IpMulticastTest, Ipv6PacketsGetMulticastedWithRewrittenSrcMacAndTtl) {
  const sai::Instantiation kInstantiation = GetParam().instantiation;
  const pdpi::IrP4Info kIrP4Info = sai::GetIrP4Info(kInstantiation);
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  // Install table entries.
  constexpr absl::string_view kVrf = "vrf";
  const netaddr::Ipv6Address kDstIp = MulticastIpv6();
  constexpr int kMulticastGroupId = 42;
  ASSERT_OK(sai::EntryBuilder()
                .AddVrfEntry(kVrf)
                .AddEntryAdmittingAllPacketsToL3()
                .AddEntrySettingVrfForAllPackets(kVrf)
                .AddMulticastRoute(kVrf, kDstIp, kMulticastGroupId)
                .AddMulticastGroupEntry(
                    kMulticastGroupId,
                    {
                        sai::Replica{.egress_port = "\7", .instance = 0},
                        sai::Replica{.egress_port = "\7", .instance = 1234},
                        sai::Replica{.egress_port = "\5", .instance = 0},
                    })
                .AddMulticastRouterInterfaceEntry({
                    .multicast_replica_port = "\7",
                    .multicast_replica_instance = 0,
                    .src_mac = netaddr::MacAddress(7, 7, 7, 7, 7, 7),
                })
                .AddMulticastRouterInterfaceEntry({
                    .multicast_replica_port = "\7",
                    .multicast_replica_instance = 1234,
                    .src_mac = netaddr::MacAddress(7, 7, 7, 7, 7, 7),
                })
                .AddMulticastRouterInterfaceEntry({
                    .multicast_replica_port = "\5",
                    .multicast_replica_instance = 0,
                    .src_mac = netaddr::MacAddress(5, 5, 5, 5, 5, 5),
                })
                // Technically only needed when `GetParam().test_packet_vlan_id`
                // is set.
                .AddDisableVlanChecksEntry()
                .LogPdEntries()
                .InstallDedupedEntities(kIrP4Info, bmv2.P4RuntimeSession()));

  // Send Ipv6 test packet and expect output packets on egress ports 7 and 5.
  ASSERT_OK_AND_ASSIGN(
      const packetlib::Packet ipv6_test_packet,
      GetIpv6TestPacket(kDstIp, GetParam().test_packet_vlan_id));
  constexpr int kArbitraryIngressPort = 24;
  ASSERT_OK_AND_ASSIGN(
      (absl::flat_hash_map<int, packetlib::Packets>
           output_packets_by_egress_port),
      bmv2.SendPacket(kArbitraryIngressPort, ipv6_test_packet));
  ASSERT_THAT(output_packets_by_egress_port,
              UnorderedElementsAre(Key(7), Key(5)));
  auto port7_output_packets = output_packets_by_egress_port[7].packets();
  auto port5_output_packets = output_packets_by_egress_port[5].packets();

  // Check that output packets at port 7 are as expected.
  ASSERT_THAT(port7_output_packets, SizeIs(2));
  EXPECT_THAT(port7_output_packets[0], EqualsProto(port7_output_packets[1]));
  EXPECT_THAT(
      gutil::ProtoDiff(ipv6_test_packet, port7_output_packets[0]),
      IsOkAndHolds(StrEq(
          GetParam().test_packet_vlan_id.has_value()
              ?
              R"(modified: headers[0].ethernet_header.ethernet_source: "00:01:02:03:04:05" -> "07:07:07:07:07:07"
modified: headers[2].ipv6_header.hop_limit: "0x03" -> "0x02"
)"
              :
              R"(modified: headers[0].ethernet_header.ethernet_source: "00:01:02:03:04:05" -> "07:07:07:07:07:07"
modified: headers[1].ipv6_header.hop_limit: "0x03" -> "0x02"
)")));

  // Check that output packets at port 5 are as expected.
  ASSERT_THAT(port5_output_packets, SizeIs(1));
  EXPECT_THAT(
      gutil::ProtoDiff(port7_output_packets[0], port5_output_packets[0]),
      IsOkAndHolds(StrEq(
          R"(modified: headers[0].ethernet_header.ethernet_source: "07:07:07:07:07:07" -> "05:05:05:05:05:05"
)")));
}

TEST_P(IpMulticastTest, AclIngressDropActionOverridesMulticastAction) {
  const sai::Instantiation kInstantiation = GetParam().instantiation;
  const pdpi::IrP4Info kIrP4Info = sai::GetIrP4Info(kInstantiation);
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  // Install multicast route.
  constexpr absl::string_view kVrf = "vrf";
  const netaddr::Ipv4Address kDstIpv4 = MulticastIpv4();
  const netaddr::Ipv6Address kDstIpv6 = MulticastIpv6();
  constexpr int kMulticastGroupId = 42;
  ASSERT_OK(sai::EntryBuilder()
                .AddVrfEntry(kVrf)
                .AddEntryAdmittingAllPacketsToL3()
                .AddEntrySettingVrfForAllPackets(kVrf)
                .AddMulticastRoute(kVrf, kDstIpv4, kMulticastGroupId)
                .AddMulticastRoute(kVrf, kDstIpv6, kMulticastGroupId)
                .AddMulticastGroupEntry(kMulticastGroupId,
                                        {sai::Replica{.egress_port = "\1"}})
                .AddMulticastRouterInterfaceEntry({
                    .multicast_replica_port = "\1",
                    .src_mac = netaddr::MacAddress(1, 2, 3, 4, 5, 6),
                })
                // Technically only needed when `GetParam().test_packet_vlan_id`
                // is set.
                .AddDisableVlanChecksEntry()
                .LogPdEntries()
                .InstallDedupedEntities(kIrP4Info, bmv2.P4RuntimeSession()));

  // Send test packets and expect output.
  constexpr int kArbitraryIngressPort1 = 24;
  constexpr int kArbitraryIngressPort2 = 42;
  ASSERT_OK_AND_ASSIGN(
      const packetlib::Packet ipv4_test_packet,
      GetIpv4TestPacket(kDstIpv4, GetParam().test_packet_vlan_id));
  ASSERT_OK_AND_ASSIGN(
      const packetlib::Packet ipv6_test_packet,
      GetIpv6TestPacket(kDstIpv6, GetParam().test_packet_vlan_id));
  EXPECT_THAT(bmv2.SendPacket(kArbitraryIngressPort1, ipv4_test_packet),
              IsOkAndHolds(Not(IsEmpty())));
  EXPECT_THAT(bmv2.SendPacket(kArbitraryIngressPort2, ipv6_test_packet),
              IsOkAndHolds(Not(IsEmpty())));

  // Install ACL, resend packets, and expect NO output.
  ASSERT_OK(sai::EntryBuilder()
                .AddIngressAclDroppingAllPackets()
                .LogPdEntries()
                .InstallDedupedEntities(kIrP4Info, bmv2.P4RuntimeSession()));
  EXPECT_THAT(bmv2.SendPacket(kArbitraryIngressPort1, ipv4_test_packet),
              IsOkAndHolds(IsEmpty()));
  EXPECT_THAT(bmv2.SendPacket(kArbitraryIngressPort2, ipv6_test_packet),
              IsOkAndHolds(IsEmpty()));
}

// We install two multicast routes:
// * An exact-match route in the IPMC table.
// * A default route that only applies if there was no IPMC table hit, in the
//   ingress ACL table.
//
// We then send two packets, one that should hit the IPMC table entry and one
// that should miss it, and verify that they hit the exact route and default
// route, respectively.
TEST_P(IpMulticastTest, IpmcTableHitQualifierWorks) {
  const sai::Instantiation kInstantiation = GetParam().instantiation;
  if (kInstantiation == sai::Instantiation::kTor ||
      kInstantiation == sai::Instantiation::kFabricBorderRouter) {
    GTEST_SKIP() << "not supported by " << absl::StrCat(kInstantiation);
  }
  const pdpi::IrP4Info kIrP4Info = sai::GetIrP4Info(kInstantiation);
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  static constexpr int kExactMatchMulticastGroupId = 1;
  static constexpr int kDefaultMulticastGroupId = 2;
  static constexpr netaddr::Ipv4Address kExactMatchIpv4Dst =
      netaddr::Ipv4Address(232, 1, 2, 3);
  static constexpr netaddr::Ipv4Address kDefaultMatchIpv4Dst =
      netaddr::Ipv4Address(10, 0, 0, 24);

  ASSERT_OK(
      sai::EntryBuilder()
          .AddVrfEntry("vrf")
          .AddEntrySettingVrfForAllPackets("vrf")
          .AddEntryAdmittingAllPacketsToL3()
          .AddMulticastRoute("vrf", kExactMatchIpv4Dst,
                             kExactMatchMulticastGroupId)
          .AddIngressAclEntryRedirectingToMulticastGroup(
              kDefaultMulticastGroupId,
              sai::MirrorAndRedirectMatchFields{
                  // This rule shall only apply if no multicast route was found.
                  .ipmc_table_hit = false,
              })
          .AddMulticastGroupEntry(kExactMatchMulticastGroupId,
                                  {
                                      sai::Replica{.egress_port = "\1"},
                                  })
          .AddMulticastGroupEntry(kDefaultMulticastGroupId,
                                  {
                                      sai::Replica{.egress_port = "\2"},
                                      sai::Replica{.egress_port = "\3"},
                                  })
          // Technically only needed when `GetParam().test_packet_vlan_id` is
          // set.
          .AddDisableVlanChecksEntry()
          .InstallDedupedEntities(kIrP4Info, bmv2.P4RuntimeSession(),
                                  /*allow_unsupported=*/true));

  ASSERT_OK_AND_ASSIGN(
      const packetlib::Packet kExactMatchInputPacket,
      GetIpv4TestPacket(kExactMatchIpv4Dst, GetParam().test_packet_vlan_id));
  ASSERT_OK_AND_ASSIGN(
      const packetlib::Packet kDefaultMatchInputPacket,
      GetIpv4TestPacket(kDefaultMatchIpv4Dst, GetParam().test_packet_vlan_id));
  ASSERT_THAT(bmv2.SendPacket(1, kExactMatchInputPacket),
              IsOkAndHolds(UnorderedElementsAre(Key(1))));
  ASSERT_THAT(bmv2.SendPacket(1, kDefaultMatchInputPacket),
              IsOkAndHolds(UnorderedElementsAre(Key(2), Key(3))));
}

std::vector<TestParams> GetAllTestInstances() {
  std::vector<TestParams> instances;
  for (sai::Instantiation instantiation : sai::AllSaiInstantiations()) {
    instances.push_back(TestParams{
        .instantiation = instantiation,
        .test_packet_vlan_id = std::nullopt,
    });
    instances.push_back(TestParams{
        .instantiation = instantiation,
        .test_packet_vlan_id = 1234,
    });
  }
  return instances;
}

INSTANTIATE_TEST_SUITE_P(IpMulticastTest, IpMulticastTest,
                         testing::ValuesIn(GetAllTestInstances()),
                         [&](const testing::TestParamInfo<TestParams>& info) {
                           return absl::StrFormat(
                               "%v_%s", info.param.instantiation,
                               info.param.test_packet_vlan_id.has_value()
                                   ? "with_vlan_header"
                                   : "");
                         });

}  // namespace
}  // namespace pins
