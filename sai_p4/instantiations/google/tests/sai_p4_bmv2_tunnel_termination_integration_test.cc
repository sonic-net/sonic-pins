// Tests that tunnel termination (in particular, `tunnel_termination.p4`)
// functions as intended on BMv2.

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

#include <ostream>
#include <string>
#include <utility>
#include <vector>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto.h"
#include "gutil/proto_matchers.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/netaddr/mac_address.h"
#include "p4_pdpi/p4_runtime_matchers.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/p4_runtime_session_extras.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_pdpi/packetlib/packetlib_matchers.h"
#include "platforms/networking/p4/p4_infra/bmv2/bmv2.h"
#include "sai_p4/fixed/ids.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "sai_p4/instantiations/google/test_tools/set_up_bmv2.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"
#include "tests/forwarding/packet_at_port.h"

namespace pins {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::orion::p4::test::Bmv2;

using ::packetlib::HasHeaderCase;
using ::pdpi::HasPacketIn;
using ::pdpi::ParsedPayloadIs;
using ::testing::ElementsAre;
using ::testing::IsEmpty;
using ::testing::StrEq;

constexpr netaddr::MacAddress kSrcMac = netaddr::MacAddress(0, 1, 2, 3, 4, 5);
constexpr netaddr::MacAddress kDstMac = netaddr::MacAddress(2, 3, 4, 5, 6, 7);
;

absl::StatusOr<packetlib::Packet> GetIpv4InIpv6Packet(
    const netaddr::MacAddress& src_mac, const netaddr::MacAddress& dst_mac) {
  ASSIGN_OR_RETURN(auto packet,
                   gutil::ParseTextProto<packetlib::Packet>(absl::Substitute(
                       R"pb(
                         headers {
                           ethernet_header {
                             ethernet_source: "$0"
                             ethernet_destination: "$1"
                             ethertype: "0x86dd"  # IPv6
                           }
                         }
                         headers {
                           ipv6_header {
                             version: "0x6"
                             dscp: "0x00"
                             ecn: "0x0"
                             flow_label: "0x12345"
                             next_header: "0x04"  # IPv4
                             hop_limit: "0x03"
                             ipv6_source: "2001::1"
                             ipv6_destination: "2001::2"
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
                         payload: "A beautiful IPv4-in-IPv6 test packet."
                       )pb",
                       src_mac.ToString(), dst_mac.ToString())));
  RETURN_IF_ERROR(packetlib::UpdateAllComputedFields(packet).status());
  return packet;
}

using TunnelTerminationTest = testing::TestWithParam<sai::Instantiation>;

// Checks that decapsulation and VRF assignment work as expected for forwarded
// packets.
TEST_P(TunnelTerminationTest, PacketGetsDecapsulatedAndForwarded) {
  const sai::Instantiation kInstantiation = GetParam();
  const pdpi::IrP4Info kIrP4Info = sai::GetIrP4Info(kInstantiation);
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  // Install table entries: decap & default route, so we can check that VRF
  // assignment works and observe the forwarded output packet.
  ASSERT_OK(sai::EntryBuilder()
                .AddEntrySettingVrfForAllPackets("vrf")
                .AddEntryDecappingAllIpInIpv6Packets()
                .AddDefaultRouteForwardingAllPacketsToGivenPort(
                    /*egress_port=*/"\001", sai::IpVersion::kIpv4, "vrf",
                    // Rewrites to the same src and dst mac as the input packet.
                    sai::NexthopRewriteOptions{.src_mac_rewrite = kSrcMac,
                                               .dst_mac_rewrite = kDstMac})
                .AddEntryAdmittingAllPacketsToL3()  // Needed for forwarding.
                .LogPdEntries()
                .InstallDedupedEntities(kIrP4Info, bmv2.P4RuntimeSession()));

  // Inject Ipv4-in-IPv6 test packet and expect one output packet.
  ASSERT_OK_AND_ASSIGN(packetlib::Packet input_packet,
                       GetIpv4InIpv6Packet(kSrcMac, kDstMac));
  ASSERT_OK_AND_ASSIGN(std::string raw_input_packet,
                       packetlib::SerializePacket(input_packet));
  ASSERT_OK_AND_ASSIGN(std::vector<pins::PacketAtPort> output_packets,
                       bmv2.SendPacket(pins::PacketAtPort{
                           .port = 42,
                           .data = raw_input_packet,
                       }));
  ASSERT_EQ(output_packets.size(), 1);
  packetlib::Packet output_packet =
      packetlib::ParsePacket(output_packets[0].data);
  EXPECT_THAT(output_packet.reasons_invalid(), IsEmpty());

  // The forwarded packet should be like the input packet but with the outer IP
  // header stripped, and some minor rewrites.
  ASSERT_THAT(input_packet.headers(),
              ElementsAre(HasHeaderCase(packetlib::Header::kEthernetHeader),
                          HasHeaderCase(packetlib::Header::kIpv6Header),
                          HasHeaderCase(packetlib::Header::kIpv4Header)));
  ASSERT_THAT(output_packet.headers(),
              ElementsAre(HasHeaderCase(packetlib::Header::kEthernetHeader),
                          HasHeaderCase(packetlib::Header::kIpv4Header)));
  auto decapped_packet = input_packet;
  decapped_packet.mutable_headers()->erase(
      decapped_packet.mutable_headers()->begin() + 1);
  EXPECT_THAT(
      gutil::ProtoDiff(decapped_packet, output_packet),
      IsOkAndHolds(StrEq(
          R"(modified: headers[0].ethernet_header.ethertype: "0x86dd" -> "0x0800"
modified: headers[1].ipv4_header.ttl: "0x20" -> "0x1f"
modified: headers[1].ipv4_header.checksum: "0x5003" -> "0x5103"
)")));
}

// Checks the interaction of pre ingress ACLs and tunnel termination:
// - Pre ingress ACLs see the original packet before decap.
TEST_P(TunnelTerminationTest,
       PreIngressAclMatchesOnUndecappedPacketAndOverridesDecapVrf) {
  const sai::Instantiation kInstantiation = GetParam();
  const pdpi::IrP4Info kIrP4Info = sai::GetIrP4Info(kInstantiation);
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  // Install table entries: decap & default routes, so we can check that VRF
  // assignment works as expected by observing the egress port of the forwarded
  // output packet.
  ASSERT_OK(
      sai::EntryBuilder()
          .AddEntryDecappingAllIpInIpv6Packets()
          .AddPreIngressAclEntryAssigningVrfForGivenIpType(
              "acl-ipv4-vrf", sai::IpVersion::kIpv4)
          .AddPreIngressAclEntryAssigningVrfForGivenIpType(
              "acl-ipv6-vrf", sai::IpVersion::kIpv6)
          // Route that will apply if the ACL entry matching the decapped packet
          // determines the VRF.
          .AddDefaultRouteForwardingAllPacketsToGivenPort(
              /*egress_port=*/"\002", sai::IpVersion::kIpv4And6, "acl-ipv4-vrf")
          // Route that will apply if the ACL entry matching the undecapped
          // packet determines the VRF.
          .AddDefaultRouteForwardingAllPacketsToGivenPort(
              /*egress_port=*/"\003", sai::IpVersion::kIpv4And6, "acl-ipv6-vrf")
          .AddEntryAdmittingAllPacketsToL3()  // Needed for forwarding.
          .LogPdEntries()
          .InstallDedupedEntities(kIrP4Info, bmv2.P4RuntimeSession()));

  // Inject Ipv4-in-IPv6 test packet and expect one output packet.
  ASSERT_OK_AND_ASSIGN(packetlib::Packet input_packet,
                       GetIpv4InIpv6Packet(kSrcMac, kDstMac));
  ASSERT_OK_AND_ASSIGN(std::string raw_input_packet,
                       packetlib::SerializePacket(input_packet));
  ASSERT_OK_AND_ASSIGN(std::vector<pins::PacketAtPort> output_packets,
                       bmv2.SendPacket(pins::PacketAtPort{
                           .port = 42,
                           .data = raw_input_packet,
                       }));
  ASSERT_EQ(output_packets.size(), 1);

  // We expect the packet to receive VRF "acl-ipv6-vrf", and thus to egress on
  // port 3.
  EXPECT_EQ(output_packets[0].port, 3);
}

// Checks that decapsulation does not affect punted packets. See b/286604845.
TEST_P(TunnelTerminationTest, PuntedPacketIsNotDecapsulated) {
  const sai::Instantiation kInstantiation = GetParam();
  const pdpi::IrP4Info kIrP4Info = sai::GetIrP4Info(kInstantiation);
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));

  // Install table entries: decap & punt to controller, so we can check that the
  // punted packet did not get decapped.
  ASSERT_OK(sai::EntryBuilder()
                .AddEntryDecappingAllIpInIpv6Packets()
                .AddEntryPuntingAllPackets(sai::PuntAction::kTrap)
                .LogPdEntries()
                .InstallDedupedEntities(kIrP4Info, bmv2.P4RuntimeSession()));

  // Inject Ipv4-in-IPv6 test packet and expect 0 forwarded packets and 1
  // punted packet.
  ASSERT_OK_AND_ASSIGN(packetlib::Packet input_packet,
                       GetIpv4InIpv6Packet(kSrcMac, kDstMac));
  ASSERT_OK_AND_ASSIGN(std::string raw_input_packet,
                       packetlib::SerializePacket(input_packet));
  ASSERT_THAT(bmv2.SendPacket(pins::PacketAtPort{
                  .port = 42,
                  .data = raw_input_packet,
              }),
              IsOkAndHolds(IsEmpty()));
  // The punted packet should be like the input packet.
  EXPECT_THAT(bmv2.P4RuntimeSession().ReadStreamChannelResponsesAndFinish(),
              IsOkAndHolds(ElementsAre(
                  HasPacketIn(ParsedPayloadIs(EqualsProto(input_packet))))));
}

INSTANTIATE_TEST_SUITE_P(
    TunnelTerminationTest, TunnelTerminationTest,

    testing::Values(sai::Instantiation::kMiddleblock,
                    sai::Instantiation::kFabricBorderRouter),
    [&](const testing::TestParamInfo<sai::Instantiation>& info) {
      return InstantiationToString(info.param);
    });

}  // namespace
}  // namespace pins
