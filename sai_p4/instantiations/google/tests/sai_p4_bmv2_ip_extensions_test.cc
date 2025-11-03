#include <bitset>
#include <optional>
#include <string>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/log/check.h"
#include "absl/log/log.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/testing.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/packetlib/bit_widths.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_pdpi/ternary.h"
#include "platforms/networking/p4/p4_infra/bmv2/bmv2.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "sai_p4/instantiations/google/test_tools/set_up_bmv2.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"

namespace pins {
namespace {

using ::orion::p4::test::Bmv2;
using ::testing::Eq;
using ::testing::IsEmpty;
using ::testing::SizeIs;

using PacketsByPort = absl::flat_hash_map<int, packetlib::Packets>;

absl::StatusOr<packetlib::Packet> GetMldPacket() {
  auto mld_packet = gutil::ParseProtoOrDie<packetlib::Packet>(R"pb(
    headers {
      ethernet_header {
        ethernet_destination: "33:33:ff:02:00:02"
        ethernet_source: "5e:33:7b:02:00:02"
        ethertype: "0x8100"
      }
    }
    headers {
      vlan_header {
        priority_code_point: "0x0"
        drop_eligible_indicator: "0x0"
        vlan_identifier: "0x0ff"
        ethertype: "0x86dd"
      }
    }
    headers {
      ipv6_header {
        version: "0x6"
        dscp: "0x00"
        ecn: "0x0"
        flow_label: "0x00000"
        payload_length: "0x0020"
        next_header: "0x00"
        hop_limit: "0x01"
        ipv6_source: "fe80::5c33:7bff:fe02:2"
        ipv6_destination: "ff02::1:ff02:2"
      }
    }
    headers {
      hop_by_hop_options_header {
        next_header: "0x3a"
        header_extension_length: "0x00"
        options_and_padding: "0x050200000100"
      }
    }
    headers {
      icmp_header {
        type: "0x83"
        code: "0x00"
        checksum: "0xabe2"
        rest_of_header: "0x00000000"
      }
    }
  )pb");
  RETURN_IF_ERROR(packetlib::PadPacketToMinimumSize(mld_packet).status());
  RETURN_IF_ERROR(packetlib::UpdateMissingComputedFields(mld_packet).status());
  return mld_packet;
}

TEST(SaiP4Bmv2IpExtensions, MldPacketGetsPunted) {
  constexpr int kIngressPort = 4;
  const sai::Instantiation kInstantiation = sai::Instantiation::kTor;
  const pdpi::IrP4Info kIrP4Info = sai::GetIrP4Info(kInstantiation);
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));
  ASSERT_OK_AND_ASSIGN(packetlib::Packet mld_packet, GetMldPacket());

  ASSERT_OK(sai::EntryBuilder()
                .AddIngressAclEntry({
                    .is_ip = true,
                    // Multicast Listener Discovery (MLD): IP protocol 58
                    .ip_protocol = pdpi::Ternary(
                        std::bitset<packetlib::kIpProtocolBitwidth>(58)),
                    .punt_action = sai::CopyAction{.cpu_queue = "some_queue"},
                    .priority = 1,
                })
                .InstallDedupedEntities(kIrP4Info, bmv2.P4RuntimeSession()));

  // Inject a test packet to kIngressPort. Note that this port value is
  // arbitrary.
  ASSERT_OK_AND_ASSIGN(auto outputs, bmv2.SendPacket(kIngressPort, mld_packet));
  // The packet must be dropped.
  ASSERT_THAT(outputs, IsEmpty());

  // The punted copy of the injected packet is the same as the MLD packet.
  ASSERT_OK_AND_ASSIGN(
      std::vector<p4::v1::StreamMessageResponse> responses,
      bmv2.P4RuntimeSession().GetAllStreamMessagesFor(absl::Seconds(1)));
  ASSERT_OK_AND_ASSIGN(std::string raw_mld_packet,
                       packetlib::RawSerializePacket(mld_packet));
  EXPECT_THAT(responses, SizeIs(1));
  for (const auto& response : responses) {
    EXPECT_THAT(response.packet().payload(), Eq(raw_mld_packet));
  }
}

TEST(SaiP4Bmv2IpExtensions, MldPacketGetsDropped) {
  constexpr int kIngressPort = 4;
  const sai::Instantiation kInstantiation = sai::Instantiation::kTor;
  const pdpi::IrP4Info kIrP4Info = sai::GetIrP4Info(kInstantiation);
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));
  ASSERT_OK_AND_ASSIGN(packetlib::Packet mld_packet, GetMldPacket());

  ASSERT_OK(sai::EntryBuilder()
                .AddIngressAclEntry({
                    .is_ip = true,
                    .ip_protocol = pdpi::Ternary(
                        std::bitset<packetlib::kIpProtocolBitwidth>(0)),
                    .punt_action = sai::CopyAction{.cpu_queue = "some_queue"},
                    .priority = 1,
                })
                .InstallDedupedEntities(kIrP4Info, bmv2.P4RuntimeSession()));

  // Inject a test packet to kIngressPort. Note that this port value is
  // arbitrary.
  ASSERT_OK_AND_ASSIGN(auto outputs, bmv2.SendPacket(kIngressPort, mld_packet));
  // The packet must be dropped.
  ASSERT_THAT(outputs, IsEmpty());

  // The punted copy of the injected packet is dropped.
  ASSERT_OK_AND_ASSIGN(
      std::vector<p4::v1::StreamMessageResponse> responses,
      bmv2.P4RuntimeSession().GetAllStreamMessagesFor(absl::Seconds(1)));
  EXPECT_THAT(responses, IsEmpty());
}

// This test models our current modeling choice of choosing to drop any packet
// with a HopByHopOptions header. GPINs switches drop packets with hop-by-hop
// options by choice, not by necessity. All expected packets should be punted,
// so we mark them all to drop by choice to get some deterministic behavior.
TEST(SaiP4Bmv2IpExtensions,
     MldPacketGetDroppedWhenForwardedWithNoAclIngressEntry) {
  constexpr int kIngressPort = 4;
  const sai::Instantiation kInstantiation = sai::Instantiation::kTor;
  const pdpi::IrP4Info kIrP4Info = sai::GetIrP4Info(kInstantiation);
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, sai::SetUpBmv2ForSaiP4(kInstantiation));
  ASSERT_OK_AND_ASSIGN(packetlib::Packet mld_packet, GetMldPacket());

  // Install entries to forward all IP packets without rewrites and no ACL
  // ingress entry.
  constexpr absl::string_view kEgressPortProto = "\001";
  sai::EntryBuilder entry_builder;
  ASSERT_OK(entry_builder
                .AddEntriesForwardingIpPacketsToGivenPort(
                    kEgressPortProto, sai::IpVersion::kIpv4And6,
                    sai::NexthopRewriteOptions{
                        .disable_decrement_ttl = true,
                        .src_mac_rewrite = std::nullopt,
                        .dst_mac_rewrite = std::nullopt,
                        .disable_vlan_rewrite = true,
                    })
                .InstallDedupedEntities(kIrP4Info, bmv2.P4RuntimeSession()));

  // Inject a test packet to kIngressPort. Note that this port value is
  // arbitrary.
  ASSERT_OK_AND_ASSIGN(auto outputs, bmv2.SendPacket(kIngressPort, mld_packet));
  // The packet must be dropped.
  ASSERT_THAT(outputs, IsEmpty());

  // The punted copy of the injected packet is dropped.
  ASSERT_OK_AND_ASSIGN(
      std::vector<p4::v1::StreamMessageResponse> responses,
      bmv2.P4RuntimeSession().GetAllStreamMessagesFor(absl::Seconds(1)));
  EXPECT_THAT(responses, IsEmpty());
}

}  // namespace
}  // namespace pins

