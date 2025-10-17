// Copyright 2025 Google LLC
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

#include "tests/packet_capture/packet_capture_test.h"

#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/flags/declare.h"
#include "absl/status/statusor.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/optional.h"
#include "glog/logging.h"
#include "gutil/collections.h"
#include "gutil/status.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/gnmi/openconfig.pb.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/p4_runtime_session_extras.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_pdpi/string_encodings/hex_string.h"
#include "proto/gnmi/gnmi.pb.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"
#include "tests/forwarding/util.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "tests/packet_capture/packet_capture_test_util.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/proto/generic_testbed.pb.h"
#include "thinkit/switch.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"

ABSL_DECLARE_FLAG(std::optional<sai::Instantiation>, switch_instantiation);

namespace pins_test {
namespace {

using ::p4::config::v1::P4Info;
using pctutil::SutToControlLinks;

// Returns a set of table entries that will cause a switch to mirror all packets
// on an incoming port to a mirror-to-port using PSAMP encapsulation and
// adding a specified Vlan tag.
absl::StatusOr<std::vector<p4::v1::Entity>>
ConstructEntriesToMirrorTrafficWithVlanTag(
    const pdpi::IrP4Info &ir_p4info, const std::string &p4rt_src_port_id,
    const sai::MirrorSessionParams &mirror_session) {
  ASSIGN_OR_RETURN(
      std::vector<p4::v1::Entity> pi_entities,
      sai::EntryBuilder()
          .AddDisableVlanChecksEntry()
          .AddMirrorSessionTableEntry(mirror_session)
          .AddMarkToMirrorAclEntry(sai::MarkToMirrorParams{
              .ingress_port = p4rt_src_port_id,
              .mirror_session_id = mirror_session.mirror_session_id,
          })
          .GetDedupedPiEntities(ir_p4info));

  return pi_entities;
}

TEST_P(PacketCaptureTestWithoutIxia, PsampEncapsulatedMirroringTest) {
  LOG(INFO) << "-- START OF TEST ---------------------------------------------";
  Testbed().Environment().SetTestCaseID("TBD");

  // Setup: the testbed consists of a SUT connected to a control device
  // that allows us to send and receive packets to/from the SUT.
  thinkit::Switch &sut = Testbed().Sut();
  thinkit::Switch &control_device = Testbed().ControlSwitch();

  // Configure mirror testbed.
  std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt_session,
      control_p4rt_session;
  ASSERT_OK_AND_ASSIGN(sut_p4rt_session,
                       pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
                           sut, std::nullopt, std::nullopt));

  ASSERT_OK_AND_ASSIGN(control_p4rt_session,
                       pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
                           control_device, std::nullopt, std::nullopt));

  ASSERT_OK_AND_ASSIGN(const P4Info &p4info,
                       pdpi::GetP4Info(*sut_p4rt_session));
  ASSERT_OK_AND_ASSIGN(const P4Info &control_p4info,
                       pdpi::GetP4Info(*control_p4rt_session));
  ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(p4info));
  ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_control_p4info,
                       pdpi::CreateIrP4Info(control_p4info));
  // Store P4Info for debugging purposes.
  EXPECT_OK(
      Testbed().Environment().StoreTestArtifact("p4info.textproto", p4info));
  // Store gNMI config for debugging purposes.
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(std::string sut_gnmi_config,
                       pins_test::GetGnmiConfig(*sut_gnmi_stub));
  EXPECT_OK(Testbed().Environment().StoreTestArtifact("sut_gnmi_config.json",
                                                      sut_gnmi_config));

  ASSERT_OK_AND_ASSIGN(std::vector<p4::v1::Entity> pi_entities,
                       sai::EntryBuilder()
                           .AddEntryPuntingAllPackets(sai::PuntAction::kCopy)
                           .GetDedupedPiEntities(ir_control_p4info));

  ASSERT_OK(pdpi::InstallPiEntities(control_p4rt_session.get(),
                                    ir_control_p4info, pi_entities));

  // Pick links to be used for packet injection and mirroring.
  ASSERT_OK_AND_ASSIGN(
      SutToControlLinks link_used_for_test_packets,
      pctutil::PickSutToControlDeviceLinkThatsUp(sut_gnmi_stub.get()));
  LOG(INFO) << "Link used to inject test packets: "
            << link_used_for_test_packets;

  // Get P4RT IDs for SUT ports.
  absl::flat_hash_map<std::string, std::string> p4rt_id_by_interface;
  ASSERT_OK_AND_ASSIGN(p4rt_id_by_interface,
                       GetAllInterfaceNameToPortId(*sut_gnmi_stub));
  ASSERT_OK_AND_ASSIGN(
      const std::string kSutIngressPortP4rtId,
      gutil::FindOrStatus(
          p4rt_id_by_interface,
          link_used_for_test_packets.sut_ingress_port.gnmi_name));
  ASSERT_OK_AND_ASSIGN(
      const std::string kSutEgressPortP4rtId,
      gutil::FindOrStatus(p4rt_id_by_interface,
                          link_used_for_test_packets.sut_mtp_port.gnmi_name));
  // Get P4RT IDs for Control Switch ports.
  ASSERT_OK_AND_ASSIGN(auto control_gnmi_stub, control_device.CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(p4rt_id_by_interface,
                       GetAllInterfaceNameToPortId(*control_gnmi_stub));

  // Configure mirror session attributes.
  auto mirror_session_params = sai::MirrorSessionParams{
      .mirror_session_id = "psamp_mirror",
      .monitor_port = kSutEgressPortP4rtId,
      .mirror_encap_src_mac = "00:00:00:22:22:22",
      .mirror_encap_dst_mac = "00:00:00:44:44:44",
      .mirror_encap_vlan_id = "0x0fe",
      .mirror_encap_src_ip = "2222:2222:2222:2222:2222:2222:2222:2222",
      .mirror_encap_dst_ip = "4444:4444:4444:4444:4444:4444:4444:4444",
      .mirror_encap_udp_src_port = "0x08ae",
      .mirror_encap_udp_dst_port = "0x1283"};
  // Install ACL table entry to match on inject port on Control switch
  // and mirror-to-port on SUT.
  ASSERT_OK_AND_ASSIGN(auto entries, ConstructEntriesToMirrorTrafficWithVlanTag(
                                         ir_p4info, kSutIngressPortP4rtId,
                                         mirror_session_params));
  ASSERT_OK(
      pdpi::InstallPiEntities(sut_p4rt_session.get(), ir_p4info, entries));

  LOG(INFO) << "injecting test packet: "
            << GetParam().test_packet.DebugString();
  ASSERT_OK_AND_ASSIGN(std::string raw_packet,
                       packetlib::SerializePacket(GetParam().test_packet));

  // Read ingress and egress port stat counters before packet injection.
  ASSERT_OK_AND_ASSIGN(
      uint64_t out_packets_pre,
      pctutil::GetGnmiStat("out-unicast-pkts",
                           link_used_for_test_packets.sut_mtp_port.gnmi_name,
                           sut_gnmi_stub.get()));
  ASSERT_OK_AND_ASSIGN(
      uint64_t in_packets_pre,
      pctutil::GetGnmiStat(
          "in-unicast-pkts",
          link_used_for_test_packets.sut_ingress_port.gnmi_name,
          sut_gnmi_stub.get()));

  const int kPacketCount = 100;
  const int kPacketInjectDelayMs = 50;
  for (int i = 0; i < kPacketCount; ++i) {
    LOG(INFO) << "Injecting packet at time: " << absl::Now();
    ASSERT_OK(pins::InjectEgressPacket(
        /*port=*/link_used_for_test_packets.control_switch_inject_port.p4_id,
        /*packet=*/raw_packet,
        /*p4info=*/ir_p4info,
        /*p4rt=*/control_p4rt_session.get(),
        /*packet_delay=std::nullopt*/
        absl::Milliseconds(kPacketInjectDelayMs)));
  }
  // Read packets mirrored back to Control switch.
  std::vector<packetlib::Packet> received_packets;
  EXPECT_OK(control_p4rt_session->HandleNextNStreamMessages(
      [&](const p4::v1::StreamMessageResponse &message) {
        if (!message.has_packet())
          return false;
        packetlib::Packet received_packet =
            packetlib::ParsePacket(message.packet().payload());
        received_packets.push_back(received_packet);
        return true;
      },
      kPacketCount, absl::Minutes(2)));
  // Ensure the correct number of packets was received.
  ASSERT_EQ(received_packets.size(), kPacketCount);

  // Validate headers of each received packet.
  int mirrored_packets_received = 0;
  std::optional<uint64_t> prev_obs_time, curr_obs_time;
  std::optional<int> prev_sequence, curr_sequence;
  for (const packetlib::Packet &received_packet : received_packets) {
    // Header count sanity check.
    LOG(INFO) << absl::StrCat("Packet: ", received_packet.DebugString());
    if (received_packet.headers().size() != 6) {
      continue;
    }
    // Parse Ethernet header.
    ASSERT_EQ(received_packet.headers(0).has_ethernet_header(), true);
    const auto &eth_header = received_packet.headers(0).ethernet_header();
    EXPECT_EQ(eth_header.ethernet_source(),
              mirror_session_params.mirror_encap_src_mac);
    EXPECT_EQ(eth_header.ethernet_destination(),
              mirror_session_params.mirror_encap_dst_mac);
    // Parse VLAN header.
    ASSERT_EQ(received_packet.headers(1).has_vlan_header(), true);
    // Parse IPv6 header.
    ASSERT_EQ(received_packet.headers(2).has_ipv6_header(), true);
    const auto &ip_header = received_packet.headers(2).ipv6_header();
    EXPECT_EQ(ip_header.ipv6_source(),
              mirror_session_params.mirror_encap_src_ip);
    EXPECT_EQ(ip_header.ipv6_destination(),
              mirror_session_params.mirror_encap_dst_ip);
    // Parse UDP header.
    ASSERT_EQ(received_packet.headers(3).has_udp_header(), true);
    const auto &udp_header = received_packet.headers(3).udp_header();

    EXPECT_EQ(udp_header.source_port(),
              mirror_session_params.mirror_encap_udp_src_port);
    EXPECT_EQ(udp_header.destination_port(),
              mirror_session_params.mirror_encap_udp_dst_port);
    // Parse IPFIX header.
    ASSERT_EQ(received_packet.headers(4).has_ipfix_header(), true);
    // Validate sequence number incrementation.

    ASSERT_OK_AND_ASSIGN(
        curr_sequence,
        pdpi::HexStringToInt(
            received_packet.headers(4).ipfix_header().sequence_number()));
    if (prev_sequence.has_value()) {
      EXPECT_EQ(curr_sequence, prev_sequence.value() + 1);
    }
    prev_sequence = curr_sequence;
    // Parse PSAMP header.
    ASSERT_EQ(received_packet.headers(5).has_psamp_header(), true);
    const auto &psamp_header = received_packet.headers(5).psamp_header();
    // Validate observation times increment within expected range.
    ASSERT_OK_AND_ASSIGN(curr_obs_time, pdpi::HexStringToUint64(
                                            psamp_header.observation_time()));
    if (prev_obs_time.has_value()) {
      constexpr int kObsTimeGapThresholdNs = 2000000;
      EXPECT_LE(
          (pctutil::ParsePsampHeaderObservationTime(curr_obs_time.value()) -
           pctutil::ParsePsampHeaderObservationTime(prev_obs_time.value())),
          absl::Nanoseconds(
              /*Injection delay*/ (kPacketInjectDelayMs * 1000000) +
              /*2 msecs*/ kObsTimeGapThresholdNs));
    }
    prev_obs_time = curr_obs_time;
    // Verify ingress port in PSAMP header.
    ASSERT_OK_AND_ASSIGN(
        auto ingress_vendor_port_id,
        pctutil::GetVendorPortId(
            link_used_for_test_packets.sut_ingress_port.gnmi_name,
            sut_gnmi_stub.get()));
    int gnmi_vendor_port_id = -1;
    ASSERT_TRUE(absl::SimpleAtoi(ingress_vendor_port_id, &gnmi_vendor_port_id));
    ASSERT_OK_AND_ASSIGN(auto psamp_ingress_port_id,
                         pdpi::HexStringToInt(psamp_header.ingress_port()));
    EXPECT_EQ(psamp_ingress_port_id, gnmi_vendor_port_id);

    LOG(INFO) << absl::StrCat(
        "Ingress port: ", psamp_header.ingress_port(),
        ", Egress port: ", psamp_header.egress_port(),
        ", Observation time: ", psamp_header.observation_time());
    mirrored_packets_received++;
  }

  // Ensure at least 90% of packets was received after being mirrored.
  // Some  packets in the 100 packets received could have been spurious.
  ASSERT_GE(mirrored_packets_received, kPacketCount * 0.9);
  // Check ingress and egress port counters increase as expected. That is,
  // within 100-110% of number of packets.
  ASSERT_OK_AND_ASSIGN(
      uint64_t in_packets_post,
      pctutil::GetGnmiStat(
          "in-unicast-pkts",
          link_used_for_test_packets.sut_ingress_port.gnmi_name,
          sut_gnmi_stub.get()));
  // Counter should increment by at least as many packets as were sent.
  EXPECT_GE(in_packets_post, in_packets_pre + kPacketCount);
  // Counter should increment by no more than 110% of packets than were sent.
  // This allows for tolerance of non-test packets such as router solicitation
  // packets and others.
  EXPECT_LE(in_packets_post, in_packets_pre + (kPacketCount * 1.1));
  LOG(INFO) << absl::StrCat("in_packets_post: ", in_packets_post,
                            ", in_packets_pre: ", in_packets_pre);

  // SUT egress port gnmi name is hard coded for now, based on the egress port
  // oid that's chosen by the manual component test to set up the mirror
  // session on the SUT. This will be replaced by the egress port that is
  // used when creating that mirror session via P4RT.
  ASSERT_OK_AND_ASSIGN(
      uint64_t out_packets_post,
      pctutil::GetGnmiStat("out-unicast-pkts",
                           link_used_for_test_packets.sut_mtp_port.gnmi_name,
                           sut_gnmi_stub.get()));
  EXPECT_GE(out_packets_post, out_packets_pre + kPacketCount);
  EXPECT_LE(out_packets_post, out_packets_pre + (kPacketCount * 1.1));
  LOG(INFO) << absl::StrCat("out_packets_post: ", out_packets_post,
                            ", out_packets_pre: ", out_packets_pre);
}

} // anonymous namespace
} // namespace pins_test
