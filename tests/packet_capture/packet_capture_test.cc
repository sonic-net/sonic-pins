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

#include <bitset>
#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/flags/declare.h"
#include "absl/log/check.h"
#include "absl/log/log.h"
#include "absl/status/statusor.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/optional.h"
#include "dvaas/dataplane_validation.h"
#include "dvaas/test_vector.h"
#include "dvaas/test_vector.pb.h"
#include "dvaas/validation_result.h"
#include "gmock/gmock.h"
#include "google/protobuf/descriptor.h"
#include "gtest/gtest.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/status.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/gnmi/openconfig.pb.h"
#include "net/google::protobuf/contrib/fixtures/proto-fixture-repository.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4_infra/p4_pdpi/p4_runtime_session_extras.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_infra/p4_pdpi/ternary.h"
#include "p4_infra/string_encodings/decimal_string.h"
#include "p4_infra/string_encodings/hex_string.h"
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

ABSL_DECLARE_FLAG(std::optional<sai::Instantiation>, switch_instantiation);

namespace pins_test {
namespace {

using ::p4::config::v1::P4Info;
using pctutil::SutToControlLinks;

// Returns a set of table entries that will cause a switch to mirror all packets
// on an incoming port to a mirror-to-port using PSAMP encapsulation and
// adding a specified Vlan tag.
absl::StatusOr<std::vector<p4::v1::Entity>>
CreateEntriesToMirrorTrafficWithVlanTag(
    const pdpi::IrP4Info& ir_p4info, const std::string& p4rt_src_port_id,
    const sai::MirrorSessionParams& mirror_session) {
  ASSIGN_OR_RETURN(
      std::vector<p4::v1::Entity> pi_entities,
      sai::EntryBuilder()
          .AddDisableIngressVlanChecksEntry()
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
  thinkit::Switch& sut = Testbed().Sut();
  thinkit::Switch& control_device = Testbed().ControlSwitch();

  // Configure mirror testbed.
  std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt_session,
      control_p4rt_session;
  ASSERT_OK_AND_ASSIGN(sut_p4rt_session,
                       pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
                           sut, std::nullopt, std::nullopt));

  ASSERT_OK_AND_ASSIGN(control_p4rt_session,
                       pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
                           control_device, std::nullopt, std::nullopt));

  ASSERT_OK_AND_ASSIGN(const P4Info& p4info,
                       pdpi::GetP4Info(*sut_p4rt_session));
  ASSERT_OK_AND_ASSIGN(const P4Info& control_p4info,
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
      .monitor_backup_port = kSutEgressPortP4rtId,
      .mirror_encap_src_mac = "00:00:00:22:22:22",
      .mirror_encap_dst_mac = "00:00:00:44:44:44",
      .mirror_encap_vlan_id = "0x0fe",
      .mirror_encap_src_ip = "2222:2222:2222:2222:2222:2222:2222:2222",
      .mirror_encap_dst_ip = "4444:4444:4444:4444:4444:4444:4444:4444",
      .mirror_encap_udp_src_port = "0x08ae",
      .mirror_encap_udp_dst_port = "0x1283"};
  // Install ACL table entry to match on inject port on Control switch
  // and mirror-to-port on SUT.
  ASSERT_OK_AND_ASSIGN(auto entries, CreateEntriesToMirrorTrafficWithVlanTag(
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
      [&](const p4::v1::StreamMessageResponse& message) {
        if (!message.has_packet()) return false;
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
  for (const packetlib::Packet& received_packet : received_packets) {
    // Header count sanity check.
    LOG(INFO) << absl::StrCat("Packet: ", received_packet.DebugString());
    if (received_packet.headers().size() != 6) {
      continue;
    }
    // Parse Ethernet header.
    ASSERT_EQ(received_packet.headers(0).has_ethernet_header(), true);
    const auto& eth_header = received_packet.headers(0).ethernet_header();
    EXPECT_EQ(eth_header.ethernet_source(),
              mirror_session_params.mirror_encap_src_mac);
    EXPECT_EQ(eth_header.ethernet_destination(),
              mirror_session_params.mirror_encap_dst_mac);
    // Parse VLAN header.
    ASSERT_EQ(received_packet.headers(1).has_vlan_header(), true);
    ASSERT_EQ(received_packet.headers(1).vlan_header().vlan_identifier(),
              mirror_session_params.mirror_encap_vlan_id);
    // Parse IPv6 header.
    ASSERT_EQ(received_packet.headers(2).has_ipv6_header(), true);
    const auto& ip_header = received_packet.headers(2).ipv6_header();
    EXPECT_EQ(ip_header.ipv6_source(),
              mirror_session_params.mirror_encap_src_ip);
    EXPECT_EQ(ip_header.ipv6_destination(),
              mirror_session_params.mirror_encap_dst_ip);
    // Parse UDP header.
    ASSERT_EQ(received_packet.headers(3).has_udp_header(), true);
    const auto& udp_header = received_packet.headers(3).udp_header();

    EXPECT_EQ(udp_header.source_port(),
              mirror_session_params.mirror_encap_udp_src_port);
    EXPECT_EQ(udp_header.destination_port(),
              mirror_session_params.mirror_encap_udp_dst_port);
    // Parse IPFIX header.
    ASSERT_EQ(received_packet.headers(4).has_ipfix_header(), true);
    // Validate sequence number incrementation.

    ASSERT_OK_AND_ASSIGN(
        curr_sequence,
        string_encodings::HexStringToInt(
            received_packet.headers(4).ipfix_header().sequence_number()));
    if (prev_sequence.has_value()) {
      EXPECT_EQ(curr_sequence, prev_sequence.value() + 1);
    }
    prev_sequence = curr_sequence;
    // Parse PSAMP header.
    ASSERT_EQ(received_packet.headers(5).has_psamp_header(), true);
    const auto& psamp_header = received_packet.headers(5).psamp_header();
    // Validate observation times increment within expected range.
    ASSERT_OK_AND_ASSIGN(curr_obs_time, string_encodings::HexStringToUint64(
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
    ASSERT_OK_AND_ASSIGN(
        auto psamp_ingress_port_id,
        string_encodings::HexStringToInt(psamp_header.ingress_port()));
    EXPECT_EQ(psamp_ingress_port_id, gnmi_vendor_port_id);

    LOG(INFO) << absl::StrCat(
        "Ingress port: ", psamp_header.ingress_port(),
        ", Egress port: ", psamp_header.egress_port(),
        ", Observation time: ", psamp_header.observation_time());
    mirrored_packets_received++;
  }

  // Ensure at least 85% of packets was received after being mirrored.
  // Some  packets in the 100 packets received could have been spurious.
  ASSERT_GE(mirrored_packets_received, kPacketCount * 0.85);
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

using ::google::protobuf::contrib::fixtures::ProtoFixtureRepository;

struct ControllerPacketCaptureParams {
  std::string ingress_port;
  std::string egress_port;
  // Ingress VLAN IDs to match on.
  std::vector<int> ingress_vlan_ids;
  // Egress VLAN ID to be set on packets.
  int forwarded_packet_vlan_id;
  std::string mirror_session_id;
  PacketCaptureTestPacketType packet_type;
};

std::string GetVlanIdHexStr(int val) {
  return absl::StrCat("0x", absl::Hex(val, absl::kZeroPad3));
}

std::string GetAclMetadataHexStr(int val) {
  return absl::StrCat("0x", absl::Hex(val, absl::kZeroPad2));
}

// Returns a set of table entries that will cause a switch to match on Ingress
// VLAN ID and Ingress Port and set ACL Metadata and Egress VLAN ID.
absl::StatusOr<std::vector<p4::v1::Entity>> CreatePreIngressAclEntries(
    const pdpi::IrP4Info& ir_p4info, const std::string& ingress_port,
    const std::vector<int>& ingress_vlan_ids,
    const int forwarded_packet_vlan_id) {
  std::vector<p4::v1::Entity> entities;
  sai::EntryBuilder entry_builder;
  for (const int ingress_vlan_id : ingress_vlan_ids) {
    ASSIGN_OR_RETURN(std::bitset<sai::kVlanIdBitwidth> ingress_vlan_id_bitset,
                     string_encodings::HexStringToBitset<sai::kVlanIdBitwidth>(
                         GetVlanIdHexStr(ingress_vlan_id)));
    entry_builder.AddPreIngressAclEntrySettingVlanAndAclMetadata(
        GetVlanIdHexStr(forwarded_packet_vlan_id),
        /*set ingress vlan id as acl metadata*/
        GetAclMetadataHexStr(ingress_vlan_id),
        sai::AclPreIngressVlanTableMatchFields{
            .vlan_id = pdpi::Ternary<std::bitset<sai::kVlanIdBitwidth>>(
                ingress_vlan_id_bitset),
            .in_port = ingress_port,
        },
        /*priority=*/1);
  }
  ASSIGN_OR_RETURN(
      std::vector<p4::v1::Entity> builder_entities,
      entry_builder.LogPdEntries().GetDedupedPiEntities(ir_p4info));
  entities.insert(entities.end(), builder_entities.begin(),
                  builder_entities.end());
  return entities;
}

// Returns a set of table entries that will cause a switch to match on ACL
// metadata and mirror all packets on an incoming port to a mirror-to-port
// using PSAMP encapsulation and adding a specified Vlan tag.
absl::StatusOr<std::vector<p4::v1::Entity>>
CreateEntriesToMatchOnAclMetadataAndMirrorTrafficAndRedirectToPort(
    const pdpi::IrP4Info& ir_p4info,
    const sai::MirrorSessionParams& mirror_session_params,
    const std::vector<int>& ingress_vlan_ids, const std::string& egress_port,
    const std::string& mirror_session_id) {
  std::vector<p4::v1::Entity> pi_entities;
  ASSIGN_OR_RETURN(std::vector<p4::v1::Entity> builder_entities,
                   sai::EntryBuilder()
                       .AddDisableIngressVlanChecksEntry()
                       .AddMirrorSessionTableEntry(mirror_session_params)
                       .LogPdEntries()
                       .GetDedupedPiEntities(ir_p4info));
  pi_entities.insert(pi_entities.end(), builder_entities.begin(),
                     builder_entities.end());
  for (const int ingress_vlan_id : ingress_vlan_ids) {
    /* Set ACL metadata to be the ingress VLAN ID. */
    ASSIGN_OR_RETURN(
        std::bitset<sai::kAclMetadataBitwidth> acl_metadata,
        string_encodings::HexStringToBitset<sai::kAclMetadataBitwidth>(
            GetAclMetadataHexStr(ingress_vlan_id)));
    ASSIGN_OR_RETURN(
        std::vector<p4::v1::Entity> pre_ingress_acl_entries,
        sai::EntryBuilder()
            .AddIngressAclEntryMirroringAndRedirectingToPort(
                egress_port, mirror_session_id,
                sai::MirrorAndRedirectMatchFields{
                    .acl_metadata =
                        pdpi::Ternary<std::bitset<sai::kAclMetadataBitwidth>>(
                            acl_metadata),
                },
                /*priority=*/1)
            .LogPdEntries()
            .GetDedupedPiEntities(ir_p4info));
    pi_entities.insert(pi_entities.end(), pre_ingress_acl_entries.begin(),
                       pre_ingress_acl_entries.end());
  }

  return pi_entities;
}

packetlib::Packet ParsePacketAndPadToMinimumSize(
    const ProtoFixtureRepository& repo, absl::string_view packet_pb) {
  packetlib::Packet packet = repo.ParseTextOrDie<packetlib::Packet>(packet_pb);
  CHECK_OK(packetlib::PadPacketToMinimumSize(packet));
  return packet;
}

absl::StatusOr<std::vector<dvaas::PacketTestVector>>
CreateControllerPacketCaptureTestVectors(
    const ControllerPacketCaptureParams& params,
    const sai::MirrorSessionParams& mirror_session_params) {
  // Test packets injected and expected results.
  std::vector<dvaas::PacketTestVector> test_vectors;

  for (int i = 0; i < params.ingress_vlan_ids.size(); ++i) {
    dvaas::PacketTestVector test_vector;
    ProtoFixtureRepository repo;

    ASSIGN_OR_RETURN(int mirror_port, string_encodings::DecimalStringToInt(
                                          mirror_session_params.monitor_port));

    std::string mirror_port_hex =
        absl::StrCat("0x", absl::Hex(mirror_port, absl::kZeroPad4));
    repo.RegisterValue("@ingress_port", "");

    repo.RegisterValue("@egress_port", params.egress_port);
    repo.RegisterValue("@mirror_port_hex", mirror_port_hex);
    repo.RegisterValue("@mirror_port", mirror_session_params.monitor_port);
    repo.RegisterValue("@ingress_vlan_id",
                       GetVlanIdHexStr(params.ingress_vlan_ids[i]));
    repo.RegisterValue("@mirror_ethernet_source",
                       mirror_session_params.mirror_encap_src_mac);
    repo.RegisterValue("@mirror_ethernet_destination",
                       mirror_session_params.mirror_encap_dst_mac);
    repo.RegisterValue("@mirror_vlan_id",
                       mirror_session_params.mirror_encap_vlan_id);
    repo.RegisterValue("@mirror_encap_udp_src_port",
                       mirror_session_params.mirror_encap_udp_src_port);
    repo.RegisterValue("@mirror_encap_udp_dst_port",
                       mirror_session_params.mirror_encap_udp_dst_port);
    repo.RegisterValue("@mirror_encap_ip_src",
                       mirror_session_params.mirror_encap_src_ip);
    repo.RegisterValue("@mirror_encap_ip_dst",
                       mirror_session_params.mirror_encap_dst_ip);
    repo.RegisterValue("@ttl", "0x10");
    repo.RegisterValue("@payload",
                       dvaas::MakeTestPacketTagFromUniqueId(
                           i,
                           "SwitchCapturesControlPacketsWithVlanTagAn"
                           "dRedirectsToPortAndMirrorsPackets"));
    // Build headers.
    repo.RegisterSnippetOrDie<packetlib::Header>("@ethernet", R"pb(
          ethernet_header {
            ethernet_destination: "aa:bb:cc:dd:ee:ff"
            ethernet_source: "02:1a:c0:a8:02:04"
            ethertype: "0x8100"
          }
        )pb")
        .RegisterSnippetOrDie<packetlib::Header>("@vlan", R"pb(
          vlan_header {
            priority_code_point: "0x0",
            drop_eligible_indicator: "0x0",
            vlan_identifier: @ingress_vlan_id,
            ethertype: "0x0800"
          }
        )pb")
        .RegisterSnippetOrDie<packetlib::Header>("@ipv4", R"pb(
          ipv4_header {
            version: "0x4"
            dscp: "0x00"
            ecn: "0x0"
            # total_length: filled in automatically.
            identification: "0xaafb"
            flags: "0x2"
            fragment_offset: "0x0000"
            ttl: @ttl
            protocol: "0x01"
            # checksum: filled in automatically
            ipv4_source: "10.0.0.1"
            ipv4_destination: "10.0.0.2"
          }
        )pb")
        .RegisterSnippetOrDie<packetlib::Header>("@ipv6", R"pb(
          ipv6_header {
            version: "0x6"
            dscp: "0x00"
            ecn: "0x0"
            flow_label: "0x00000"
            # payload_length: filled in automatically.
            next_header: "0x11"
            hop_limit: "0x00"
            ipv6_source: @mirror_encap_ip_src
            ipv6_destination: @mirror_encap_ip_dst
          }
        )pb")
        .RegisterSnippetOrDie<packetlib::Header>("@icmp", R"pb(
          icmp_header { type: "0x00" code: "0x00" rest_of_header: "0x1e600000" }
        )pb")
        .RegisterSnippetOrDie<packetlib::Header>("@udp", R"pb(
          udp_header {
            source_port: @mirror_encap_udp_src_port
            destination_port: @mirror_encap_udp_dst_port
            # length: filled in automatically
            # checksum: filled in automatically
          }
        )pb")
        .RegisterSnippetOrDie<packetlib::Header>("@arp_request", R"pb(
          arp_header {
            hardware_type: "0x0001"
            protocol_type: "0x0800"
            hardware_length: "0x06"
            protocol_length: "0x04"
            operation: "0x0001"
            sender_hardware_address: "02:1a:c0:a8:02:04"
            sender_protocol_address: "192.168.2.4"
            target_hardware_address: "00:00:00:00:00:00"
            target_protocol_address: "192.168.2.5"
          }
        )pb")
        .RegisterSnippetOrDie<packetlib::Header>("@arp_response", R"pb(
          arp_header {
            hardware_type: "0x0001"
            protocol_type: "0x0800"
            hardware_length: "0x06"
            protocol_length: "0x04"
            operation: "0x0002"
            sender_hardware_address: "aa:bb:cc:dd:ee:ff"
            sender_protocol_address: "192.168.2.5"
            target_hardware_address: "02:1a:c0:a8:02:04"
            target_protocol_address: "192.168.2.4"
          }
        )pb")
        .RegisterSnippetOrDie<packetlib::Header>("@ipfix", R"pb(
          ipfix_header {
            version: "0x000a"
            # length: filled in automatically
            export_time: "0x00002edf"
            sequence_number: "0x00000000"
            observation_domain_id: "0x00000000"
          }
        )pb")
        .RegisterSnippetOrDie<packetlib::Header>("@psamp_header", R"pb(
          psamp_header {
            template_id: "0x0000"
            # length: filled in automatically
            observation_time: "0x00002edf27a5cb40"
            flowset: "0xe72d"
            next_hop_index: "0x0000"
            epoch: "0x0000"
            ingress_port: "0x0000"
            egress_port: @mirror_port_hex
            user_meta_field: "0x0000"
            dlb_id: "0x00"
          }
        )pb")
        .RegisterSnippetOrDie<packetlib::Header>("@tcp_bgp", R"pb(
          tcp_header {
            source_port: "0x80df"
            destination_port: "0x00b3"
            sequence_number: "0xbdae7573"
            acknowledgement_number: "0x00000000"
            data_offset: "0xa"
            rest_of_header: "0x002ffff9be80000"
            uninterpreted_options: "0x020405b40402080ad96c989b0000000001030308"
          }
        )pb");

    switch (params.packet_type) {
      case PacketCaptureTestPacketType::kIcmpv4:
        repo.RegisterMessage("@input_packet",
                             ParsePacketAndPadToMinimumSize(repo,
                                                            R"pb(
                                                              headers: @ethernet
                                                              headers: @vlan
                                                              headers: @ipv4
                                                              headers: @icmp
                                                              payload: @payload
                                                            )pb"));
        break;
      case PacketCaptureTestPacketType::kIcmpv6:
        repo.RegisterMessage(
            "@input_packet",
            ParsePacketAndPadToMinimumSize(
                repo,
                R"pb(
                  headers: @ethernet
                  headers: @vlan { vlan_header { ethertype: "0x86dd" } }
                  headers: @ipv6 { ipv6_header { next_header: "0x3a" } }
                  headers: @icmp
                  payload: @payload
                )pb"));
        break;
      case PacketCaptureTestPacketType::kArpRequest:
        repo.RegisterMessage(
            "@input_packet",
            ParsePacketAndPadToMinimumSize(
                repo,
                R"pb(
                  headers: @ethernet {
                    ethernet_header {
                      ethernet_destination: "ff:ff:ff:ff:ff:ff"
                    }
                  }
                  headers: @vlan { vlan_header { ethertype: "0x0806" } }
                  headers: @arp_request
                  payload: @payload
                )pb"));
        break;
      case PacketCaptureTestPacketType::kArpResponse:
        repo.RegisterMessage(
            "@input_packet",
            ParsePacketAndPadToMinimumSize(
                repo,
                R"pb(
                  headers: @ethernet {
                    ethernet_header {
                      ethernet_destination: "ff:ff:ff:ff:ff:ff"
                    }
                  }
                  headers: @vlan { vlan_header { ethertype: "0x0806" } }
                  headers: @arp_response
                  payload: @payload
                )pb"));
        break;
      case PacketCaptureTestPacketType::kBgp:
        repo.RegisterMessage(
            "@input_packet",
            ParsePacketAndPadToMinimumSize(
                repo,
                R"pb(
                  headers: @ethernet
                  headers: @vlan
                  headers: @ipv4 { ipv4_header { protocol: "0x06" } }
                  headers: @tcp_bgp
                  payload: @payload
                )pb"));
        break;
    }

    // Build up acceptable_outputs string, to account for each replica.
    dvaas::SwitchOutput expected_output;
    switch (params.packet_type) {
      case PacketCaptureTestPacketType::kIcmpv4:
        *expected_output.add_packets() =
            repo.RegisterValue("@egress_port", params.egress_port)
                .RegisterMessage(
                    "@output_packet", ParsePacketAndPadToMinimumSize(repo, R"pb(
                      headers:
                          @ethernet { ethernet_header { ethertype: "0x0800" } }
                      headers: @ipv4
                      headers: @icmp
                      payload: @payload
                    )pb"))
                .ParseTextOrDie<dvaas::Packet>(R"pb(
                  port: @egress_port
                  parsed: @output_packet
                )pb");
        *expected_output.add_packets() =
            repo.RegisterValue("@egress_port",
                               mirror_session_params.monitor_port)
                .RegisterMessage(
                    "@output_packet", ParsePacketAndPadToMinimumSize(repo, R"pb(
                      headers: @ethernet {
                        ethernet_header {
                          ethernet_destination: @mirror_ethernet_destination
                          ethernet_source: @mirror_ethernet_source
                          ethertype: "0x8100"
                        }
                      }
                      headers: @vlan {
                        vlan_header {
                          vlan_identifier: @mirror_vlan_id
                          ethertype: "0x86dd"
                        }
                      }
                      headers: @ipv6
                      headers: @udp
                      headers: @ipfix
                      headers: @psamp_header
                      payload: @payload
                    )pb"))
                .ParseTextOrDie<dvaas::Packet>(R"pb(
                  port: @egress_port
                  parsed: @output_packet
                )pb");
        break;
      case PacketCaptureTestPacketType::kIcmpv6:
        *expected_output.add_packets() =
            repo.RegisterValue("@egress_port", params.egress_port)
                .RegisterMessage(
                    "@output_packet", ParsePacketAndPadToMinimumSize(repo, R"pb(
                      headers:
                          @ethernet { ethernet_header { ethertype: "0x86dd" } }
                      headers: @ipv6 { ipv6_header { next_header: "0x3a" } }
                      headers: @icmp
                      payload: @payload
                    )pb"))
                .ParseTextOrDie<dvaas::Packet>(R"pb(
                  port: @egress_port
                  parsed: @output_packet
                )pb");
        *expected_output.add_packets() =
            repo.RegisterValue("@egress_port",
                               mirror_session_params.monitor_port)
                .RegisterMessage(
                    "@output_packet", ParsePacketAndPadToMinimumSize(repo, R"pb(
                      headers: @ethernet {
                        ethernet_header {
                          ethernet_destination: @mirror_ethernet_destination
                          ethernet_source: @mirror_ethernet_source
                          ethertype: "0x8100"
                        }
                      }
                      headers: @vlan {
                        vlan_header {
                          vlan_identifier: @mirror_vlan_id
                          ethertype: "0x86dd"
                        }
                      }
                      headers: @ipv6
                      headers: @udp
                      headers: @ipfix
                      headers: @psamp_header
                      payload: @payload
                    )pb"))
                .ParseTextOrDie<dvaas::Packet>(R"pb(
                  port: @egress_port
                  parsed: @output_packet
                )pb");
        break;
      case PacketCaptureTestPacketType::kArpRequest:
        *expected_output.add_packets() =
            repo.RegisterValue("@egress_port", params.egress_port)
                .RegisterMessage("@output_packet",
                                 ParsePacketAndPadToMinimumSize(repo, R"pb(
                                   headers: @ethernet {
                                     ethernet_header {
                                       ethernet_destination: "ff:ff:ff:ff:ff:ff"
                                       ethertype: "0x0806"
                                     }
                                   }
                                   headers: @arp_request
                                   payload: @payload
                                 )pb"))
                .ParseTextOrDie<dvaas::Packet>(R"pb(
                  port: @egress_port
                  parsed: @output_packet
                )pb");
        *expected_output.add_packets() =
            repo.RegisterValue("@egress_port",
                               mirror_session_params.monitor_port)
                .RegisterMessage(
                    "@output_packet", ParsePacketAndPadToMinimumSize(repo, R"pb(
                      headers: @ethernet {
                        ethernet_header {
                          ethernet_destination: @mirror_ethernet_destination
                          ethernet_source: @mirror_ethernet_source
                          ethertype: "0x8100"
                        }
                      }
                      headers: @vlan {
                        vlan_header {
                          vlan_identifier: @mirror_vlan_id
                          ethertype: "0x86dd"
                        }
                      }
                      headers: @ipv6
                      headers: @udp
                      headers: @ipfix
                      headers: @psamp_header
                      payload: @payload
                    )pb"))
                .ParseTextOrDie<dvaas::Packet>(R"pb(
                  port: @egress_port
                  parsed: @output_packet
                )pb");
        break;
      case PacketCaptureTestPacketType::kArpResponse:
        *expected_output.add_packets() =
            repo.RegisterValue("@egress_port", params.egress_port)
                .RegisterMessage("@output_packet",
                                 ParsePacketAndPadToMinimumSize(repo, R"pb(
                                   headers: @ethernet {
                                     ethernet_header {
                                       ethernet_destination: "ff:ff:ff:ff:ff:ff"
                                       ethertype: "0x0806"
                                     }
                                   }
                                   headers: @arp_response
                                   payload: @payload
                                 )pb"))
                .ParseTextOrDie<dvaas::Packet>(R"pb(
                  port: @egress_port
                  parsed: @output_packet
                )pb");
        *expected_output.add_packets() =
            repo.RegisterValue("@egress_port",
                               mirror_session_params.monitor_port)
                .RegisterMessage(
                    "@output_packet", ParsePacketAndPadToMinimumSize(repo, R"pb(
                      headers: @ethernet {
                        ethernet_header {
                          ethernet_destination: @mirror_ethernet_destination
                          ethernet_source: @mirror_ethernet_source
                          ethertype: "0x8100"
                        }
                      }
                      headers: @vlan {
                        vlan_header {
                          vlan_identifier: @mirror_vlan_id
                          ethertype: "0x86dd"
                        }
                      }
                      headers: @ipv6
                      headers: @udp
                      headers: @ipfix
                      headers: @psamp_header
                      payload: @payload
                    )pb"))
                .ParseTextOrDie<dvaas::Packet>(R"pb(
                  port: @egress_port
                  parsed: @output_packet
                )pb");
        break;
      case PacketCaptureTestPacketType::kBgp:
        *expected_output.add_packets() =
            repo.RegisterValue("@egress_port", params.egress_port)
                .RegisterMessage(
                    "@output_packet", ParsePacketAndPadToMinimumSize(repo, R"pb(
                      headers:
                          @ethernet { ethernet_header { ethertype: "0x0800" } }
                      headers: @ipv4 { ipv4_header { protocol: "0x06" } }
                      headers: @tcp_bgp
                      payload: @payload
                    )pb"))
                .ParseTextOrDie<dvaas::Packet>(R"pb(
                  port: @egress_port
                  parsed: @output_packet
                )pb");
        *expected_output.add_packets() =
            repo.RegisterValue("@egress_port",
                               mirror_session_params.monitor_port)
                .RegisterMessage(
                    "@output_packet", ParsePacketAndPadToMinimumSize(repo, R"pb(
                      headers: @ethernet {
                        ethernet_header {
                          ethernet_destination: @mirror_ethernet_destination
                          ethernet_source: @mirror_ethernet_source
                          ethertype: "0x8100"
                        }
                      }
                      headers: @vlan {
                        vlan_header {
                          vlan_identifier: @mirror_vlan_id
                          ethertype: "0x86dd"
                        }
                      }
                      headers: @ipv6
                      headers: @udp
                      headers: @ipfix
                      headers: @psamp_header
                      payload: @payload
                    )pb"))
                .ParseTextOrDie<dvaas::Packet>(R"pb(
                  port: @egress_port
                  parsed: @output_packet
                )pb");
        break;
    }

    test_vector = repo.RegisterMessage("@expected_output", expected_output)
                      .ParseTextOrDie<dvaas::PacketTestVector>(R"pb(
                        input {
                          type: DATAPLANE
                          packet { port: @ingress_port parsed: @input_packet }
                        }
                        acceptable_outputs: @expected_output
                      )pb");
    test_vector.mutable_input()->set_type(
        dvaas::SwitchInput::SUBMIT_TO_INGRESS);
    test_vectors.push_back(test_vector);
  }
  return test_vectors;
}

TEST_P(ControllerPacketCaptureTestWithoutIxia,
       SwitchCapturesControlPacketWithVlanTagAndRedirectsToPort) {
  const int kPortsToUseInTest = 3;

  dvaas::DataplaneValidationParams dvaas_params = GetParam().validation_params;
  thinkit::MirrorTestbed& testbed =
      GetParam().testbed_interface->GetMirrorTestbed();

  // Initialize the connection, clear all entities, and (for the SUT) push
  // P4Info.
  ASSERT_OK_AND_ASSIGN(
      auto sut_p4rt_session,
      pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
          testbed.Sut(),
          /*gnmi_config=*/std::nullopt, GetParam().sut_p4info));

  ASSERT_OK_AND_ASSIGN(auto sut_ir_p4info,
                       pdpi::GetIrP4Info(*sut_p4rt_session));
  ASSERT_OK(pdpi::ClearEntities(*sut_p4rt_session));

  // Collect port IDs.
  // Get SUT and control ports to test on.
  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, testbed.Sut().CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(std::vector<std::string> sut_port_ids,
                       GetNUpInterfacePortIds(*gnmi_stub, kPortsToUseInTest));

  const std::string kMirrorSessionId = "psamp_mirror";
  const ControllerPacketCaptureParams controller_packet_capture_params = {
      .ingress_port = absl::StrCat(GetParam().cpu_port_id),
      .egress_port = sut_port_ids[0],
      .ingress_vlan_ids = GetParam().vlans_to_be_tested,
      .forwarded_packet_vlan_id = 4095,
      .mirror_session_id = kMirrorSessionId,
      .packet_type = GetParam().packet_type};

  ASSERT_OK_AND_ASSIGN(
      std::vector<p4::v1::Entity> acl_entities,
      CreatePreIngressAclEntries(
          sut_ir_p4info, controller_packet_capture_params.ingress_port,
          controller_packet_capture_params.ingress_vlan_ids,
          controller_packet_capture_params.forwarded_packet_vlan_id));
  ASSERT_OK(pdpi::InstallPiEntities(sut_p4rt_session.get(), sut_ir_p4info,
                                    acl_entities));

  // Configure mirror session attributes.
  const sai::MirrorSessionParams mirror_session_params =
      sai::MirrorSessionParams{
          .mirror_session_id = kMirrorSessionId,
          .monitor_port = sut_port_ids[1],
          .monitor_backup_port = sut_port_ids[1],
          .mirror_encap_src_mac = "00:00:00:22:22:22",
          .mirror_encap_dst_mac = "00:00:00:44:44:44",
          .mirror_encap_vlan_id = "0x0fe",
          .mirror_encap_src_ip = "2222:2222:2222:2222:2222:2222:2222:2222",
          .mirror_encap_dst_ip = "4444:4444:4444:4444:4444:4444:4444:4444",
          .mirror_encap_udp_src_port = "0x08ae",
          .mirror_encap_udp_dst_port = "0x1283"};
  // Install ACL table entry to match on inject port on Control switch
  // and mirror-to-port on SUT.
  ASSERT_OK_AND_ASSIGN(
      const std::vector<p4::v1::Entity> entries,
      CreateEntriesToMatchOnAclMetadataAndMirrorTrafficAndRedirectToPort(
          sut_ir_p4info, mirror_session_params,
          controller_packet_capture_params.ingress_vlan_ids,
          controller_packet_capture_params.egress_port, kMirrorSessionId));
  ASSERT_OK(
      pdpi::InstallPiEntities(sut_p4rt_session.get(), sut_ir_p4info, entries));
  // Build test vectors.
  ASSERT_OK_AND_ASSIGN(
      std::vector<dvaas::PacketTestVector> test_vector,
      CreateControllerPacketCaptureTestVectors(controller_packet_capture_params,
                                               mirror_session_params));

  dvaas_params.packet_test_vector_override = test_vector;

  const google::protobuf::FieldDescriptor* ipfix_header_descriptor =
      packetlib::Header::descriptor()->FindFieldByName("ipfix_header");
  if (ipfix_header_descriptor == nullptr) {
    FAIL() << "IPFIX header not found in packetlib";
  }
  const google::protobuf::FieldDescriptor* psamp_header_descriptor =
      packetlib::Header::descriptor()->FindFieldByName("psamp_header");
  if (psamp_header_descriptor == nullptr) {
    FAIL() << "PSAMP header not found in packetlib";
  }
  dvaas_params.switch_output_diff_params.ignored_packetlib_fields.push_back(
      ipfix_header_descriptor);
  dvaas_params.switch_output_diff_params.ignored_packetlib_fields.push_back(
      psamp_header_descriptor);
  const google::protobuf::FieldDescriptor*
      ipv6_header_payload_length_descriptor =
          packetlib::Ipv6Header::descriptor()->FindFieldByName(
              "payload_length");
  if (ipv6_header_payload_length_descriptor == nullptr) {
    FAIL() << "IPv6 header field payload_length not found in packetlib";
  }
  dvaas_params.switch_output_diff_params.ignored_packetlib_fields.push_back(
      ipv6_header_payload_length_descriptor);
  const google::protobuf::FieldDescriptor* udp_header_length_descriptor =
      packetlib::UdpHeader::descriptor()->FindFieldByName("length");
  if (udp_header_length_descriptor == nullptr) {
    FAIL() << "UDP header field length not found in packetlib";
  }
  const google::protobuf::FieldDescriptor* udp_header_checksum_descriptor =
      packetlib::UdpHeader::descriptor()->FindFieldByName("checksum");
  if (udp_header_checksum_descriptor == nullptr) {
    FAIL() << "UDP header field checksum not found in packetlib";
  }
  dvaas_params.switch_output_diff_params.ignored_packetlib_fields.push_back(
      udp_header_length_descriptor);
  dvaas_params.switch_output_diff_params.ignored_packetlib_fields.push_back(
      udp_header_checksum_descriptor);
  const google::protobuf::FieldDescriptor* payload_descriptor =
      packetlib::Packet::descriptor()->FindFieldByName("payload");
  if (payload_descriptor == nullptr) {
    FAIL() << "Payload field not found in packetlib";
  }
  dvaas_params.switch_output_diff_params.ignored_packetlib_fields.push_back(
      payload_descriptor);

  // Send test packets.
  LOG(INFO) << "Sending test packets.";
  ASSERT_OK_AND_ASSIGN(
      dvaas::ValidationResult validation_result,
      GetParam().validator->ValidateDataplane(testbed, dvaas_params));
  // Validate traffic.
  validation_result.LogStatistics();
  EXPECT_OK(validation_result.HasSuccessRateOfAtLeast(1.0));
}

}  // anonymous namespace
}  // namespace pins_test
