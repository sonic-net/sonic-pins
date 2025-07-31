// Copyright 2025 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
#include "tests/forwarding/timestamping_test.h"

#include <cstdint>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "lib/gnmi/gnmi_helper.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "tests/forwarding/util.h"
#include "tests/lib/common_ir_table_entries.h"
#include "tests/lib/p4rt_fixed_table_programming_helper.h"

namespace pins {
namespace {

// PTP headers exist inside a UDP header so the specific MAC addresses do not
// matter for testing. We use this global MAC to ensure the flows we install on
// the switch and packets we send to the switch are in sync.
const absl::string_view kSwitchMac = "00:11:11:11:11:11";

// When parsing packet headers a PTP header is identified by a UDP packet with
// destination port 319 (0x013f in hex).
const absl::string_view kPtpEventUdpDstPort = "0x013f";

// send_to_ingress is a special port created on the switch which allows the CPU
// to inject a packet into the ingress pipeline.
constexpr absl::string_view kSendToIngress = "send_to_ingress";

absl::Status PuntAllPacketToCpu(pdpi::P4RuntimeSession& session,
                                const pdpi::IrP4Info& ir_p4info) {
  LOG(INFO) << "Punting all packet to the CPU.";
  p4::v1::WriteRequest write_request;

  auto& update = *write_request.add_updates();
  update.set_type(p4::v1::Update::INSERT);
  ASSIGN_OR_RETURN(
      *update.mutable_entity()->mutable_table_entry(),
      pdpi::IrTableEntryToPi(ir_p4info, PuntAllPacketsToControllerIrTableEntry(
                                            /*queue_id=*/"0x7")));

  return pdpi::SetMetadataAndSendPiWriteRequest(&session, write_request);
}

absl::Status SendAllTrafficToVrf(pdpi::P4RuntimeSession& session,
                                 const pdpi::IrP4Info& ir_p4info,
                                 absl::string_view vrf_id) {
  LOG(INFO) << absl::StreamFormat(
      "Creating VRF '%s' and assigning all traffic to it.", vrf_id);
  p4::v1::WriteRequest write_request;
  ASSIGN_OR_RETURN(*write_request.add_updates(),
                   VrfTableUpdate(ir_p4info, p4::v1::Update::INSERT, vrf_id));

  auto& forward_vrf_update = *write_request.add_updates();
  forward_vrf_update.set_type(p4::v1::Update::INSERT);
  ASSIGN_OR_RETURN(*forward_vrf_update.mutable_entity()->mutable_table_entry(),
                   pdpi::IrTableEntryToPi(
                       ir_p4info, SetVrfIdForAllPacketsIrTableEntry(vrf_id)));

  return pdpi::SetMetadataAndSendPiWriteRequest(&session, write_request);
}

absl::StatusOr<std::vector<WcmpAction>> CreateNextHopsForPorts(
    pdpi::P4RuntimeSession& session, const pdpi::IrP4Info& ir_p4info,
    absl::Span<const std::string> ports) {
  const absl::string_view kPeerSwitchMac = "00:22:22:22:22:22";
  const absl::string_view kNeighborId = "fe80::2";

  p4::v1::WriteRequest write_request;
  std::vector<WcmpAction> nexthop_info;
  for (const std::string& port : ports) {
    std::string rif_id = absl::StrCat("rif-", port);
    std::string nexthop_id = absl::StrCat("nexthop-", port);

    LOG(INFO) << absl::StreamFormat(
        "Adding nexthop route from (%s) to (%s,%s) through: %s, and %s",
        kSwitchMac, kPeerSwitchMac, kNeighborId, rif_id, nexthop_id);

    ASSIGN_OR_RETURN(
        *write_request.add_updates(),
        RouterInterfaceTableUpdate(ir_p4info, p4::v1::Update::INSERT, rif_id,
                                   port, kSwitchMac));
    ASSIGN_OR_RETURN(*write_request.add_updates(),
                     NeighborTableUpdate(ir_p4info, p4::v1::Update::INSERT,
                                         rif_id, kNeighborId, kPeerSwitchMac));
    ASSIGN_OR_RETURN(*write_request.add_updates(),
                     NexthopTableUpdate(ir_p4info, p4::v1::Update::INSERT,
                                        nexthop_id, rif_id, kNeighborId));
    nexthop_info.push_back(WcmpAction{
        .nexthop_id = nexthop_id,
        .weight = 1,
        .watch_port = port,
    });
  }

  RETURN_IF_ERROR(
      pdpi::SetMetadataAndSendPiWriteRequest(&session, write_request));
  return nexthop_info;
}

// If we have only 1 nexthop then we use the set_nexthop action, but if we have
// >1 nexthops we create a WCMP group and use the set_wcmp_group_id action.
absl::Status ForwardAllIpTrafficToPorts(pdpi::P4RuntimeSession& session,
                                        const pdpi::IrP4Info& ir_p4info,
                                        absl::Span<const std::string> ports) {
  const std::string kVrfId = "vrf-80";

  RETURN_IF_ERROR(SendAllTrafficToVrf(session, ir_p4info, kVrfId));
  ASSIGN_OR_RETURN(std::vector<WcmpAction> nexthops,
                   CreateNextHopsForPorts(session, ir_p4info, ports));

  p4::v1::WriteRequest write_request;

  if (nexthops.empty()) {
    return absl::InvalidArgumentError(
        "Need at least 1 next hop to forward IP traffic through.");
  } else if (nexthops.size() == 1) {
    std::string nexthop_id = nexthops[0].nexthop_id;
    LOG(INFO) << absl::StreamFormat(
        "Assigning all IPv4 and IPv6 traffic from VRF '%s' to Nexthop '%s'.",
        kVrfId, nexthop_id);
    ASSIGN_OR_RETURN(
        *write_request.add_updates(),
        Ipv4TableUpdate(ir_p4info, p4::v1::Update::INSERT,
                        IpTableOptions{
                            .vrf_id = kVrfId,
                            .action = IpTableOptions::Action::kSetNextHopId,
                            .nexthop_id = nexthop_id,
                        }));
    ASSIGN_OR_RETURN(
        *write_request.add_updates(),
        Ipv6TableUpdate(ir_p4info, p4::v1::Update::INSERT,
                        IpTableOptions{
                            .vrf_id = kVrfId,
                            .action = IpTableOptions::Action::kSetNextHopId,
                            .nexthop_id = nexthop_id,
                        }));
  } else {
    std::string wcmp_group_id = "group-1";
    LOG(INFO) << absl::StreamFormat("Creating WCMP group '%s'.", wcmp_group_id);
    ASSIGN_OR_RETURN(*write_request.add_updates(),
                     WcmpGroupTableUpdate(ir_p4info, p4::v1::Update::INSERT,
                                          wcmp_group_id, nexthops));

    LOG(INFO) << absl::StreamFormat(
        "Assigning all IPv4 and IPv6 traffic from VRF '%s' to WCMP group '%s'.",
        kVrfId, wcmp_group_id);
    ASSIGN_OR_RETURN(
        *write_request.add_updates(),
        Ipv4TableUpdate(ir_p4info, p4::v1::Update::INSERT,
                        IpTableOptions{
                            .vrf_id = kVrfId,
                            .action = IpTableOptions::Action::kSetWcmpGroupId,
                            .wcmp_group_id = wcmp_group_id,
                        }));
    ASSIGN_OR_RETURN(
        *write_request.add_updates(),
        Ipv6TableUpdate(ir_p4info, p4::v1::Update::INSERT,
                        IpTableOptions{
                            .vrf_id = kVrfId,
                            .action = IpTableOptions::Action::kSetWcmpGroupId,
                            .wcmp_group_id = wcmp_group_id,
                        }));
  }

  // Admit all traffic to L3.
  LOG(INFO) << "Forwarding all traffic to IP routing.";
  ASSIGN_OR_RETURN(
      *write_request.add_updates(),
      L3AdmitTableUpdate(ir_p4info, p4::v1::Update::INSERT,
                         L3AdmitOptions{
                             .priority = 2070,
                             .dst_mac = std::make_pair("00:00:00:00:00:00",
                                                       "01:00:00:00:00:00"),
                         }));

  return pdpi::SetMetadataAndSendPiWriteRequest(&session, write_request);
}

packetlib::Packet GetGenericIpHeadersForUdpPacket(bool use_ipv4) {
  packetlib::Packet packet;

  // Ethernet
  packetlib::Header& ethernet = *packet.add_headers();
  ethernet.mutable_ethernet_header()->set_ethernet_destination(kSwitchMac);
  ethernet.mutable_ethernet_header()->set_ethernet_source("00:00:22:22:00:00");

  if (use_ipv4) {
    ethernet.mutable_ethernet_header()->set_ethertype("0x0800");

    packetlib::Header& ip = *packet.add_headers();
    ip.mutable_ipv4_header()->set_version("0x4");
    ip.mutable_ipv4_header()->set_ihl("0x5");
    ip.mutable_ipv4_header()->set_dscp("0x1b");
    ip.mutable_ipv4_header()->set_ecn("0x1");
    ip.mutable_ipv4_header()->set_identification("0x0000");
    ip.mutable_ipv4_header()->set_flags("0x0");
    ip.mutable_ipv4_header()->set_fragment_offset("0x0000");
    ip.mutable_ipv4_header()->set_ttl("0x10");
    ip.mutable_ipv4_header()->set_protocol("0x11");
    ip.mutable_ipv4_header()->set_ipv4_source("10.0.0.1");
    ip.mutable_ipv4_header()->set_ipv4_destination("10.0.0.2");
  } else {
    ethernet.mutable_ethernet_header()->set_ethertype("0x86dd");

    packetlib::Header& ip = *packet.add_headers();
    ip.mutable_ipv6_header()->set_version("0x6");
    ip.mutable_ipv6_header()->set_dscp("0x1b");
    ip.mutable_ipv6_header()->set_ecn("0x1");
    ip.mutable_ipv6_header()->set_flow_label("0x12345");
    ip.mutable_ipv6_header()->set_next_header("0x11");
    ip.mutable_ipv6_header()->set_hop_limit("0x10");
    ip.mutable_ipv6_header()->set_ipv6_source("2607:f8b0:11::");
    ip.mutable_ipv6_header()->set_ipv6_destination("2607:f8b0:12::");
  }
  return packet;
}

struct UdpHeaderOptions {
  std::string source_port = "0x0014";
  std::string destination_port = "0x0015";
  std::string checksum = "0x0000";
};

packetlib::Header GetUdpHeader(const UdpHeaderOptions& options) {
  packetlib::Header udp;
  udp.mutable_udp_header()->set_source_port(options.source_port);
  udp.mutable_udp_header()->set_destination_port(options.destination_port);
  udp.mutable_udp_header()->set_checksum(options.checksum);
  return udp;
}

struct PtpHeaderOptions {
  std::string transport_specific = "0x0";
  std::string message_type = "0x0";
  std::string reserved0 = "0x0";
  std::string version_ptp = "0x2";  // Default to v2 which our switches support.
  std::string domain_number = "0x00";
  std::string reserved1 = "0x00";
  std::string flags = "0x0000";
  std::string correction_field = "0x0000000000000000";
  std::string reserved2 = "0x00000000";
  std::string source_port_identity = "0x00000000000000000000";
  std::string sequence_id = "0x0000";
  std::string control_field = "0x00";
  std::string log_message_interval = "0x00";
};

packetlib::Header GetPtpHeader(const PtpHeaderOptions& options) {
  packetlib::Header ptp;
  ptp.mutable_ptp_header()->set_transport_specific(options.transport_specific);
  ptp.mutable_ptp_header()->set_message_type(options.message_type);
  ptp.mutable_ptp_header()->set_reserved0(options.reserved0);
  ptp.mutable_ptp_header()->set_version_ptp(options.version_ptp);
  ptp.mutable_ptp_header()->set_domain_number(options.domain_number);
  ptp.mutable_ptp_header()->set_reserved1(options.reserved1);
  ptp.mutable_ptp_header()->set_flags(options.flags);
  ptp.mutable_ptp_header()->set_correction_field(options.correction_field);
  ptp.mutable_ptp_header()->set_reserved2(options.reserved2);
  ptp.mutable_ptp_header()->set_source_port_identity(
      options.source_port_identity);
  ptp.mutable_ptp_header()->set_sequence_id(options.sequence_id);
  ptp.mutable_ptp_header()->set_control_field(options.control_field);
  ptp.mutable_ptp_header()->set_log_message_interval(
      options.log_message_interval);
  return ptp;
}

absl::Status SendPacketsToSwitch(pdpi::P4RuntimeSession& session,
                                 const pdpi::IrP4Info& ir_p4info,
                                 absl::string_view port,
                                 absl::Span<const packetlib::Packet> packets) {
  // Rate limit to 500pps to avoid punt packet drops on the control switch.
  absl::Duration kDelay = absl::Milliseconds(2);

  LOG(INFO) << absl::StreamFormat("Sending %d packets to port '%s'.",
                                  packets.size(), port);
  for (const auto& packet : packets) {
    ASSIGN_OR_RETURN(std::string raw_packet,
                     packetlib::SerializePacket(packet));

    if (port == kSendToIngress) {
      RETURN_IF_ERROR(
          InjectIngressPacket(raw_packet, ir_p4info, &session, kDelay));
    } else {
      RETURN_IF_ERROR(InjectEgressPacket(std::string{port}, raw_packet,
                                         ir_p4info, &session, kDelay));
    }
  }
  return absl::OkStatus();
}

struct TestPacketInfo {
  std::string payload;
  int32_t packet_count = 0;
};

bool UpdatePacketCountByPayload(std::vector<TestPacketInfo>& payloads,
                                const packetlib::Packet& packet) {
  for (auto& payload_info : payloads) {
    if (absl::StrContains(packet.payload(), payload_info.payload)) {
      ++payload_info.packet_count;
      return true;
    }
  }
  LOG(WARNING) << "Unexpected packet payload: " << packet.DebugString();
  return false;
}

bool UpdatePacketCountByPayload(std::vector<TestPacketInfo>& payloads,
                                const p4::v1::StreamMessageResponse& message) {
  if (message.update_case() != p4::v1::StreamMessageResponse::kPacket) {
    LOG(WARNING) << "Unexpected stream response: " << message.DebugString();
  }

  packetlib::Packet packet = packetlib::ParsePacket(message.packet().payload());
  return UpdatePacketCountByPayload(payloads, packet);
}

TEST_P(TimestampingTestFixture, InvalidPtpPacketsAreDropped) {
  // We use the control_port to send traffic through the front-panel ports. The
  // SUT ports will be used to forward any IP traffic.
  ASSERT_OK_AND_ASSIGN(std::string control_port,
                       pins_test::GetAnyUpInterfacePortId(*control_gnmi_stub_));
  ASSERT_OK_AND_ASSIGN(std::vector<std::string> sut_ports,
                       pins_test::GetNUpInterfacePortIds(*sut_gnmi_stub_, 4));

  // Configure the control switch to collect all packets, and the SUT to forward
  // any IP traffic.
  ASSERT_OK(PuntAllPacketToCpu(*control_p4rt_session_, ir_p4info_));
  ASSERT_OK(
      ForwardAllIpTrafficToPorts(*sut_p4rt_session_, ir_p4info_, sut_ports));

  // Create 8000 packets that we expect to be dropped. We expect our switches to
  // use PTPv2, and drop PTPv1 packets. PTPv3 doesn't exist in the standard and
  // is invalid so it should be dropped as well.
  std::vector<TestPacketInfo> test_packet_info = {
      TestPacketInfo{
          .payload = "PTPv1 packet that should be dropped (front-panel).",
      },
      TestPacketInfo{
          .payload = "PTPv1 packet that should be dropped (submit_to_ingress).",
      },
      TestPacketInfo{
          .payload = "PTPv3 packet that should be dropped (front-panel).",
      },
      TestPacketInfo{
          .payload = "PTPv3 packet that should be dropped (submit_to_ingress).",
      },
  };
  std::vector<packetlib::Packet> front_panel_packets;
  std::vector<packetlib::Packet> submit_to_ingress_packets;
  for (int i = 0; i < 2000; ++i) {
    // Alternate between IPv4 and IPv6 packets.
    packetlib::Packet ptpv1_packet =
        GetGenericIpHeadersForUdpPacket(/*use_ipv4=*/i % 2);
    *ptpv1_packet.add_headers() = GetUdpHeader(UdpHeaderOptions{
        .destination_port = std::string{kPtpEventUdpDstPort},
    });
    *ptpv1_packet.add_headers() =
        GetPtpHeader(PtpHeaderOptions{.version_ptp = "0x1"});

    packetlib::Packet ptpv3_packet =
        GetGenericIpHeadersForUdpPacket(/*use_ipv4=*/i % 2);
    *ptpv3_packet.add_headers() = GetUdpHeader(UdpHeaderOptions{
        .destination_port = std::string{kPtpEventUdpDstPort},
    });
    *ptpv3_packet.add_headers() =
        GetPtpHeader(PtpHeaderOptions{.version_ptp = "0x3"});

    front_panel_packets.push_back(ptpv1_packet);
    front_panel_packets.back().set_payload(
        absl::Substitute("[Packet:$0] $1", i, test_packet_info[0].payload));

    submit_to_ingress_packets.push_back(ptpv1_packet);
    submit_to_ingress_packets.back().set_payload(
        absl::Substitute("[Packet:$0] $1", i, test_packet_info[1].payload));

    front_panel_packets.push_back(ptpv3_packet);
    front_panel_packets.back().set_payload(
        absl::Substitute("[Packet:$0] $1", i, test_packet_info[2].payload));

    submit_to_ingress_packets.push_back(ptpv3_packet);
    submit_to_ingress_packets.back().set_payload(
        absl::Substitute("[Packet:$0] $1", i, test_packet_info[3].payload));
  }
  ASSERT_OK(SendPacketsToSwitch(*control_p4rt_session_, ir_p4info_,
                                control_port, front_panel_packets));
  ASSERT_OK(SendPacketsToSwitch(*sut_p4rt_session_, ir_p4info_, kSendToIngress,
                                submit_to_ingress_packets));

  // Wait for some fixed time then collect all packets that made it through the
  // SUT switch, and back to the control switch.
  ASSERT_OK_AND_ASSIGN(
      std::vector<p4::v1::StreamMessageResponse> messages,
      control_p4rt_session_->GetAllStreamMessagesFor(absl::Seconds(10)));
  LOG(INFO) << "Done collecting packets.";

  // Verify that none of the packets which made it through are PTPv1 packets.
  std::vector<std::string> ptpv1_packets;
  for (const auto& message : messages) {
    if (UpdatePacketCountByPayload(test_packet_info, message)) {
      packetlib::Packet packet_in =
          packetlib::ParsePacket(message.packet().payload());
      ptpv1_packets.push_back(packet_in.DebugString());
    }
  }

  // If we did see any PTPv1 packets store them as a test artifact to help when
  // triaging failures.
  if (!ptpv1_packets.empty()) {
    absl::Status status = GetMirrorTestbed().Environment().StoreTestArtifact(
        "ptpv1_packets_that_were_not_dropped.txt",
        absl::StrJoin(ptpv1_packets, "\n"));
    LOG_IF(WARNING, !status.ok())
        << "Could not save PTPv1 packets as an artifact: " << status;
  }

  EXPECT_EQ(test_packet_info[0].packet_count, 0) << "ptpv1 front-panel ports";
  EXPECT_EQ(test_packet_info[1].packet_count, 0) << "ptpv1 submit_to_ingress";
  EXPECT_EQ(test_packet_info[2].packet_count, 0) << "ptpv3 front-panel ports";
  EXPECT_EQ(test_packet_info[3].packet_count, 0) << "ptpv3 submit_to_ingress";
}

TEST_P(TimestampingTestFixture, PtpV2PacketsAreForwardedSuccessfully) {
  // We use the control_port to send traffic through the front-panel ports. The
  // SUT ports will be used to forward any IP traffic.
  ASSERT_OK_AND_ASSIGN(std::string control_port,
                       pins_test::GetAnyUpInterfacePortId(*control_gnmi_stub_));
  ASSERT_OK_AND_ASSIGN(std::vector<std::string> sut_ports,
                       pins_test::GetNUpInterfacePortIds(*sut_gnmi_stub_, 4));

  // Configure the control switch to collect all packets, and the SUT to forward
  // any IP traffic.
  ASSERT_OK(PuntAllPacketToCpu(*control_p4rt_session_, ir_p4info_));
  ASSERT_OK(
      ForwardAllIpTrafficToPorts(*sut_p4rt_session_, ir_p4info_, sut_ports));

  // Create 4000 PTPv2 packets. We will send 2000 of them through a front-panel
  // port, and 2000 of them through submit_to_ingress. We expect all these
  // packets to be forwarded by the SUT switch, and have an updated
  // 'correction_field' value.
  constexpr absl::string_view kZeroValueCorrectionField = "0x0000000000000000";
  std::vector<TestPacketInfo> test_packet_info = {
      TestPacketInfo{
          .payload =
              "Sample PTPv2 packet that should be forwarded (front-panel).",
      },
      TestPacketInfo{
          .payload = "Sample PTPv2 packet that should be forwarded "
                     "(submit_to_ingress).",
      },
  };
  std::vector<packetlib::Packet> front_panel_packets;
  std::vector<packetlib::Packet> submit_to_ingress_packets;
  for (int i = 0; i < 2000; ++i) {
    // Mix IPv4 and IPv6 packets.
    packetlib::Packet packet =
        GetGenericIpHeadersForUdpPacket(/*use_ipv4=*/i % 2);
    *packet.add_headers() = GetUdpHeader(UdpHeaderOptions{
        .destination_port = std::string{kPtpEventUdpDstPort},
    });
    *packet.add_headers() = GetPtpHeader(PtpHeaderOptions{
        .version_ptp = "0x2",
        .correction_field = std::string{kZeroValueCorrectionField},
    });

    front_panel_packets.push_back(packet);
    front_panel_packets.back().set_payload(
        absl::Substitute("[Packet:$0] $1", i, test_packet_info[0].payload));
    submit_to_ingress_packets.push_back(packet);
    submit_to_ingress_packets.back().set_payload(
        absl::Substitute("[Packet:$0] $1", i, test_packet_info[1].payload));
  }
  ASSERT_OK(SendPacketsToSwitch(*control_p4rt_session_, ir_p4info_,
                                control_port, front_panel_packets));
  ASSERT_OK(SendPacketsToSwitch(*sut_p4rt_session_, ir_p4info_, kSendToIngress,
                                submit_to_ingress_packets));

  int number_of_expected_packets =
      front_panel_packets.size() + submit_to_ingress_packets.size();
  ASSERT_OK(control_p4rt_session_->HandleNextNStreamMessages(
      [&](const p4::v1::StreamMessageResponse& message) {
        if (message.update_case() != p4::v1::StreamMessageResponse::kPacket) {
          LOG(WARNING) << "Unexpected stream response: "
                       << message.DebugString();
        }
        packetlib::Packet packet =
            packetlib::ParsePacket(message.packet().payload());

        // First verify that this packet has the payload we sent with it.
        bool correct_payload =
            UpdatePacketCountByPayload(test_packet_info, message);
        if (!correct_payload) return false;

        // Then verify that the correction field has been changed. We can't
        // predict what value to expect so we simply check that it is not 0.
        if (packet.headers_size() < 4 ||
            packet.headers(3).ptp_header().correction_field() ==
                kZeroValueCorrectionField) {
          static bool first_failure = false;  // only report the first failure.
          if (!first_failure) {
            ADD_FAILURE() << "PTPv2 correction field was not updated:\n"
                          << packet.DebugString();
            first_failure = true;
          }
        }

        // So long as we see a packet with our expected payload we return true.
        // Otherwise, this test will stall until the timeout waiting for the
        // "correct" packet.
        return correct_payload;
      },
      number_of_expected_packets, /*timeout=*/absl::Minutes(1)));
  LOG(INFO) << "Done collecting packets.";

  EXPECT_EQ(test_packet_info[0].packet_count, front_panel_packets.size());
  EXPECT_EQ(test_packet_info[1].packet_count, submit_to_ingress_packets.size());
}

}  // namespace
}  // namespace pins
