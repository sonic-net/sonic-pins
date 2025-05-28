// Copyright 2024 Google LLC
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

#include "tests/forwarding/l3_admit_test.h"

#include <algorithm>
#include <iterator>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "absl/log/log.h"
#include "absl/random/random.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/gnmi/openconfig.pb.h"
#include "lib/p4rt/p4rt_port.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/netaddr/ipv4_address.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.pb.h"
#include "tests/forwarding/util.h"
#include "tests/lib/p4info_helper.h"
#include "tests/lib/p4rt_fixed_table_programming_helper.h"
#include "thinkit/mirror_testbed_fixture.h"
#include "thinkit/switch.h"

namespace pins {
namespace {

// Depending on the test we may want to send packets with, or without, a VLAN
// ID. If the test want's to use a VLAN ID it should choose the value itself,
// otherwise it can use this constant to say no VLAN ID should be set.
constexpr absl::string_view kNoVlanId = "";

// send_to_ingress is a special port created on the switch which allows the CPU
// to inject a packet into the ingress pipeline.
constexpr absl::string_view kSendToIngress = "send_to_ingress";

absl::Status AddAndSetDefaultVrf(pdpi::P4RuntimeSession& session,
                                 const pdpi::IrP4Info& ir_p4info,
                                 const std::string& vrf_id) {
  LOG(INFO) << "Assigning all packets to VRF " << vrf_id << ".";
  pdpi::IrUpdate set_vrf_ir_update;
  RETURN_IF_ERROR(gutil::ReadProtoFromString(
      absl::Substitute(R"pb(
                         type: INSERT
                         entity {
                           table_entry {
                             table_name: "acl_pre_ingress_table"
                             priority: 2000
                             action {
                               name: "set_vrf"
                               params {
                                 name: "vrf_id"
                                 value { str: "$0" }
                               }
                             }
                           }
                         }
                       )pb",
                       vrf_id),
      &set_vrf_ir_update));

  p4::v1::WriteRequest pi_write_request;
  ASSIGN_OR_RETURN(*pi_write_request.add_updates(),
                   VrfTableUpdate(ir_p4info, p4::v1::Update::INSERT, vrf_id));
  ASSIGN_OR_RETURN(*pi_write_request.add_updates(),
                   pdpi::IrUpdateToPi(ir_p4info, set_vrf_ir_update));
  return pdpi::SetMetadataAndSendPiWriteRequest(&session, pi_write_request);
}

absl::Status AllowVrfTrafficToDstMac(pdpi::P4RuntimeSession& session,
                                     const pdpi::IrP4Info& ir_p4info,
                                     const std::string& dst_mac,
                                     const std::string& vrf_id) {
  LOG(INFO) << "Assigning " << dst_mac << " packets with to " << vrf_id << ".";
  pdpi::IrUpdate set_vrf_ir_update;
  RETURN_IF_ERROR(gutil::ReadProtoFromString(
      absl::Substitute(R"pb(
                         type: INSERT
                         entity {
                           table_entry {
                             table_name: "acl_pre_ingress_table"
                             matches {
                               name: "dst_mac"
                               ternary {
                                 value { mac: "$0" }
                                 mask { mac: "ff:ff:ff:ff:ff:ff" }
                               }
                             }
                             priority: 2000
                             action {
                               name: "set_vrf"
                               params {
                                 name: "vrf_id"
                                 value { str: "$1" }
                               }
                             }
                           }
                         }
                       )pb",
                       dst_mac, vrf_id),
      &set_vrf_ir_update));

  p4::v1::WriteRequest pi_write_request;
  ASSIGN_OR_RETURN(*pi_write_request.add_updates(),
                   VrfTableUpdate(ir_p4info, p4::v1::Update::INSERT, vrf_id));
  ASSIGN_OR_RETURN(*pi_write_request.add_updates(),
                   pdpi::IrUpdateToPi(ir_p4info, set_vrf_ir_update));
  return pdpi::SetMetadataAndSendPiWriteRequest(&session, pi_write_request);
}

absl::Status PuntAllPacketsToController(pdpi::P4RuntimeSession& session,
                                        const pdpi::IrP4Info& ir_p4info) {
  pdpi::IrWriteRequest ir_write_request;
  RETURN_IF_ERROR(gutil::ReadProtoFromString(
      R"pb(
        updates {
          type: INSERT
          entity {
            table_entry {
              table_name: "acl_ingress_table"
              priority: 2
              action {
                name: "acl_trap",
                params {
                  name: "qos_queue"
                  value { str: "0x1" }
                }
              }
            }
          }
        }
      )pb",
      &ir_write_request));

  ASSIGN_OR_RETURN(p4::v1::WriteRequest pi_write_request,
                   pdpi::IrWriteRequestToPi(ir_p4info, ir_write_request));
  return pdpi::SetMetadataAndSendPiWriteRequest(&session, pi_write_request);
}

// L3 routing configurations that can be shared when generating the L3 routing
// flows.
struct L3Route {
  std::string vrf_id;

  std::string switch_mac;
  std::pair<std::string, int> switch_ip;

  std::string peer_port;
  std::string peer_mac;
  std::string peer_ip;

  std::string router_interface_id;
  std::string nexthop_id;
};

absl::Status AddL3Route(pdpi::P4RuntimeSession& session,
                        const pdpi::IrP4Info& ir_p4info,
                        const L3Route& options) {
  LOG(INFO) << absl::StreamFormat(
      "Adding L3 route for %s, %s to port %s.", options.vrf_id,
      absl::StrCat(options.switch_ip.first, "/", options.switch_ip.second),
      options.peer_port);

  p4::v1::WriteRequest write_request;
  LOG(INFO) << "Adding router interface for " << options.switch_mac
            << " on port " << options.peer_port << ".";
  ASSIGN_OR_RETURN(
      *write_request.add_updates(),
      RouterInterfaceTableUpdate(ir_p4info, p4::v1::Update::INSERT,
                                 options.router_interface_id, options.peer_port,
                                 options.switch_mac));
  ASSIGN_OR_RETURN(*write_request.add_updates(),
                   NeighborTableUpdate(ir_p4info, p4::v1::Update::INSERT,
                                       options.router_interface_id,
                                       options.peer_ip, options.peer_mac));
  ASSIGN_OR_RETURN(
      *write_request.add_updates(),
      NexthopTableUpdate(ir_p4info, p4::v1::Update::INSERT, options.nexthop_id,
                         options.router_interface_id, options.peer_ip));
  ASSIGN_OR_RETURN(
      *write_request.add_updates(),
      Ipv4TableUpdate(ir_p4info, p4::v1::Update::INSERT,
                      IpTableOptions{
                          .vrf_id = options.vrf_id,
                          .dst_addr_lpm = options.switch_ip,
                          .action = IpTableOptions::Action::kSetNextHopId,
                          .nexthop_id = options.nexthop_id,
                      }));

  return pdpi::SetMetadataAndSendPiWriteRequest(&session, write_request);
}

absl::Status AdmitL3Route(pdpi::P4RuntimeSession& session,
                          const pdpi::IrP4Info& ir_p4info,
                          const L3AdmitOptions& options) {
  if (options.in_port.has_value()) {
    LOG(INFO) << "Admiting only L3 packets on port " << *options.in_port
              << " with DST MAC: " << options.dst_mac.first << " & "
              << options.dst_mac.second;
  } else {
    LOG(INFO) << "Admiting all L3 packets with DST MAC: "
              << options.dst_mac.first << " & " << options.dst_mac.second;
  }
  p4::v1::WriteRequest write_request;
  ASSIGN_OR_RETURN(
      *write_request.add_updates(),
      L3AdmitTableUpdate(ir_p4info, p4::v1::Update::INSERT, options));
  return pdpi::SetMetadataAndSendPiWriteRequest(&session, write_request);
}

absl::StatusOr<std::string> UdpPacket(absl::string_view dst_mac,
                                      absl::string_view vlan_id,
                                      absl::string_view dst_ip,
                                      absl::string_view payload) {
  packetlib::Packet packet;

  // Ethernet
  auto* ethernet = packet.add_headers();
  ethernet->mutable_ethernet_header()->set_ethernet_destination(dst_mac);
  ethernet->mutable_ethernet_header()->set_ethernet_source("00:00:22:22:00:00");
  ethernet->mutable_ethernet_header()->set_ethertype("0x0800");

  // VLAN
  if (!vlan_id.empty()) {
    auto* vlan = packet.add_headers();
    vlan->mutable_vlan_header()->set_priority_code_point("0x0");
    vlan->mutable_vlan_header()->set_drop_eligible_indicator("0x0");
    vlan->mutable_vlan_header()->set_vlan_identifier(vlan_id);
    vlan->mutable_vlan_header()->set_ethertype(
        ethernet->ethernet_header().ethertype());

    ethernet->mutable_ethernet_header()->set_ethertype("0x8100");
  }

  // IP
  auto* ip = packet.add_headers();
  ip->mutable_ipv4_header()->set_version("0x4");
  ip->mutable_ipv4_header()->set_ihl("0x5");
  ip->mutable_ipv4_header()->set_dscp("0x1b");
  ip->mutable_ipv4_header()->set_ecn("0x1");
  ip->mutable_ipv4_header()->set_identification("0x0000");
  ip->mutable_ipv4_header()->set_flags("0x0");
  ip->mutable_ipv4_header()->set_fragment_offset("0x0000");
  ip->mutable_ipv4_header()->set_ttl("0x10");
  ip->mutable_ipv4_header()->set_protocol("0x11");
  ip->mutable_ipv4_header()->set_ipv4_source("10.0.0.1");
  ip->mutable_ipv4_header()->set_ipv4_destination(dst_ip);

  // UDP
  auto* udp = packet.add_headers();
  udp->mutable_udp_header()->set_source_port("0x0014");
  udp->mutable_udp_header()->set_destination_port("0x000a");

  // Payload
  packet.set_payload(payload);

  return packetlib::SerializePacket(packet);
}

absl::Status SendUdpPacket(pdpi::P4RuntimeSession& session,
                           const pdpi::IrP4Info& ir_p4info,
                           absl::string_view port_id, int packet_count,
                           absl::string_view dst_mac, absl::string_view vlan_id,
                           absl::string_view dst_ip,
                           absl::string_view payload) {
  LOG(INFO) << absl::StreamFormat("Sending %d packets with %s, %s to port %s.",
                                  packet_count, dst_mac, dst_ip, port_id);

  for (int i = 0; i < packet_count; ++i) {
    ASSIGN_OR_RETURN(std::string packet,
                     UdpPacket(dst_mac, vlan_id, dst_ip,
                               absl::Substitute("[Packet:$0] $1", i, payload)));
    // Rate limit to 500pps to avoid punt packet drops on the control switch.
    if (port_id == kSendToIngress) {
      RETURN_IF_ERROR(
          InjectIngressPacket(packet, ir_p4info, &session,
                              /*packet_delay=*/absl::Milliseconds(2)));
    } else {
      RETURN_IF_ERROR(
          InjectEgressPacket(std::string{port_id}, packet, ir_p4info, &session,
                             /*packet_delay=*/absl::Milliseconds(2)));
    }
  }
  return absl::OkStatus();
}

bool IsNonLagEthernetInterface(
    const pins_test::openconfig::Interfaces::Interface& interface) {
  return interface.state().enabled() && interface.state().has_p4rt_id() &&
         absl::StartsWith(interface.name(), "Ethernet") &&
         interface.ethernet().state().aggregate_id().empty();
}

absl::StatusOr<std::vector<std::string>> GetNUpInterfaceIDs(
    thinkit::Switch& device, int num_interfaces) {
  // The test fixture pushes a new config during setup so we give the switch a
  // few minutes to converge before failing to report no valid ports.
  absl::Duration time_limit = absl::Minutes(3);
  absl::Time stop_time = absl::Now() + time_limit;
  std::vector<pins_test::P4rtPortId> port_ids;
  while (port_ids.size() < num_interfaces) {
    if (absl::Now() > stop_time) {
      return absl::FailedPreconditionError(
          absl::StrCat("Could not find ", num_interfaces, " interfaces in ",
                       absl::FormatDuration(time_limit), "."));
    }

    ASSIGN_OR_RETURN(auto gnmi_stub, device.CreateGnmiStub());
    ASSIGN_OR_RETURN(port_ids, pins_test::GetMatchingP4rtPortIds(
                                   *gnmi_stub, IsNonLagEthernetInterface));
  }

  // Get a random sample of the available ports.
  std::vector<pins_test::P4rtPortId> random_sample;
  std::sample(port_ids.begin(), port_ids.end(),
              std::back_inserter(random_sample), num_interfaces,
              absl::BitGen());

  // Convert the sample into a string.
  std::vector<std::string> result;
  for (const auto& port_id : random_sample) {
    result.push_back(absl::StrCat(port_id.GetOpenConfigEncoding()));
  }
  return result;
}

}  // namespace

TEST_P(L3AdmitTestFixture, L3PacketsAreRoutedOnlyWhenMacAddressIsInMyStation) {

  // Get SUT and control ports to test on.
  ASSERT_OK_AND_ASSIGN(
      auto sut_ports,
      GetNUpInterfaceIDs(GetParam().testbed_interface->GetMirrorTestbed().Sut(),
                         1));
  ASSERT_OK_AND_ASSIGN(
      auto control_ports,
      GetNUpInterfaceIDs(
          GetParam().testbed_interface->GetMirrorTestbed().ControlSwitch(), 1));

  // Punt all traffic arriving at the control switch, and collect them to verify
  // forwarding.
  ASSERT_OK(
      PuntAllPacketsToController(*control_switch_p4rt_session_, ir_p4info_));

  // Add an L3 route to enable forwarding.
  L3Route l3_route{
      .vrf_id = "vrf-1",
      .switch_mac = "00:00:00:00:00:01",
      .switch_ip = std::make_pair("10.0.0.1", 32),
      .peer_port = sut_ports[0],
      .peer_mac = "00:00:00:00:00:02",
      .peer_ip = "fe80::2",
      .router_interface_id = "rif-1",
      .nexthop_id = "nexthop-1",
  };
  ASSERT_OK(
      AddAndSetDefaultVrf(*sut_p4rt_session_, ir_p4info_, l3_route.vrf_id));
  ASSERT_OK(AddL3Route(*sut_p4rt_session_, ir_p4info_, l3_route));

  // Admit only 1 MAC address to the forwarding pipeline.
  ASSERT_OK(AdmitL3Route(
      *sut_p4rt_session_, ir_p4info_,
      L3AdmitOptions{
          .priority = 2070,
          .dst_mac = std ::make_pair("00:01:02:03:04:05", "FF:FF:FF:FF:FF:FF"),
      }));

  // Send 2 sets of packets to the switch. The first set of packets should not
  // match the L3 admit MAC and therefore will be dropped. The second set of
  // packet should match the L3 admit MAC and therefore get forwarded.
  const int kNumberOfTestPackets = 100;

  // Send the "bad" packets first to give them the most time.
  const std::string kBadPayload =
      "Testing L3 forwarding. This packet should be dropped.";
  ASSERT_OK(SendUdpPacket(*control_switch_p4rt_session_, ir_p4info_,
                          control_ports[0], kNumberOfTestPackets,
                          /*dst_mac=*/"00:aa:bb:cc:cc:dd", kNoVlanId,
                          /*dst_ip=*/"10.0.0.1", kBadPayload));

  // Then send the "good" packets.
  const std::string kGoodPayload =
      "Testing L3 forwarding. This packet should arrive to packet in.";
  ASSERT_OK(SendUdpPacket(*control_switch_p4rt_session_, ir_p4info_,
                          control_ports[0], kNumberOfTestPackets,
                          /*dst_mac=*/"00:01:02:03:04:05", kNoVlanId,
                          /*dst_ip=*/"10.0.0.1", kGoodPayload));

  int good_packet_count = 0;
  int bad_packet_count = 0;
  ASSERT_OK(control_switch_p4rt_session_->HandleNextNStreamMessages(
      [&](const p4::v1::StreamMessageResponse& message) {
        // Verify this is the packet we expect.
        packetlib::Packet packet_in =
            packetlib::ParsePacket(message.packet().payload());
        if (message.update_case() == p4::v1::StreamMessageResponse::kPacket &&
            absl::StrContains(packet_in.payload(), kGoodPayload)) {
          ++good_packet_count;
          return true;
        }
        if (message.update_case() == p4::v1::StreamMessageResponse::kPacket &&
            absl::StrContains(packet_in.payload(), kBadPayload)) {
          ++bad_packet_count;
          return false;
        }
        LOG(WARNING) << "Unexpected response: " << message.DebugString();
        return false;
      },
      kNumberOfTestPackets, /*timeout=*/absl::Minutes(1)));
  LOG(INFO) << "Done collecting packets.";

  EXPECT_EQ(good_packet_count, kNumberOfTestPackets);
  EXPECT_EQ(bad_packet_count, 0);
}

TEST_P(L3AdmitTestFixture, L3AdmitCanUseMaskToAllowMultipleMacAddresses) {

  // Get SUT and control ports to test on.
  ASSERT_OK_AND_ASSIGN(
      auto sut_ports,
      GetNUpInterfaceIDs(GetParam().testbed_interface->GetMirrorTestbed().Sut(),
                         1));
  ASSERT_OK_AND_ASSIGN(
      auto control_ports,
      GetNUpInterfaceIDs(
          GetParam().testbed_interface->GetMirrorTestbed().ControlSwitch(), 1));

  // Punt all traffic arriving at the control switch, and collect them to verify
  // forwarding.
  ASSERT_OK(
      PuntAllPacketsToController(*control_switch_p4rt_session_, ir_p4info_));

  // Add an L3 route to enable forwarding.
  L3Route l3_route{
      .vrf_id = "vrf-1",
      .switch_mac = "00:00:00:00:00:01",
      .switch_ip = std::make_pair("10.0.0.1", 32),
      .peer_port = sut_ports[0],
      .peer_mac = "00:00:00:00:00:02",
      .peer_ip = "fe80::2",
      .router_interface_id = "rif-1",
      .nexthop_id = "nexthop-1",
  };
  ASSERT_OK(
      AddAndSetDefaultVrf(*sut_p4rt_session_, ir_p4info_, l3_route.vrf_id));
  ASSERT_OK(AddL3Route(*sut_p4rt_session_, ir_p4info_, l3_route));

  // Admit multiple MAC addresses into L3 routing with a single L3 admit rule.
  ASSERT_OK(AdmitL3Route(
      *sut_p4rt_session_, ir_p4info_,
      L3AdmitOptions{
          .priority = 2070,
          .dst_mac = std ::make_pair("00:01:02:03:00:05", "FF:FF:FF:FF:F0:FF"),
      }));

  // Send 5 sets of packets to the switch each with a different MAC address that
  // matches the L3Admit rule's mask.
  const int kNumberOfTestPackets = 20;
  const std::string kGoodPayload =
      "Testing L3 forwarding. This packet should arrive to packet in.";
  for (int i = 0; i < 5; ++i) {
    std::string dst_mac = absl::StrFormat("00:01:02:03:%02d:05", i);
    ASSERT_OK(SendUdpPacket(*control_switch_p4rt_session_, ir_p4info_,
                            control_ports[0], kNumberOfTestPackets, dst_mac,
                            kNoVlanId, /*dst_ip=*/"10.0.0.1", kGoodPayload));
  }

  int good_packet_count = 0;
  ASSERT_OK(control_switch_p4rt_session_->HandleNextNStreamMessages(
      [&](const p4::v1::StreamMessageResponse& message) {
        // Verify this is the packet we expect.
        packetlib::Packet packet_in =
            packetlib::ParsePacket(message.packet().payload());
        if (message.update_case() == p4::v1::StreamMessageResponse::kPacket &&
            absl::StrContains(packet_in.payload(), kGoodPayload)) {
          ++good_packet_count;
          return true;
        }
        LOG(WARNING) << "Unexpected response: " << message.DebugString();
        return false;
      },
      5 * kNumberOfTestPackets, /*timeout=*/absl::Minutes(1)));
  LOG(INFO) << "Done collecting packets.";

  EXPECT_EQ(good_packet_count, 5 * kNumberOfTestPackets);
}

TEST_P(L3AdmitTestFixture, L3AdmitCanUseInPortToRestrictMacAddresses) {
  if (!pins::TableHasMatchField(ir_p4info_, "l3_admit_table", "in_port")) {
    GTEST_SKIP() << "Skipping because l3_admit table in p4info does not "
                    "support match on in_port.";
  }

  // Get SUT and control ports to test on.
  ASSERT_OK_AND_ASSIGN(
      auto sut_ports,
      GetNUpInterfaceIDs(GetParam().testbed_interface->GetMirrorTestbed().Sut(),
                         1));
  ASSERT_OK_AND_ASSIGN(
      auto control_ports,
      GetNUpInterfaceIDs(
          GetParam().testbed_interface->GetMirrorTestbed().ControlSwitch(), 2));

  // Punt all traffic arriving at the control switch, and collect them to verify
  // forwarding.
  ASSERT_OK(
      PuntAllPacketsToController(*control_switch_p4rt_session_, ir_p4info_));

  // Add an L3 route to enable forwarding.
  L3Route l3_route{
      .vrf_id = "vrf-1",
      .switch_mac = "00:00:00:00:00:01",
      .switch_ip = std::make_pair("10.0.0.1", 32),
      .peer_port = sut_ports[0],
      .peer_mac = "00:00:00:00:00:02",
      .peer_ip = "fe80::2",
      .router_interface_id = "rif-1",
      .nexthop_id = "nexthop-1",
  };
  ASSERT_OK(
      AddAndSetDefaultVrf(*sut_p4rt_session_, ir_p4info_, l3_route.vrf_id));
  ASSERT_OK(AddL3Route(*sut_p4rt_session_, ir_p4info_, l3_route));

  // Admit the MAC addresses only on port XYZ
  ASSERT_OK(AdmitL3Route(
      *sut_p4rt_session_, ir_p4info_,
      L3AdmitOptions{
          .priority = 2070,
          .dst_mac = std ::make_pair("00:01:02:03:00:05", "FF:FF:FF:FF:F0:FF"),
          .in_port = control_ports[0],
      }));

  // Send 2 sets of packets to the switch. The first set of packets should not
  // match the L3 admit port and therefore will be dropped. The second set of
  // packet should match the L3 admit port and therefore get forwarded.
  const int kNumberOfTestPackets = 100;

  // Send the "bad" packets first to give them the most time.
  const std::string kBadPayload =
      "Testing L3 forwarding. This packet should be dropped.";
  ASSERT_OK(SendUdpPacket(*control_switch_p4rt_session_, ir_p4info_,
                          control_ports[1], kNumberOfTestPackets,
                          /*dst_mac=*/"00:01:02:03:04:05", kNoVlanId,
                          /*dst_ip=*/"10.0.0.1", kBadPayload));

  // Then send the "good" packets.
  const std::string kGoodPayload =
      "Testing L3 forwarding. This packet should arrive to packet in.";
  ASSERT_OK(SendUdpPacket(*control_switch_p4rt_session_, ir_p4info_,
                          control_ports[0], kNumberOfTestPackets,
                          /*dst_mac=*/"00:01:02:03:04:05", kNoVlanId,
                          /*dst_ip=*/"10.0.0.1", kGoodPayload));

  int good_packet_count = 0;
  int bad_packet_count = 0;
  ASSERT_OK(control_switch_p4rt_session_->HandleNextNStreamMessages(
      [&](const p4::v1::StreamMessageResponse& message) {
        // Verify this is the packet we expect.
        packetlib::Packet packet_in =
            packetlib::ParsePacket(message.packet().payload());
        if (message.update_case() == p4::v1::StreamMessageResponse::kPacket &&
            absl::StrContains(packet_in.payload(), kGoodPayload)) {
          ++good_packet_count;
          return true;
        }
        if (message.update_case() == p4::v1::StreamMessageResponse::kPacket &&
            absl::StrContains(packet_in.payload(), kBadPayload)) {
          ++bad_packet_count;
          return false;
        }
        LOG(WARNING) << "Unexpected response: " << message.DebugString();
        return false;
      },
      kNumberOfTestPackets, /*timeout=*/absl::Minutes(1)));
  LOG(INFO) << "Done collecting packets.";

  EXPECT_EQ(good_packet_count, kNumberOfTestPackets);
  EXPECT_EQ(bad_packet_count, 0);
}

TEST_P(L3AdmitTestFixture, L3PacketsCanBeRoutedWithOnlyARouterInterface) {
  
  // Only run this test if set_port_and_src_mac is used, which at SAI level
  // results in RIFs that also program MyMac table - see
  // go/rif-without-mystation for details.
  if (!ir_p4info_.actions_by_name().contains("set_port_and_src_mac")) {
    GTEST_SKIP()
        << "Skipping because p4info does not support router_interfaces table "
           "entries that program l3_admit table.";
  }

  // TODO: This is a temporary workaround to mask l3 admit legacy
  // RIF test on the testbeds that do not need legacy RIF. Legacy RIFs are not
  // needed for Pod and should be removed from P4 models. Once non-legacy RIF
  // is enforced for Pod, move this test filter back to whether legacy RIF is
  // supported or not.
  if (GetParam().skip_testing_legacy_rifs) {
    GTEST_SKIP()
        << "Skipping because there is no use case to use the router_interfaces "
           "table entries that program l3_admit table.";
  }

  // Only use 1 port because for the router interface L3 admit behavior to work
  // the incomming packet needs to match the outgoing port.
  ASSERT_OK_AND_ASSIGN(
      auto sut_ports,
      GetNUpInterfaceIDs(GetParam().testbed_interface->GetMirrorTestbed().Sut(),
                         1));

  // Punt all traffic arriving at the control switch, and collect them to verify
  // forwarding.
  ASSERT_OK(
      PuntAllPacketsToController(*control_switch_p4rt_session_, ir_p4info_));

  // Add an L3 route to enable forwarding, but do not add an explicit L3Admit
  // rule.
  L3Route l3_route{
      .vrf_id = "vrf-1",
      .switch_mac = "00:00:00:00:00:01",
      .switch_ip = std::make_pair("10.0.0.1", 32),
      .peer_port = sut_ports[0],
      .peer_mac = "00:00:00:00:00:02",
      .peer_ip = "fe80::2",
      .router_interface_id = "rif-1",
      .nexthop_id = "nexthop-1",
  };
  ASSERT_OK(
      AddAndSetDefaultVrf(*sut_p4rt_session_, ir_p4info_, l3_route.vrf_id));
  ASSERT_OK(AddL3Route(*sut_p4rt_session_, ir_p4info_, l3_route));

  // Send 1 set of packets to the switch using the switch's MAC address from the
  // L3 route.
  const int kNumberOfTestPackets = 100;
  const std::string kGoodPayload =
      "Testing L3 forwarding. This packet should arrive to packet in.";
  ASSERT_OK(SendUdpPacket(*control_switch_p4rt_session_, ir_p4info_,
                          sut_ports[0], kNumberOfTestPackets,
                          /*dst_mac=*/"00:00:00:00:00:01", kNoVlanId,
                          /*dst_ip=*/"10.0.0.1", kGoodPayload));

  int good_packet_count = 0;
  ASSERT_OK(control_switch_p4rt_session_->HandleNextNStreamMessages(
      [&](const p4::v1::StreamMessageResponse& message) {
        // Verify this is the packet we expect.
        packetlib::Packet packet_in =
            packetlib::ParsePacket(message.packet().payload());
        if (message.update_case() == p4::v1::StreamMessageResponse::kPacket &&
            absl::StrContains(packet_in.payload(), kGoodPayload)) {
          ++good_packet_count;
          return true;
        }
        LOG(WARNING) << "Unexpected response: " << message.DebugString();
        return false;
      },
      kNumberOfTestPackets, /*timeout=*/absl::Minutes(1)));
  LOG(INFO) << "Done collecting packets.";

  EXPECT_EQ(good_packet_count, kNumberOfTestPackets);
}

TEST_P(L3AdmitTestFixture, L3PacketsCanBeClassifiedByDestinationMac) {

  // Only run this test if the ACL_PRE_INGRESS table supports matching on
  // DST_MAC.
  if (!TableHasMatchField(ir_p4info_, "acl_pre_ingress_table", "dst_mac")) {
    GTEST_SKIP()
        << "Skipping because ACL_PRE_INGRESS table can not match on DST_MAC.";
  }

  // Get SUT and control ports to test on.
  ASSERT_OK_AND_ASSIGN(
      auto sut_ports,
      GetNUpInterfaceIDs(GetParam().testbed_interface->GetMirrorTestbed().Sut(),
                         1));
  ASSERT_OK_AND_ASSIGN(
      auto control_ports,
      GetNUpInterfaceIDs(
          GetParam().testbed_interface->GetMirrorTestbed().ControlSwitch(), 1));

  // Punt all traffic arriving at the control switch, and collect them to verify
  // forwarding.
  ASSERT_OK(
      PuntAllPacketsToController(*control_switch_p4rt_session_, ir_p4info_));

  // This test uses 2 MAC addresses. Both will be admitted to L3 routing, but
  // only one will get assigned a VRF ID. We expect packets receiving the
  // VRF ID (i.e. good) to get routed, and the others (i.e. bad/drop) to get
  // dropped.
  std::string vrf_id = "vrf-1";
  std::string good_dst_mac = "00:00:00:00:00:03";
  std::string drop_dst_mac = "00:00:00:00:00:04";
  ASSERT_OK(AllowVrfTrafficToDstMac(*sut_p4rt_session_, ir_p4info_,
                                    good_dst_mac, vrf_id));
  ASSERT_OK(AdmitL3Route(
      *sut_p4rt_session_, ir_p4info_,
      L3AdmitOptions{
          .priority = 2070,
          .dst_mac = std ::make_pair(good_dst_mac, "FF:FF:FF:FF:FF:FF"),
      }));
  ASSERT_OK(AdmitL3Route(
      *sut_p4rt_session_, ir_p4info_,
      L3AdmitOptions{
          .priority = 2070,
          .dst_mac = std ::make_pair(drop_dst_mac, "FF:FF:FF:FF:FF:FF"),
      }));

  // Add an L3 route to enable forwarding for 10.0.0.1/32 packets.
  L3Route l3_route{
      .vrf_id = vrf_id,
      .switch_mac = "00:00:00:00:00:01",
      .switch_ip = std::make_pair("10.0.0.1", 32),
      .peer_port = sut_ports[0],
      .peer_mac = "00:00:00:00:00:02",
      .peer_ip = "fe80::2",
      .router_interface_id = "rif-1",
      .nexthop_id = "nexthop-1",
  };
  ASSERT_OK(AddL3Route(*sut_p4rt_session_, ir_p4info_, l3_route));

  // Send 2 set of packets to the switch. One using the expected destination
  // MAC (gets forwarded), and another using an unexpected destination MAC
  // (gets dropped).
  const int kNumberOfTestPackets = 100;
  const std::string kGoodPayload =
      "Testing L3 forwarding. This packet should arrive to packet in.";
  const std::string kBadPayload =
      "Testing L3 forwarding. This packet should be dropped.";

  // Send the "bad" packets first to give them the most time.
  ASSERT_OK(SendUdpPacket(*control_switch_p4rt_session_, ir_p4info_,
                          control_ports[0], kNumberOfTestPackets, drop_dst_mac,
                          kNoVlanId, /*dst_ip=*/"10.0.0.1", kBadPayload));
  ASSERT_OK(SendUdpPacket(*control_switch_p4rt_session_, ir_p4info_,
                          control_ports[0], kNumberOfTestPackets, good_dst_mac,
                          kNoVlanId, /*dst_ip=*/"10.0.0.1", kGoodPayload));

  // Wait for all the good packets to get punted back on the control switch.
  int good_packet_count = 0;
  int bad_packet_count = 0;
  ASSERT_OK(control_switch_p4rt_session_->HandleNextNStreamMessages(
      [&](const p4::v1::StreamMessageResponse& message) {
        // Verify this is the packet we expect.
        packetlib::Packet packet_in =
            packetlib::ParsePacket(message.packet().payload());
        if (message.update_case() == p4::v1::StreamMessageResponse::kPacket &&
            absl::StrContains(packet_in.payload(), kGoodPayload)) {
          ++good_packet_count;
          return true;
        }
        if (message.update_case() == p4::v1::StreamMessageResponse::kPacket &&
            absl::StrContains(packet_in.payload(), kBadPayload)) {
          ++bad_packet_count;
          return false;
        }
        LOG(WARNING) << "Unexpected response: " << message.DebugString();
        return false;
      },
      kNumberOfTestPackets, /*timeout=*/absl::Minutes(1)));
  LOG(INFO) << "Done collecting packets.";

  EXPECT_EQ(good_packet_count, kNumberOfTestPackets);
  EXPECT_EQ(bad_packet_count, 0);
}

TEST_P(L3AdmitTestFixture, VlanOverrideAdmitsAllPacketsToL3Routing) {

  // Only run this test if the ACL_PRE_INGRESS_VLAN_TABLE exists.
  if (!ir_p4info_.tables_by_name().contains("acl_pre_ingress_vlan_table")) {
    GTEST_SKIP()
        << "Skipping because ACL_PRE_INGRESS_VLAN_TABLE does not exist.";
  }

  // Get SUT and control ports to test on.
  ASSERT_OK_AND_ASSIGN(
      auto sut_ports,
      GetNUpInterfaceIDs(GetParam().testbed_interface->GetMirrorTestbed().Sut(),
                         1));
  ASSERT_OK_AND_ASSIGN(
      auto control_ports,
      GetNUpInterfaceIDs(
          GetParam().testbed_interface->GetMirrorTestbed().ControlSwitch(), 1));

  // Punt all traffic arriving at the control switch, and collect them to verify
  // forwarding.
  ASSERT_OK(
      PuntAllPacketsToController(*control_switch_p4rt_session_, ir_p4info_));

  // Add an L3 route to enable forwarding.
  L3Route l3_route{
      .vrf_id = "vrf-1",
      .switch_mac = "00:00:00:00:00:01",
      .switch_ip = std::make_pair("10.0.0.1", 32),
      .peer_port = sut_ports[0],
      .peer_mac = "00:00:00:00:00:02",
      .peer_ip = "fe80::2",
      .router_interface_id = "rif-1",
      .nexthop_id = "nexthop-1",
  };
  ASSERT_OK(
      AddAndSetDefaultVrf(*sut_p4rt_session_, ir_p4info_, l3_route.vrf_id));
  ASSERT_OK(AddL3Route(*sut_p4rt_session_, ir_p4info_, l3_route));

  // Admit only 1 MAC address to the forwarding pipeline.
  ASSERT_OK(AdmitL3Route(
      *sut_p4rt_session_, ir_p4info_,
      L3AdmitOptions{
          .priority = 2070,
          .dst_mac = std ::make_pair("00:01:02:03:04:05", "FF:FF:FF:FF:FF:FF"),
      }));

  // Force all Packet to have the default VLAN.
  pdpi::IrWriteRequest ir_set_default_vlan;
  ASSERT_OK(gutil::ReadProtoFromString(
      R"pb(
        updates {
          type: INSERT
          entity {
            table_entry {
              priority: 10
              action {
                name: "set_outer_vlan_id"
                params {
                  name: "vlan_id"
                  value { hex_str: "0xfff" }
                }
              }
            }
          }
        }
      )pb",
      &ir_set_default_vlan));
  ASSERT_OK_AND_ASSIGN(
      p4::v1::WriteRequest pi_set_default_vlan,
      pdpi::IrWriteRequestToPi(ir_p4info_, ir_set_default_vlan));
  ASSERT_OK(pdpi::SetMetadataAndSendPiWriteRequest(sut_p4rt_session_.get(),
                                                   pi_set_default_vlan));

  // Send 100 packets to the switch with an Outer VLAN that is not the default
  // PINs VLAN (i.e. 4095).
  const int kNumberOfTestPackets = 100;
  const std::string kGoodPayload =
      "Testing L3 forwarding. This packet should arrive to packet in.";
  ASSERT_OK(SendUdpPacket(*control_switch_p4rt_session_, ir_p4info_,
                          control_ports[0], kNumberOfTestPackets,
                          /*dst_mac=*/"00:01:02:03:04:05", /*vlan_id=*/"0x004",
                          /*dst_ip=*/"10.0.0.1", kGoodPayload));

  int good_packet_count = 0;
  ASSERT_OK(control_switch_p4rt_session_->HandleNextNStreamMessages(
      [&](const p4::v1::StreamMessageResponse& message) {
        if (message.update_case() != p4::v1::StreamMessageResponse::kPacket) {
          LOG(WARNING) << "Unexpected response: " << message.DebugString();
          return false;
        }
        packetlib::Packet packet_in =
            packetlib::ParsePacket(message.packet().payload());

        // If we have the correct packet (i.e. it has a good payload) we will
        // return true so that the test doesn't have to wait for the timeout.
        // However, we don't count the packet as good unless it is missing the
        // VLAN ID.
        if (absl::StrContains(packet_in.payload(), kGoodPayload)) {
          bool has_vlan_id = false;
          for (const auto& header : packet_in.headers()) {
            if (header.has_vlan_header()) {
              LOG(WARNING) << "packet_in message still has VLAN ID: "
                           << packet_in.DebugString();
              has_vlan_id = true;
            }
          }
          if (!has_vlan_id) {
            ++good_packet_count;
          }
          return true;
        }
        LOG(WARNING) << "Unexpected packet_in message: "
                     << packet_in.DebugString();
        return false;
      },
      kNumberOfTestPackets, /*timeout=*/absl::Minutes(1)));
  LOG(INFO) << "Done collecting packets.";

  EXPECT_EQ(good_packet_count, kNumberOfTestPackets);
}

TEST_P(L3AdmitTestFixture, RoutedPacketsCanMatchOnCpuPort) {

  // Only run this test if the ACL_INGRESS_QOS_TABLE exists and we can match on
  // the IN_PORT.
  if (!TableHasMatchField(ir_p4info_, "acl_ingress_qos_table", "in_port")) {
    GTEST_SKIP() << "Skipping because ACL_INGRESS_QOS_TABLE does not exist.";
  }

  // Get SUT and control ports to test on.
  ASSERT_OK_AND_ASSIGN(
      auto gnmi_stub_sut,
      GetParam().testbed_interface->GetMirrorTestbed().Sut().CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(
      auto gnmi_stub_control,
      GetParam().testbed_interface->GetMirrorTestbed().Sut().CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(std::string sut_port,
                       pins_test::GetAnyUpInterfacePortId(*gnmi_stub_sut));
  ASSERT_OK_AND_ASSIGN(std::string control_port,
                       pins_test::GetAnyUpInterfacePortId(*gnmi_stub_control));

  // Punt all traffic arriving at the control switch, and collect them to verify
  // forwarding.
  ASSERT_OK(
      PuntAllPacketsToController(*control_switch_p4rt_session_, ir_p4info_));

  // Add an L3 route to enable forwarding.
  L3Route l3_route{
      .vrf_id = "vrf-1",
      .switch_mac = "00:00:00:00:00:01",
      .switch_ip = std::make_pair("10.0.0.1", 32),
      .peer_port = sut_port,
      .peer_mac = "00:00:00:00:00:02",
      .peer_ip = "fe80::2",
      .router_interface_id = "rif-1",
      .nexthop_id = "nexthop-1",
  };
  ASSERT_OK(
      AddAndSetDefaultVrf(*sut_p4rt_session_, ir_p4info_, l3_route.vrf_id));
  ASSERT_OK(AddL3Route(*sut_p4rt_session_, ir_p4info_, l3_route));

  // Admit only 1 MAC address to the forwarding pipeline.
  ASSERT_OK(AdmitL3Route(
      *sut_p4rt_session_, ir_p4info_,
      L3AdmitOptions{
          .priority = 2070,
          .dst_mac = std ::make_pair("00:01:02:03:04:05", "FF:FF:FF:FF:FF:FF"),
      }));

  {
    // Write QoS rule that will drop any packet, and a higher priority rule that
    // will only allow ports matching on the CPU port.
    pdpi::IrWriteRequest ir_write_request;
    ASSERT_OK(gutil::ReadProtoFromString(
        R"pb(
          updates {
            type: INSERT
            entity {
              table_entry {
                table_name: "acl_ingress_qos_table"
                priority: 10
                action {
                  name: "acl_drop",
                }
              }
            }
          }
          updates {
            type: INSERT
            entity {
              table_entry {
                table_name: "acl_ingress_qos_table"
                priority: 11
                matches {
                  name: "in_port"
                  optional {
                    value {
                      str: "4294967293"  # OPENFLOW_PORT_CONTROLLER
                    }
                  }
                }
                action {
                  name: "acl_forward",
                }
              }
            }
          }
        )pb",
        &ir_write_request));
    ASSERT_OK_AND_ASSIGN(
        p4::v1::WriteRequest pi_write_request,
        pdpi::IrWriteRequestToPi(ir_p4info_, ir_write_request));
    ASSERT_OK(pdpi::SetMetadataAndSendPiWriteRequest(sut_p4rt_session_.get(),
                                                     pi_write_request));
  }

  // Send 2 sets of packets to the switch. The packets are exactly the same, but
  // the first set of packets will be sent to the SUT from the control switch
  // (i.e. they arrive on a physical port). The second set of packets will be
  // sent through the "send_to_ingress" port.
  const int kNumberOfTestPackets = 100;

  // Send the "bad" packets first to give them the most time.
  const std::string kBadPayload =
      "Testing L3 forwarding. This packet should be dropped.";
  ASSERT_OK(SendUdpPacket(*control_switch_p4rt_session_, ir_p4info_,
                          control_port, kNumberOfTestPackets,
                          /*dst_mac=*/"00:01:02:03:04:05", kNoVlanId,
                          /*dst_ip=*/"10.0.0.1", kBadPayload));

  // Then send the "good" packets.
  const std::string kGoodPayload =
      "Testing L3 forwarding. This packet should arrive to packet in.";
  ASSERT_OK(SendUdpPacket(*sut_p4rt_session_, ir_p4info_, kSendToIngress,
                          kNumberOfTestPackets, /*dst_mac=*/"00:01:02:03:04:05",
                          kNoVlanId, /*dst_ip=*/"10.0.0.1", kGoodPayload));

  int good_packet_count = 0;
  int bad_packet_count = 0;
  ASSERT_OK(control_switch_p4rt_session_->HandleNextNStreamMessages(
      [&](const p4::v1::StreamMessageResponse& message) {
        // Verify this is the packet we expect.
        packetlib::Packet packet_in =
            packetlib::ParsePacket(message.packet().payload());
        if (absl::StrContains(packet_in.payload(), kGoodPayload)) {
          ++good_packet_count;
          return true;
        }
        if (absl::StrContains(packet_in.payload(), kBadPayload)) {
          ++bad_packet_count;
          return false;
        }
        LOG(WARNING) << "Unexpected P4 Stream response: "
                     << message.DebugString();
        return false;
      },
      kNumberOfTestPackets, /*timeout=*/absl::Minutes(1)));
  LOG(INFO) << "Done collecting packets.";

  EXPECT_EQ(good_packet_count, kNumberOfTestPackets);
  EXPECT_EQ(bad_packet_count, 0);
}

}  // namespace pins
