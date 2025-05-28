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

#include "tests/forwarding/tunnel_decap_test.h"

#include <memory>
#include <optional>
#include <string>
#include <vector>

#include "absl/log/check.h"
#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "dvaas/dataplane_validation.h"
#include "dvaas/test_vector.h"
#include "dvaas/validation_result.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status.h"  // IWYU pragma: keep
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"  // IWYU pragma: keep
#include "lib/gnmi/gnmi_helper.h"
#include "net/google::protobuf/contrib/fixtures/proto-fixture-repository.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/netaddr/ipv4_address.h"
#include "p4_infra/netaddr/ipv6_address.h"
#include "p4_infra/netaddr/mac_address.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4_infra/p4_pdpi/p4_runtime_session_extras.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.pb.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"
#include "thinkit/mirror_testbed.h"

namespace pins_test {
namespace {

using ::google::protobuf::contrib::fixtures::ProtoFixtureRepository;

static const auto dst_mac =
    netaddr::MacAddress(0x00, 0xaa, 0xbb, 0xcc, 0xcc, 0xdd);
static const auto tunnel_dst_ipv6 = netaddr::Ipv6Address(
    0x11, 0x2233, 0x4455, 0x6677, 0x8899, 0xaabb, 0xccdd, 0xeeff);
static const auto tunnel_dst_ipv6_wildcard =
    netaddr::Ipv6Address(0x11, 0x2233, 0x4455, 0x6677, 0x8899, 0xaabb, 0, 0);
static const auto tunnel_src_ipv6 = netaddr::Ipv6Address(
    0x1122, 0x1122, 0x3344, 0x3344, 0x5566, 0x5566, 0x7788, 0x7788);
static const auto tunnel_src_ipv6_wildcard =
    netaddr::Ipv6Address(0x1122, 0x1122, 0x3344, 0x3344, 0x5566, 0x5566, 0, 0);
static const auto inner_dst_ipv4 = netaddr::Ipv4Address(0x10, 0, 0, 0x1);
static const auto inner_dst_ipv4_mask =
    netaddr::Ipv4Address(0xff, 0xff, 0xff, 0xff);
static const auto incorrect_dst_ipv6 = netaddr::Ipv6Address(
    0x77, 0x2233, 0x4455, 0x5577, 0x8899, 0xaabb, 0xccdd, 0xeeff);
static const auto exact_match_mask = netaddr::Ipv6Address(
    0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff);
static const auto ternary_match_mask =
    netaddr::Ipv6Address(0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0, 0);
static const auto inner_dst_ipv6 = netaddr::Ipv6Address(
    0x2001, 0xdb8, 0x3333, 0x4444, 0x5555, 0x6666, 0x7777, 0x8888);
static const auto tunnel_dst_ipv6_first64 =
    netaddr::Ipv6Address(0x11, 0x2233, 0x4455, 0x6677, 0, 0, 0, 0);
static const auto exact_match_mask_first64 =
    netaddr::Ipv6Address(0xffff, 0xffff, 0xffff, 0xffff, 0, 0, 0, 0);
constexpr absl::string_view kRedirectNexthopId = "redirect-nexthop";

// Helper function to build a Ipv6 in Ipv6 packet
dvaas::PacketTestVector Ipv6InIpv6DecapTestVector(
    const TunnelDecapTestVectorParams& packet_vector_param) {
  ProtoFixtureRepository repo;

  repo.RegisterValue("@payload", dvaas::MakeTestPacketTagFromUniqueId(
                                     1, "Testing IPv6-in-Ipv6 packets"))
      .RegisterValue("@ingress_port", packet_vector_param.in_port)
      .RegisterValue("@egress_port", packet_vector_param.out_port)
      .RegisterValue("@inner_dst_ipv6",
                     packet_vector_param.inner_dst_ipv6.ToString())
      .RegisterValue("@dst_ipv6", packet_vector_param.dst_ipv6.ToString())
      .RegisterValue("@dst_mac", packet_vector_param.dst_mac.ToString());

  dvaas::PacketTestVector test_vector =
      repo.RegisterSnippetOrDie<packetlib::Header>("@ethernet", R"pb(
            ethernet_header {
              ethernet_destination: @dst_mac,
              ethernet_source: "00:00:22:22:00:00"
              ethertype: "0x86dd"  # ipv6
            }
          )pb")
          .RegisterSnippetOrDie<packetlib::Header>("@ipv6", R"pb(
            ipv6_header {
              version: "0x6"
              dscp: "0x1b"
              ecn: "0x1"
              flow_label: "0x12345"
              # payload_length: filled in automatically.
              next_header: "0x29"  # next is ipv6
              hop_limit: 0x42
              ipv6_source: "1122:1122:3344:3344:5566:5566:7788:7788"
              ipv6_destination: @dst_ipv6
              # ipv6_destination: "11:2233:4455:6677:8899:aabb:ccdd:eeff"
            }
          )pb")
          .RegisterSnippetOrDie<packetlib::Header>("@inner_ipv6", R"pb(
            ipv6_header {
              version: "0x6"
              dscp: "0x1b"
              ecn: "0x1"
              flow_label: "0x12345"
              next_header: "0x11"  # UDP
              hop_limit: "0x42"
              ipv6_source: "2001:db8:3333:4444:5555:6666:7777:2222"
              ipv6_destination: @inner_dst_ipv6
            }
          )pb")
          .RegisterSnippetOrDie<packetlib::Header>("@udp", R"pb(
            udp_header { source_port: "0x0014" destination_port: "0x000a" }
          )pb")
          .RegisterMessage("@input_packet",
                           repo.ParseTextOrDie<packetlib::Packet>(
                               R"pb(
                                 headers: @ethernet
                                 headers: @ipv6
                                 headers: @inner_ipv6
                                 headers: @udp
                                 payload: @payload
                               )pb"))
          .RegisterMessage(
              "@output_packet", repo.ParseTextOrDie<packetlib::Packet>(R"pb(
                headers: @ethernet {
                  ethernet_header {
                    ethernet_destination: "02:02:02:02:02:02"
                    ethernet_source: "06:05:04:03:02:01"
                    ethertype: "0x86dd"
                  }
                }
                headers: @inner_ipv6 { ipv6_header { hop_limit: "0x41" } }
                headers: @udp
                payload: @payload
              )pb"))
          .ParseTextOrDie<dvaas::PacketTestVector>(R"pb(
            input {
              type: DATAPLANE
              packet { port: @ingress_port parsed: @input_packet }
            }
            acceptable_outputs {
              packets { port: @egress_port parsed: @output_packet }
            }
          )pb");

  return test_vector;
}

// Helper function to build a Ipv4 in Ipv6 packet
dvaas::PacketTestVector Ipv4InIpv6DecapTestVector(
    const TunnelDecapTestVectorParams& packet_vector_param) {
  ProtoFixtureRepository repo;

  repo.RegisterValue("@payload", dvaas::MakeTestPacketTagFromUniqueId(
                                     1, "Testing IPv4-in-Ipv6 packets"))
      .RegisterValue("@ingress_port", packet_vector_param.in_port)
      .RegisterValue("@egress_port", packet_vector_param.out_port)
      .RegisterValue("@dst_ip", packet_vector_param.inner_dst_ipv4.ToString())
      .RegisterValue("@dst_ipv6", packet_vector_param.dst_ipv6.ToString())
      .RegisterValue("@dst_mac", packet_vector_param.dst_mac.ToString())
      .RegisterValue("@ttl", "0x10")
      .RegisterValue("@decremented_ttl", "0x0f");

  dvaas::PacketTestVector test_vector =
      repo.RegisterSnippetOrDie<packetlib::Header>("@ethernet", R"pb(
            ethernet_header {
              ethernet_destination: @dst_mac,
              ethernet_source: "00:00:22:22:00:00"
              ethertype: "0x86dd"  # Udp
            }
          )pb")
          .RegisterSnippetOrDie<packetlib::Header>("@ipv6", R"pb(
            ipv6_header {
              version: "0x6"
              dscp: "0x1b"
              ecn: "0x1"
              flow_label: "0x12345"
              # payload_length: filled in automatically.
              next_header: "0x04"  # next is ipv4
              hop_limit: 0x42
              ipv6_source: "1122:1122:3344:3344:5566:5566:7788:7788"
              ipv6_destination: @dst_ipv6
            }
          )pb")
          .RegisterSnippetOrDie<packetlib::Header>("@ipv4", R"pb(
            ipv4_header {
              version: "0x4"
              dscp: "0x1b"
              ecn: "0x1"
              ihl: "0x5"
              identification: "0x0000"
              flags: "0x0"
              ttl: @ttl
              fragment_offset: "0x0000"
              # payload_length: filled in automatically.
              protocol: "0x11"
              ipv4_source: "10.0.0.8"
              ipv4_destination: @dst_ip
            }
          )pb")
          .RegisterSnippetOrDie<packetlib::Header>("@udp", R"pb(
            udp_header { source_port: "0x0014" destination_port: "0x000a" }
          )pb")
          .RegisterMessage("@input_packet",
                           repo.ParseTextOrDie<packetlib::Packet>(
                               R"pb(
                                 headers: @ethernet
                                 headers: @ipv6
                                 headers: @ipv4
                                 headers: @udp
                                 payload: @payload
                               )pb"))
          .RegisterMessage(
              "@output_packet", repo.ParseTextOrDie<packetlib::Packet>(R"pb(
                headers: @ethernet {
                  ethernet_header {
                    ethernet_destination: "02:02:02:02:02:02"
                    ethernet_source: "06:05:04:03:02:01"
                    ethertype: "0x0800"
                  }
                }
                headers: @ipv4 { ipv4_header { ttl: @decremented_ttl } }
                headers: @udp
                payload: @payload
              )pb"))
          .ParseTextOrDie<dvaas::PacketTestVector>(R"pb(
            input {
              type: DATAPLANE
              packet { port: @ingress_port parsed: @input_packet }
            }
            acceptable_outputs {
              packets { port: @egress_port parsed: @output_packet }
            }
          )pb");

  return test_vector;
}

// Helper function to build a Ipv4 in Ipv6 packet
dvaas::PacketTestVector Ipv4InIpv6NoDecapTestVector(
    const TunnelDecapTestVectorParams &packet_vector_param) {
  ProtoFixtureRepository repo;

  repo.RegisterValue("@payload", dvaas::MakeTestPacketTagFromUniqueId(
                                     1, "Testing IPv4-in-Ipv6 packets"))
      .RegisterValue("@ingress_port", packet_vector_param.in_port)
      .RegisterValue("@egress_port", packet_vector_param.out_port)
      .RegisterValue("@dst_ip", packet_vector_param.inner_dst_ipv4.ToString())
      .RegisterValue("@dst_ipv6", packet_vector_param.dst_ipv6.ToString())
      .RegisterValue("@dst_mac", packet_vector_param.dst_mac.ToString())
      .RegisterValue("@ttl", "0x10")
      .RegisterValue("@decremented_hop", "0x41");

  dvaas::PacketTestVector test_vector =
      repo.RegisterSnippetOrDie<packetlib::Header>("@ethernet", R"pb(
            ethernet_header {
              ethernet_destination: @dst_mac,
              ethernet_source: "00:00:22:22:00:00"
              ethertype: "0x86dd"  # Udp
            }
          )pb")
          .RegisterSnippetOrDie<packetlib::Header>("@ipv6", R"pb(
            ipv6_header {
              version: "0x6"
              dscp: "0x1b"
              ecn: "0x1"
              flow_label: "0x12345"
              # payload_length: filled in automatically.
              next_header: "0x04"  # next is ipv4
              hop_limit: 0x42
              ipv6_source: "1122:1122:3344:3344:5566:5566:7788:7788"
              ipv6_destination: @dst_ipv6
            }
          )pb")
          .RegisterSnippetOrDie<packetlib::Header>("@ipv4", R"pb(
            ipv4_header {
              version: "0x4"
              dscp: "0x1b"
              ecn: "0x1"
              ihl: "0x5"
              identification: "0x0000"
              flags: "0x0"
              ttl: @ttl
              fragment_offset: "0x0000"
              # payload_length: filled in automatically.
              protocol: "0x11"
              ipv4_source: "10.0.0.8"
              ipv4_destination: @dst_ip
            }
          )pb")
          .RegisterSnippetOrDie<packetlib::Header>("@udp", R"pb(
            udp_header { source_port: "0x0014" destination_port: "0x000a" }
          )pb")
          .RegisterMessage("@input_packet",
                           repo.ParseTextOrDie<packetlib::Packet>(
                               R"pb(
                                 headers: @ethernet
                                 headers: @ipv6
                                 headers: @ipv4
                                 headers: @udp
                                 payload: @payload
                               )pb"))
          .RegisterMessage(
              "@output_packet", repo.ParseTextOrDie<packetlib::Packet>(R"pb(
                headers: @ethernet {
                  ethernet_header {
                    ethernet_destination: "02:02:02:02:02:02"
                    ethernet_source: "06:05:04:03:02:01"
                    ethertype: "0x86dd"
                  }
                }
                headers: @ipv6 { ipv6_header { hop_limit: @decremented_hop } }
                # As the packet is not decapped, inner packet is not changed
                headers: @ipv4 {}
                headers: @udp
                payload: @payload
              )pb"))
          .ParseTextOrDie<dvaas::PacketTestVector>(R"pb(
            input {
              type: DATAPLANE
              packet { port: @ingress_port parsed: @input_packet }
            }
            acceptable_outputs {
              packets { port: @egress_port parsed: @output_packet }
            }
          )pb");

  return test_vector;
}

// Helper routine to install L3 route
absl::StatusOr<std::vector<p4::v1::Entity>> InstallTunnelTermTable(
    pdpi::P4RuntimeSession& switch_session, pdpi::IrP4Info& ir_p4info,
    const pins_test::TunnelMatchType tunnel_type) {
  std::vector<p4::v1::Entity> pi_entities;
  LOG(INFO) << "Installing Tunnel term table";
  sai::Ipv6TunnelTerminationParams params{
      .src_ipv6_value = tunnel_src_ipv6,
      .src_ipv6_mask = exact_match_mask,
      .dst_ipv6_value = tunnel_dst_ipv6,
      .dst_ipv6_mask = exact_match_mask,
  };

  switch (tunnel_type) {
    case pins_test::TunnelMatchType::kTernaryMatchSrcIp:
      params.src_ipv6_value = tunnel_src_ipv6_wildcard;
      params.src_ipv6_mask = ternary_match_mask;
      break;
    case pins_test::TunnelMatchType::kTernaryMatchDstIp:
      params.dst_ipv6_value = tunnel_dst_ipv6_wildcard;
      params.dst_ipv6_mask = ternary_match_mask;
      break;
    case pins_test::TunnelMatchType::kExactMatch:
      break;
  }

  sai::EntryBuilder entry_builder =
      sai::EntryBuilder().AddIpv6TunnelTerminationEntry(params);

  ASSIGN_OR_RETURN(
      pi_entities,
      entry_builder.LogPdEntries().GetDedupedPiEntities(ir_p4info));
  RETURN_IF_ERROR(pdpi::InstallPiEntities(switch_session, pi_entities));
  return pi_entities;
}

// Helper routine to install L3 admit table
absl::Status InstallL3AdmitTable(pdpi::P4RuntimeSession &switch_session) {
  LOG(INFO) << "Installing L3 admit rule";
  sai::EntryBuilder entry_builder =
      sai::EntryBuilder().AddEntryAdmittingAllPacketsToL3();

  return (entry_builder.LogPdEntries().InstallDedupedEntities(switch_session));
}

// Helper routine to install L3 route
absl::Status InstallL3Route(pdpi::P4RuntimeSession& switch_session,
                            pdpi::IrP4Info& ir_p4info, std::string given_port,
                            sai::IpVersion ip_version, bool l3_admit) {
  std::vector<p4::v1::Entity> pi_entities;
  LOG(INFO) << "Installing L3 route";
  sai::EntryBuilder entry_builder =
      sai::EntryBuilder()
          .AddVrfEntry("vrf-1")
          .AddPreIngressAclTableEntry(
              "vrf-1", sai::AclPreIngressMatchFields{.is_ipv6 = true})
          .AddDefaultRouteForwardingAllPacketsToGivenPort(given_port,
                                                          ip_version, "vrf-1");
  if (l3_admit) {
    entry_builder.AddEntryAdmittingAllPacketsToL3();
  }

  ASSIGN_OR_RETURN(
      pi_entities,
      entry_builder.LogPdEntries().GetDedupedPiEntities(ir_p4info));
  RETURN_IF_ERROR(pdpi::InstallPiEntities(switch_session, pi_entities));
  return absl::OkStatus();
}

// Helper routine to install ingress acl redirect to egress port
absl::StatusOr<std::vector<p4::v1::Entity>>
InstallIngressAclRedirectToNexthop(pdpi::P4RuntimeSession &switch_session,
                                   std::string given_port,
                                   sai::IpVersion ip_version) {
  std::vector<p4::v1::Entity> pi_entities;
  LOG(INFO) << "Installing ACL Redirect on "
            << (ip_version == sai::IpVersion::kIpv4 ? "IPv4" : "IPv6");
  sai::MirrorAndRedirectMatchFields match_fields;
  if (ip_version == sai::IpVersion::kIpv4) {
    match_fields = sai::MirrorAndRedirectMatchFields{
        .is_ipv4 = true,
        .dst_ip =
            sai::P4RuntimeTernary<netaddr::Ipv4Address>{
                .value = inner_dst_ipv4,
                .mask = inner_dst_ipv4_mask,
            },
    };
    LOG(INFO) << "Match fields dst-ip: "
              << match_fields.dst_ip->value.ToString();

  } else {
    match_fields = sai::MirrorAndRedirectMatchFields{
        .is_ipv6 = true,
        .dst_ipv6 =
            sai::P4RuntimeTernary<netaddr::Ipv6Address>{
                .value = tunnel_dst_ipv6_first64,
                .mask = exact_match_mask_first64,
            },
    };
    LOG(INFO) << "Match fields dst-ipv6: "
              << match_fields.dst_ipv6->value.ToString();
  }

  sai::EntryBuilder entry_builder =
      sai::EntryBuilder()
          .AddIngressAclEntryRedirectingToNexthop(kRedirectNexthopId,
                                                  match_fields)
          .AddNexthopRifNeighborEntries(kRedirectNexthopId, given_port);

  RETURN_IF_ERROR(
      entry_builder.LogPdEntries().InstallDedupedEntities(switch_session));
  return pi_entities;
}

TEST_P(TunnelDecapTestFixture, BasicTunnelTermDecapv4Inv6) {
  dvaas::DataplaneValidationParams dvaas_params = GetParam().dvaas_params;

  thinkit::MirrorTestbed& testbed =
      GetParam().mirror_testbed->GetMirrorTestbed();

  // Set testbed environment
  switch (GetParam().tunnel_type) {
    case pins_test::TunnelMatchType::kTernaryMatchSrcIp:
      break;
    case pins_test::TunnelMatchType::kTernaryMatchDstIp:
      break;
    case pins_test::TunnelMatchType::kExactMatch:
      break;
  }

  // Initialize the connection, clear all entities, and (for the SUT) push
  // P4Info.
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt_session,
                       pdpi::P4RuntimeSession::Create(testbed.Sut()));

  ASSERT_OK(pdpi::ClearEntities(*sut_p4rt_session));

  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info sut_ir_p4info,
                       pdpi::GetIrP4Info(*sut_p4rt_session));

  // Get control ports to test on.
  ASSERT_OK_AND_ASSIGN(
      auto gnmi_stub_control,
      GetParam().mirror_testbed->GetMirrorTestbed().Sut().CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(std::string in_port,
                       pins_test::GetAnyUpInterfacePortId(*gnmi_stub_control));
  ASSERT_OK_AND_ASSIGN(std::string out_port,
                       pins_test::GetAnyUpInterfacePortId(*gnmi_stub_control));

  // Install L3 route entry on SUT
  ASSERT_OK(InstallL3Route(*sut_p4rt_session.get(), sut_ir_p4info, out_port,
                           sai::IpVersion::kIpv4, /*l3_admit=*/true));

  // Install tunnel term table entry on SUT
  ASSERT_OK_AND_ASSIGN(
      const auto tunnel_entities,
      InstallTunnelTermTable(*sut_p4rt_session.get(), sut_ir_p4info,
                             GetParam().tunnel_type));

  LOG(INFO) << "Sending IPv4-in-IPv6 Packet from ingress:" << in_port
            << " to egress:" << out_port;
  // Send IPv4-in-IPv6 Packet and Verify positive testcase dst-ipv6 is matching
  pins_test::TunnelDecapTestVectorParams tunnel_v6_match{
      .in_port = in_port,
      .out_port = out_port,
      .dst_mac = dst_mac,
      .inner_dst_ipv4 = inner_dst_ipv4,
      .dst_ipv6 = tunnel_dst_ipv6};
  dvaas_params.packet_test_vector_override = {
      Ipv4InIpv6DecapTestVector(tunnel_v6_match)};

  ASSERT_OK_AND_ASSIGN(
      dvaas::ValidationResult validation_result,
      GetParam().dvaas->ValidateDataplane(testbed, dvaas_params));

  // Log statistics and check that things succeeded.
  validation_result.LogStatistics();
  EXPECT_OK(validation_result.HasSuccessRateOfAtLeast(1.0));

  // Send IPv4-in-IPv6 with wrong dst_ipv6 Packet and Verify
  pins_test::TunnelDecapTestVectorParams tunnel_v6_mismatch{
      .in_port = in_port,
      .out_port = out_port,
      .dst_mac = dst_mac,
      .inner_dst_ipv4 = inner_dst_ipv4,
      .dst_ipv6 = incorrect_dst_ipv6};
  dvaas::PacketTestVector test_vector =
      Ipv4InIpv6DecapTestVector(tunnel_v6_mismatch);

  for (dvaas::SwitchOutput& output :
       *test_vector.mutable_acceptable_outputs()) {
    output.clear_packet_ins();
    output.clear_packets();
  }

  dvaas_params.packet_test_vector_override = {test_vector};

  ASSERT_OK_AND_ASSIGN(
      dvaas::ValidationResult validation_result1,
      GetParam().dvaas->ValidateDataplane(testbed, dvaas_params));

  // Log statistics and check that things succeeded.
  validation_result1.LogStatistics();
  EXPECT_OK(validation_result1.HasSuccessRateOfAtLeast(1.0));
}

TEST_P(TunnelDecapTestFixture, BasicTunnelTermDecapv6Inv6) {
  dvaas::DataplaneValidationParams dvaas_params = GetParam().dvaas_params;
  thinkit::MirrorTestbed& testbed =
      GetParam().mirror_testbed->GetMirrorTestbed();

  // Set testbed environment
  switch (GetParam().tunnel_type) {
    case pins_test::TunnelMatchType::kTernaryMatchDstIp:
      break;
    case pins_test::TunnelMatchType::kTernaryMatchSrcIp:
      break;
    case pins_test::TunnelMatchType::kExactMatch:
      break;
  }

  // Initialize the connection, clear all entities, and (for the SUT) push
  // P4Info.
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt_session,
                       pdpi::P4RuntimeSession::Create(testbed.Sut()));

  ASSERT_OK(pdpi::ClearEntities(*sut_p4rt_session));

  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info sut_ir_p4info,
                       pdpi::GetIrP4Info(*sut_p4rt_session));

  // Get control ports to test on.
  ASSERT_OK_AND_ASSIGN(
      auto gnmi_stub_control,
      GetParam().mirror_testbed->GetMirrorTestbed().Sut().CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(std::string in_port,
                       pins_test::GetAnyUpInterfacePortId(*gnmi_stub_control));
  ASSERT_OK_AND_ASSIGN(std::string out_port,
                       pins_test::GetAnyUpInterfacePortId(*gnmi_stub_control));

  // Install L3 route entry on SUT
  ASSERT_OK(InstallL3Route(*sut_p4rt_session.get(), sut_ir_p4info, out_port,
                           sai::IpVersion::kIpv6, /*l3_admit=*/true));

  // Install tunnel term table entry on SUT
  ASSERT_OK_AND_ASSIGN(
      const auto tunnel_entities,
      InstallTunnelTermTable(*sut_p4rt_session.get(), sut_ir_p4info,
                             GetParam().tunnel_type));

  LOG(INFO) << "Sending IPv6-in-IPv6 Packet for packet match from in:"
            << in_port << " to out:" << out_port;
  // Send IPv6-in-IPv6 Packet and Verify positive testcase dst-ipv6 is matching
  pins_test::TunnelDecapTestVectorParams tunnel_v6_match{
      .in_port = in_port,
      .out_port = out_port,
      .dst_mac = dst_mac,
      .inner_dst_ipv6 = inner_dst_ipv6,
      .dst_ipv6 = tunnel_dst_ipv6};
  dvaas_params.packet_test_vector_override = {
      Ipv6InIpv6DecapTestVector(tunnel_v6_match)};

  ASSERT_OK_AND_ASSIGN(
      dvaas::ValidationResult validation_result,
      GetParam().dvaas->ValidateDataplane(testbed, dvaas_params));

  // Log statistics and check that things succeeded.
  validation_result.LogStatistics();
  EXPECT_OK(validation_result.HasSuccessRateOfAtLeast(1.0));
}

TEST_P(TunnelDecapTestFixture, BasicTunnelTermDecapNoAdmit) {
  if (GetParam().tunnel_type ==
          pins_test::TunnelMatchType::kTernaryMatchSrcIp ||
      GetParam().tunnel_type ==
          pins_test::TunnelMatchType::kTernaryMatchDstIp) {
    GTEST_SKIP();
  }

  dvaas::DataplaneValidationParams dvaas_params = GetParam().dvaas_params;

  thinkit::MirrorTestbed &testbed =
      GetParam().mirror_testbed->GetMirrorTestbed();

  // Set testbed environment
  // Initialize the connection, clear all entities, and (for the SUT) push
  // P4Info.
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt_session,
                       pdpi::P4RuntimeSession::Create(testbed.Sut()));

  ASSERT_OK(pdpi::ClearEntities(*sut_p4rt_session));

  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info sut_ir_p4info,
                       pdpi::GetIrP4Info(*sut_p4rt_session));

  // Get control ports to test on.
  ASSERT_OK_AND_ASSIGN(
      auto gnmi_stub_control,
      GetParam().mirror_testbed->GetMirrorTestbed().Sut().CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(std::string in_port,
                       pins_test::GetAnyUpInterfacePortId(*gnmi_stub_control));
  ASSERT_OK_AND_ASSIGN(std::string out_port,
                       pins_test::GetAnyUpInterfacePortId(*gnmi_stub_control));

  // Install L3 route entry on SUT
  ASSERT_OK(InstallL3Route(*sut_p4rt_session.get(), sut_ir_p4info, out_port,
                           sai::IpVersion::kIpv4, /*l3_admit=*/false));

  // Install tunnel term table entry on SUT
  ASSERT_OK_AND_ASSIGN(const auto tunnel_entities,
                       InstallTunnelTermTable(*sut_p4rt_session.get(),
                                              sut_ir_p4info,
                                              GetParam().tunnel_type));

  LOG(INFO) << "Sending IPv4-in-IPv6 Packet from ingress:" << in_port
            << " to egress:" << out_port;
  // Send IPv4-in-IPv6 Packet and verify that packet is getting
  // dropped as l3-admit is not configured
  pins_test::TunnelDecapTestVectorParams tunnel_v6_match{
      .in_port = in_port,
      .out_port = out_port,
      .dst_mac = dst_mac,
      .inner_dst_ipv4 = inner_dst_ipv4,
      .dst_ipv6 = tunnel_dst_ipv6,
  };
  dvaas::PacketTestVector test_vector =
      Ipv4InIpv6DecapTestVector(tunnel_v6_match);

  for (dvaas::SwitchOutput &output :
       *test_vector.mutable_acceptable_outputs()) {
    output.clear_packet_ins();
    output.clear_packets();
  }

  dvaas_params.packet_test_vector_override = {test_vector};

  ASSERT_OK_AND_ASSIGN(
      dvaas::ValidationResult validation_result1,
      GetParam().dvaas->ValidateDataplane(testbed, dvaas_params));

  // Log statistics and check that things succeeded.
  validation_result1.LogStatistics();
  EXPECT_OK(validation_result1.HasSuccessRateOfAtLeast(1.0));
}

TEST_P(TunnelDecapTestFixture, NoAdmitTableAclRedirectTunnelTermNoDecapForV4) {
  if (GetParam().tunnel_type != pins_test::TunnelMatchType::kExactMatch) {
    GTEST_SKIP();
  }

  dvaas::DataplaneValidationParams dvaas_params = GetParam().dvaas_params;

  thinkit::MirrorTestbed &testbed =
      GetParam().mirror_testbed->GetMirrorTestbed();

  // Set testbed environment

  // Initialize the connection, clear all entities, and (for the SUT) push
  // P4Info.
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt_session,
                       pdpi::P4RuntimeSession::Create(testbed.Sut()));

  ASSERT_OK(pdpi::ClearEntities(*sut_p4rt_session));

  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info sut_ir_p4info,
                       pdpi::GetIrP4Info(*sut_p4rt_session));

  // Get control ports to test on.
  ASSERT_OK_AND_ASSIGN(
      auto gnmi_stub_control,
      GetParam().mirror_testbed->GetMirrorTestbed().Sut().CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(std::string in_port,
                       pins_test::GetAnyUpInterfacePortId(*gnmi_stub_control));
  ASSERT_OK_AND_ASSIGN(std::string out_port,
                       pins_test::GetAnyUpInterfacePortId(*gnmi_stub_control));

  // Install Ingress ACL redirect to nexthop entry on SUT
  ASSERT_OK(InstallIngressAclRedirectToNexthop(
      *sut_p4rt_session.get(), out_port, sai::IpVersion::kIpv4));

  // Install tunnel term table entry on SUT
  ASSERT_OK_AND_ASSIGN(const auto tunnel_entities,
                       InstallTunnelTermTable(*sut_p4rt_session.get(),
                                              sut_ir_p4info,
                                              GetParam().tunnel_type));

  LOG(INFO) << "Sending IPv4-in-IPv6 Packet from ingress:" << in_port
            << " to egress:" << out_port;
  // Send IPv4-in-IPv6 Packet and Verify positive testcase dst-ipv6 is matching
  pins_test::TunnelDecapTestVectorParams tunnel_v6_match{
      .in_port = in_port,
      .out_port = out_port,
      .dst_mac = dst_mac,
      .inner_dst_ipv4 = inner_dst_ipv4,
      .dst_ipv6 = tunnel_dst_ipv6};

  dvaas_params.packet_test_vector_override = {
      Ipv4InIpv6NoDecapTestVector(tunnel_v6_match)};

  ASSERT_OK_AND_ASSIGN(
      dvaas::ValidationResult validation_result,
      GetParam().dvaas->ValidateDataplane(testbed, dvaas_params));

  // Log statistics and check that things succeeded.
  validation_result.LogStatistics();
  EXPECT_OK(validation_result.HasSuccessRateOfAtLeast(1.0));
}

TEST_P(TunnelDecapTestFixture, AdmitTableAclRedirectTunnelTermDecapForV4) {
  if (GetParam().tunnel_type != pins_test::TunnelMatchType::kExactMatch) {
    GTEST_SKIP();
  }

  dvaas::DataplaneValidationParams dvaas_params = GetParam().dvaas_params;

  thinkit::MirrorTestbed &testbed =
      GetParam().mirror_testbed->GetMirrorTestbed();

  // Set testbed environment

  // Initialize the connection, clear all entities, and (for the SUT) get
  // P4Info.
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt_session,
                       pdpi::P4RuntimeSession::Create(testbed.Sut()));

  ASSERT_OK(pdpi::ClearEntities(*sut_p4rt_session));

  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info sut_ir_p4info,
                       pdpi::GetIrP4Info(*sut_p4rt_session));

  // Get control ports to test on.
  ASSERT_OK_AND_ASSIGN(
      auto gnmi_stub_control,
      GetParam().mirror_testbed->GetMirrorTestbed().Sut().CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(std::string in_port,
                       pins_test::GetAnyUpInterfacePortId(*gnmi_stub_control));
  ASSERT_OK_AND_ASSIGN(std::string out_port,
                       pins_test::GetAnyUpInterfacePortId(*gnmi_stub_control));

  // Install L3 admit table  on SUT
  ASSERT_OK(InstallL3AdmitTable(*sut_p4rt_session.get()));

  // Install Ingress ACL redirect to nexthop entry on SUT
  ASSERT_OK(InstallIngressAclRedirectToNexthop(
      *sut_p4rt_session.get(), out_port, sai::IpVersion::kIpv4));

  // Install tunnel term table entry on SUT
  ASSERT_OK_AND_ASSIGN(const auto tunnel_entities,
                       InstallTunnelTermTable(*sut_p4rt_session.get(),
                                              sut_ir_p4info,
                                              GetParam().tunnel_type));

  LOG(INFO) << "Sending IPv4-in-IPv6 Packet from ingress:" << in_port
            << " to egress:" << out_port;
  // Send IPv4-in-IPv6 Packet and Verify positive testcase dst-ipv6 is matching
  pins_test::TunnelDecapTestVectorParams tunnel_v6_match{
      .in_port = in_port,
      .out_port = out_port,
      .dst_mac = dst_mac,
      .inner_dst_ipv4 = inner_dst_ipv4,
      .dst_ipv6 = tunnel_dst_ipv6};

  dvaas_params.packet_test_vector_override = {
      Ipv4InIpv6DecapTestVector(tunnel_v6_match)};

  ASSERT_OK_AND_ASSIGN(
      dvaas::ValidationResult validation_result,
      GetParam().dvaas->ValidateDataplane(testbed, dvaas_params));

  // Log statistics and check that things succeeded.
  validation_result.LogStatistics();
  EXPECT_OK(validation_result.HasSuccessRateOfAtLeast(1.0));
}

}  // namespace
}  // namespace pins_test
