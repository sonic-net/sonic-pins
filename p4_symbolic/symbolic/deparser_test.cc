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

#include "p4_symbolic/symbolic/deparser.h"

#include <memory>
#include <string>
#include <vector>

#include "absl/log/log.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_symbolic/symbolic/context.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/symbolic/util.h"
#include "p4_symbolic/test_util.h"
#include "z3++.h"

namespace p4_symbolic {
namespace {

using ::p4_symbolic::symbolic::util::GetHeaderValidityFieldName;

class IPv4RoutingBasicTest : public testing::Test {
 public:
  void SetUp() override {
    constexpr absl::string_view bmv2_json_path =
        "p4_symbolic/testdata/ipv4-routing/"
        "basic.config.json";
    constexpr absl::string_view p4info_path =
        "p4_symbolic/testdata/ipv4-routing/"
        "basic.p4info.pb.txt";
    constexpr absl::string_view entries_path =
        "p4_symbolic/testdata/ipv4-routing/"
        "entries.pb.txt";
    ASSERT_OK_AND_ASSIGN(
        p4::v1::ForwardingPipelineConfig config,
        ParseToForwardingPipelineConfig(bmv2_json_path, p4info_path));
    ASSERT_OK_AND_ASSIGN(std::vector<p4::v1::Entity> entities,
                         GetPiEntitiesFromPiUpdatesProtoTextFile(entries_path));
    ASSERT_OK_AND_ASSIGN(state_, symbolic::EvaluateP4Program(config, entities));
  }

 protected:
  std::unique_ptr<symbolic::SolverState> state_;
};

TEST_F(IPv4RoutingBasicTest, DeparseIngressAndEgressHeadersWithoutConstraints) {
  ASSERT_EQ(state_->solver->check(), z3::check_result::sat);
  auto model = state_->solver->get_model();
  EXPECT_OK(DeparseIngressPacket(*state_, model).status());
  EXPECT_OK(DeparseEgressPacket(*state_, model).status());
}

TEST_F(IPv4RoutingBasicTest, DeparseIngressHeaders1) {
  // Add constraints.
  {
    z3::context &z3_context = *state_->context.z3_context;
    ASSERT_OK_AND_ASSIGN(
        z3::expr eth_dst_addr,
        state_->context.egress_headers.Get("ethernet.dstAddr"));
    state_->solver->add(eth_dst_addr == z3_context.bv_val(0, 48));
    state_->solver->add(state_->context.egress_port == z3_context.bv_val(1, 9));

    ASSERT_OK_AND_ASSIGN(
        z3::expr ipv4_valid,
        state_->context.ingress_headers.Get(
            symbolic::util::GetHeaderValidityFieldName("ipv4")));
    state_->solver->add(ipv4_valid);
  }

  // Solve and deparse.
  ASSERT_EQ(state_->solver->check(), z3::check_result::sat);
  auto model = state_->solver->get_model();
  ASSERT_OK_AND_ASSIGN(std::string raw_packet,
                       DeparseIngressPacket(*state_, model));

  // Check that we got an IPv4 packet with destination address 10.10.0.0.
  packetlib::Packet packet = packetlib::ParsePacket(raw_packet);
  LOG(INFO) << "Z3-generated packet = " << packet.DebugString();
  ASSERT_GE(packet.headers_size(), 2);
  EXPECT_TRUE(packet.headers(0).has_ethernet_header());
  EXPECT_TRUE(packet.headers(1).has_ipv4_header());
  EXPECT_EQ(packet.headers(1).ipv4_header().ipv4_destination(), "10.10.0.0");
}

TEST_F(IPv4RoutingBasicTest, DeparseIngressHeaders2) {
  // Add constraints.
  {
    z3::context &z3_context = *state_->context.z3_context;
    ASSERT_OK_AND_ASSIGN(
        z3::expr eth_dst_addr,
        state_->context.egress_headers.Get("ethernet.dstAddr"));
    state_->solver->add(eth_dst_addr ==
                        z3_context.bv_val((22UL << 40) + 22, 48));
    state_->solver->add(state_->context.egress_port == z3_context.bv_val(1, 9));

    ASSERT_OK_AND_ASSIGN(
        z3::expr ipv4_valid,
        state_->context.ingress_headers.Get(
            symbolic::util::GetHeaderValidityFieldName("ipv4")));
    state_->solver->add(ipv4_valid);
  }

  // Solve and deparse.
  ASSERT_EQ(state_->solver->check(), z3::check_result::sat);
  auto model = state_->solver->get_model();
  ASSERT_OK_AND_ASSIGN(std::string raw_packet,
                       DeparseIngressPacket(*state_, model));

  // Check that we got an IPv4 packet with destination within 20.20.0.0/16.
  packetlib::Packet packet = packetlib::ParsePacket(raw_packet);
  LOG(INFO) << "Z3-generated packet = " << packet.DebugString();
  ASSERT_GE(packet.headers_size(), 2);
  EXPECT_TRUE(packet.headers(0).has_ethernet_header());
  EXPECT_TRUE(packet.headers(1).has_ipv4_header());
  EXPECT_TRUE(absl::StartsWith(
      packet.headers(1).ipv4_header().ipv4_destination(), "20.20."));
}

TEST_F(IPv4RoutingBasicTest, DeparseEgressHeaders) {
  // Add constraints.
  {
    z3::context &z3_context = *state_->context.z3_context;
    ASSERT_OK_AND_ASSIGN(z3::expr ipv4_dst_addr,
                         state_->context.ingress_headers.Get("ipv4.dstAddr"));
    state_->solver->add(ipv4_dst_addr ==
                        z3_context.bv_val((10UL << 24) + 1, 32));

    ASSERT_OK_AND_ASSIGN(
        z3::expr ipv4_valid,
        state_->context.ingress_headers.Get(
            symbolic::util::GetHeaderValidityFieldName("ipv4")));
    state_->solver->add(ipv4_valid);
  }

  // Solve and deparse.
  ASSERT_EQ(state_->solver->check(), z3::check_result::sat);
  auto model = state_->solver->get_model();
  ASSERT_OK_AND_ASSIGN(std::string raw_packet,
                       DeparseEgressPacket(*state_, model));

  // Check that we got an IPv4 packet with destination MAC 00:00:00:00:00:0a.
  packetlib::Packet packet = packetlib::ParsePacket(raw_packet);
  LOG(INFO) << "Z3-generated packet = " << packet.DebugString();
  ASSERT_GE(packet.headers_size(), 2);
  EXPECT_TRUE(packet.headers(0).has_ethernet_header());
  EXPECT_TRUE(packet.headers(1).has_ipv4_header());
  EXPECT_EQ(packet.headers(0).ethernet_header().ethernet_destination(),
            "00:00:00:00:00:0a");
  EXPECT_EQ(packet.headers(1).ipv4_header().ipv4_destination(), "10.0.0.1");
}

class SaiDeparserTest : public testing::Test {
 public:
  void SetUp() override {
    constexpr absl::string_view bmv2_json_path =
        "p4_symbolic/testdata/parser/"
        "sai_parser.config.json";
    constexpr absl::string_view p4info_path =
        "p4_symbolic/testdata/parser/"
        "sai_parser.p4info.pb.txt";
    ASSERT_OK_AND_ASSIGN(
        p4::v1::ForwardingPipelineConfig config,
        ParseToForwardingPipelineConfig(bmv2_json_path, p4info_path));
    ASSERT_OK_AND_ASSIGN(state_,
                         symbolic::EvaluateP4Program(config, /*entries=*/{}));
  }

 protected:
  std::unique_ptr<symbolic::SolverState> state_;
};

TEST_F(SaiDeparserTest, DeparseIngressAndEgressHeadersWithoutConstraints) {
  ASSERT_EQ(state_->solver->check(), z3::check_result::sat);
  auto model = state_->solver->get_model();
  EXPECT_OK(DeparseIngressPacket(*state_, model).status());
  EXPECT_OK(DeparseEgressPacket(*state_, model).status());
}

TEST_F(SaiDeparserTest, VlanPacketParserIntegrationTest) {
  // Add VLAN constraint.
  {
    ASSERT_OK_AND_ASSIGN(z3::expr vlan_valid,
                         state_->context.ingress_headers.Get(
                             GetHeaderValidityFieldName("vlan")));
    state_->solver->add(vlan_valid);
  }

  // Solve and deparse.
  ASSERT_EQ(state_->solver->check(), z3::check_result::sat);
  auto model = state_->solver->get_model();
  ASSERT_OK_AND_ASSIGN(std::string raw_packet,
                       DeparseIngressPacket(*state_, model));

  // Check we indeed got a VLAN packet.
  packetlib::Packet packet = packetlib::ParsePacket(raw_packet);
  LOG(INFO) << "Z3-generated packet = " << packet.DebugString();
  ASSERT_GE(packet.headers_size(), 2);
  EXPECT_TRUE(packet.headers(0).has_ethernet_header());
  EXPECT_TRUE(packet.headers(1).has_vlan_header());
}

TEST_F(SaiDeparserTest, Ipv4UdpPacketParserIntegrationTest) {
  // Add IPv4 + UDP (+ no VLAN) constraint.
  {
    ASSERT_OK_AND_ASSIGN(z3::expr ipv4_valid,
                         state_->context.ingress_headers.Get(
                             GetHeaderValidityFieldName("ipv4")));
    ASSERT_OK_AND_ASSIGN(
        z3::expr udp_valid,
        state_->context.ingress_headers.Get(GetHeaderValidityFieldName("udp")));
    ASSERT_OK_AND_ASSIGN(z3::expr vlan_valid,
                         state_->context.ingress_headers.Get(
                             GetHeaderValidityFieldName("vlan")));
    state_->solver->add(ipv4_valid);
    state_->solver->add(udp_valid);
    state_->solver->add(!vlan_valid);
  }

  // Solve and deparse.
  ASSERT_EQ(state_->solver->check(), z3::check_result::sat);
  auto model = state_->solver->get_model();
  ASSERT_OK_AND_ASSIGN(std::string raw_packet,
                       DeparseIngressPacket(*state_, model));

  // Check we indeed got an IPv4 UDP packet.
  packetlib::Packet packet = packetlib::ParsePacket(raw_packet);
  LOG(INFO) << "Z3-generated packet = " << packet.DebugString();
  ASSERT_GE(packet.headers_size(), 3);
  EXPECT_TRUE(packet.headers(0).has_ethernet_header());
  EXPECT_TRUE(packet.headers(1).has_ipv4_header());
  EXPECT_TRUE(packet.headers(2).has_udp_header());
  EXPECT_THAT(packet.payload(), testing::IsEmpty());
}

TEST_F(SaiDeparserTest, Ipv6TcpPacketParserIntegrationTest) {
  // Add IPv6 + TCP (+ no VLAN) constraint.
  {
    ASSERT_OK_AND_ASSIGN(z3::expr ipv4_valid,
                         state_->context.ingress_headers.Get(
                             GetHeaderValidityFieldName("ipv4")));
    ASSERT_OK_AND_ASSIGN(
        z3::expr tcp_valid,
        state_->context.ingress_headers.Get(GetHeaderValidityFieldName("tcp")));
    ASSERT_OK_AND_ASSIGN(z3::expr vlan_valid,
                         state_->context.ingress_headers.Get(
                             GetHeaderValidityFieldName("vlan")));
    state_->solver->add(!ipv4_valid);
    state_->solver->add(tcp_valid);
    // The only way to have a TCP packet that is not an IPv4 packet is to have
    // an IPv6 packet.
    state_->solver->add(!vlan_valid);
  }

  // Solve and deparse.
  ASSERT_EQ(state_->solver->check(), z3::check_result::sat);
  auto model = state_->solver->get_model();
  ASSERT_OK_AND_ASSIGN(std::string raw_packet,
                       DeparseIngressPacket(*state_, model));

  // Check we indeed got an IPv6 TCP packet.
  packetlib::Packet packet = packetlib::ParsePacket(raw_packet);
  LOG(INFO) << "Z3-generated packet = " << packet.DebugString();
  ASSERT_GE(packet.headers_size(), 3);
  EXPECT_TRUE(packet.headers(0).has_ethernet_header());
  EXPECT_TRUE(packet.headers(1).has_ipv6_header());
  EXPECT_TRUE(packet.headers(2).has_tcp_header());
  EXPECT_THAT(packet.payload(), testing::IsEmpty());
}

TEST_F(SaiDeparserTest, ArpPacketParserIntegrationTest) {
  // Add ARP (+ no VLAN) constraint.
  {
    ASSERT_OK_AND_ASSIGN(
        z3::expr arp_valid,
        state_->context.ingress_headers.Get(GetHeaderValidityFieldName("arp")));
    ASSERT_OK_AND_ASSIGN(z3::expr vlan_valid,
                         state_->context.ingress_headers.Get(
                             GetHeaderValidityFieldName("vlan")));
    state_->solver->add(arp_valid);
    state_->solver->add(!vlan_valid);
  }

  // Solve and deparse.
  ASSERT_EQ(state_->solver->check(), z3::check_result::sat);
  auto model = state_->solver->get_model();
  ASSERT_OK_AND_ASSIGN(std::string raw_packet,
                       DeparseIngressPacket(*state_, model));

  // Check we indeed got an ARP packet.
  packetlib::Packet packet = packetlib::ParsePacket(raw_packet);
  LOG(INFO) << "Z3-generated packet = " << packet.DebugString();
  ASSERT_GE(packet.headers_size(), 2);
  EXPECT_TRUE(packet.headers(0).has_ethernet_header());
  EXPECT_TRUE(packet.headers(1).has_arp_header());
  EXPECT_THAT(packet.payload(), testing::IsEmpty());
}

TEST_F(SaiDeparserTest, IcmpPacketParserIntegrationTest) {
  // Add ICMP (+ no VLAN) constraint.
  {
    ASSERT_OK_AND_ASSIGN(z3::expr icmp_valid,
                         state_->context.ingress_headers.Get(
                             GetHeaderValidityFieldName("icmp")));
    ASSERT_OK_AND_ASSIGN(z3::expr vlan_valid,
                         state_->context.ingress_headers.Get(
                             GetHeaderValidityFieldName("vlan")));
    state_->solver->add(icmp_valid);
    state_->solver->add(!vlan_valid);
  }

  // Solve and deparse.
  ASSERT_EQ(state_->solver->check(), z3::check_result::sat);
  auto model = state_->solver->get_model();
  ASSERT_OK_AND_ASSIGN(std::string raw_packet,
                       DeparseIngressPacket(*state_, model));

  // Check we indeed got an ARP packet.
  packetlib::Packet packet = packetlib::ParsePacket(raw_packet);
  LOG(INFO) << "Z3-generated packet = " << packet.DebugString();
  ASSERT_GE(packet.headers_size(), 3);
  EXPECT_TRUE(packet.headers(0).has_ethernet_header());
  EXPECT_TRUE(packet.headers(1).has_ipv4_header() ||
              packet.headers(1).has_ipv6_header());
  EXPECT_TRUE(packet.headers(2).has_icmp_header());
  EXPECT_THAT(packet.payload(), testing::IsEmpty());
}

TEST_F(SaiDeparserTest, PacketInHeaderIsNeverParsedIntegrationTest) {
  // Add packet_in constraint.
  {
    ASSERT_OK_AND_ASSIGN(z3::expr packet_in_valid,
                         state_->context.ingress_headers.Get(
                             GetHeaderValidityFieldName("packet_in_header")));
    state_->solver->add(packet_in_valid);
  }

  // Should be unsatisfiable, because we never parse a packet-in header.
  EXPECT_EQ(state_->solver->check(), z3::check_result::unsat);
}

}  // namespace
}  // namespace p4_symbolic
