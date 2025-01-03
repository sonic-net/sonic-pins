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

#include "p4_symbolic/deparser.h"

#include <memory>

#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/io.h"
#include "gutil/proto.h"
#include "gutil/status_matchers.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_symbolic/parser.h"
#include "p4_symbolic/sai/fields.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/z3_util.h"
#include "z3++.h"

namespace p4_symbolic {
namespace {

class SaiDeparserTest : public testing::Test {
 public:
  void SetUp() override {
    constexpr absl::string_view p4info_path =
        "p4_symbolic/testdata/parser/"
        "sai_parser.p4info.pb.txt";
    constexpr absl::string_view p4_config_path =
        "p4_symbolic/testdata/parser/"
        "sai_parser.config.json";
    p4::v1::ForwardingPipelineConfig config;
    ASSERT_OK(gutil::ReadProtoFromFile(p4info_path, config.mutable_p4info()));
    ASSERT_OK_AND_ASSIGN(*config.mutable_p4_device_config(),
                         gutil::ReadFile(std::string(p4_config_path)));

    Z3Context(/*renew=*/true);
    ASSERT_OK_AND_ASSIGN(ir::Dataplane dataplane,
                         ParseToIr(config, /*table_entries=*/{}));
    ASSERT_OK_AND_ASSIGN(state_, symbolic::EvaluateP4Program(dataplane));
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
    ASSERT_OK_AND_ASSIGN(SaiFields fields,
                         GetSaiFields(state_->context.ingress_headers));
    state_->solver->add(fields.headers.vlan->valid);
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
    ASSERT_OK_AND_ASSIGN(SaiFields fields,
                         GetSaiFields(state_->context.ingress_headers));
    state_->solver->add(fields.headers.ipv4.valid);
    state_->solver->add(fields.headers.udp.valid);
    state_->solver->add(!fields.headers.vlan->valid);
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
    ASSERT_OK_AND_ASSIGN(SaiFields fields,
                         GetSaiFields(state_->context.ingress_headers));
    state_->solver->add(!fields.headers.ipv4.valid);
    state_->solver->add(fields.headers.tcp.valid);
    // The only way to have a TCP packet that is not an IPv4 packet is to have
    // an IPv6 packet.
    state_->solver->add(!fields.headers.vlan->valid);
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
    ASSERT_OK_AND_ASSIGN(SaiFields fields,
                         GetSaiFields(state_->context.ingress_headers));
    state_->solver->add(fields.headers.arp.valid);
    state_->solver->add(!fields.headers.vlan->valid);
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
    ASSERT_OK_AND_ASSIGN(SaiFields fields,
                         GetSaiFields(state_->context.ingress_headers));
    state_->solver->add(fields.headers.icmp.valid);
    state_->solver->add(!fields.headers.vlan->valid);
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
    ASSERT_OK_AND_ASSIGN(SaiFields fields,
                         GetSaiFields(state_->context.ingress_headers));
    EXPECT_TRUE(fields.headers.packet_in.has_value());
    state_->solver->add(fields.headers.packet_in->valid);
  }

  // Should be unsatisfiable, because we never parse a packet-in header.
  EXPECT_EQ(state_->solver->check(), z3::check_result::unsat);
}

}  // namespace
}  // namespace p4_symbolic
