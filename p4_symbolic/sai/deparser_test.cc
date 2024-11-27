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
#include "p4_symbolic/sai/deparser.h"

#include <memory>
#include <string>
#include <type_traits>
#include <vector>

#include "absl/status/statusor.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_pdpi/string_encodings/bit_string.h"
#include "p4_symbolic/sai/fields.h"
#include "p4_symbolic/sai/parser.h"
#include "p4_symbolic/sai/sai.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_nonstandard_platforms.h"
#include "z3++.h"

namespace p4_symbolic {
namespace {

using ::testing::IsEmpty;

class SaiDeparserTest : public testing::TestWithParam<sai::Instantiation> {
 public:
  void SetUp() override {
    testing::TestWithParam<sai::Instantiation>::SetUp();
    const auto config = sai::GetNonstandardForwardingPipelineConfig(
        /*instantiation=*/GetParam(), sai::NonstandardPlatform::kP4Symbolic);
    ASSERT_OK_AND_ASSIGN(
        state_, EvaluateSaiPipeline(config, /*entries=*/{}, /*ports=*/{}));
  }

 protected:
  std::unique_ptr<symbolic::SolverState> state_;
};

TEST_P(SaiDeparserTest, DeparseIngressAndEgressHeadersWithoutConstraints) {
  ASSERT_EQ(state_->solver->check(), z3::check_result::sat);
  auto model = state_->solver->get_model();
  for (auto& packet :
       {state_->context.ingress_headers, state_->context.egress_headers}) {
    EXPECT_OK(SaiDeparser(packet, model).status());
  }
}

TEST_P(SaiDeparserTest, Ipv4UdpPacketParserIntegrationTest) {
  // Add parse constraints.
  {
    ASSERT_OK_AND_ASSIGN(auto parse_constraints,
                         EvaluateSaiParser(state_->context.ingress_headers));
    for (auto& constraint : parse_constraints) state_->solver->add(constraint);
  }

  // Add IPv4 + UDP constraint.
  {
    ASSERT_OK_AND_ASSIGN(SaiFields fields,
                         GetSaiFields(state_->context.ingress_headers));
    state_->solver->add(fields.headers.ipv4.valid);
    state_->solver->add(fields.headers.udp.valid);
  }

  // Solve and deparse.
  ASSERT_EQ(state_->solver->check(), z3::check_result::sat);
  auto model = state_->solver->get_model();
  ASSERT_OK_AND_ASSIGN(std::string raw_packet,
                       SaiDeparser(state_->context.ingress_headers, model));

  // Check we indeed got an IPv4 UDP packet.
  packetlib::Packet packet = packetlib::ParsePacket(raw_packet);
  LOG(INFO) << "Z3-generated packet = " << packet.DebugString();
  ASSERT_GE(packet.headers_size(), 3);
  ASSERT_TRUE(packet.headers(0).has_ethernet_header());
  ASSERT_TRUE(packet.headers(1).has_ipv4_header());
  ASSERT_TRUE(packet.headers(2).has_udp_header());
  ASSERT_THAT(packet.payload(), IsEmpty());
}

TEST_P(SaiDeparserTest, Ipv6TcpPacketParserIntegrationTest) {
  // Add parse constraints.
  {
    ASSERT_OK_AND_ASSIGN(auto parse_constraints,
                         EvaluateSaiParser(state_->context.ingress_headers));
    for (auto& constraint : parse_constraints) state_->solver->add(constraint);
  }

  // Add IPv6 + UDP constraint.
  {
    ASSERT_OK_AND_ASSIGN(SaiFields fields,
                         GetSaiFields(state_->context.ingress_headers));
    state_->solver->add(!fields.headers.ipv4.valid);
    state_->solver->add(fields.headers.tcp.valid);
    // The only way to have an TCP packet that is not an IPv4 packet is to have
    // an IPv6 packet.
  }

  // Solve and deparse.
  ASSERT_EQ(state_->solver->check(), z3::check_result::sat);
  auto model = state_->solver->get_model();
  ASSERT_OK_AND_ASSIGN(std::string raw_packet,
                       SaiDeparser(state_->context.ingress_headers, model));

  // Check we indeed got an IPv6 TCP packet.
  packetlib::Packet packet = packetlib::ParsePacket(raw_packet);
  LOG(INFO) << "Z3-generated packet = " << packet.DebugString();
  ASSERT_GE(packet.headers_size(), 3);
  ASSERT_TRUE(packet.headers(0).has_ethernet_header());
  ASSERT_TRUE(packet.headers(1).has_ipv6_header());
  ASSERT_TRUE(packet.headers(2).has_tcp_header());
  ASSERT_THAT(packet.payload(), IsEmpty());
}

TEST_P(SaiDeparserTest, ArpPacketParserIntegrationTest) {
  // Add parse constraints.
  {
    ASSERT_OK_AND_ASSIGN(auto parse_constraints,
                         EvaluateSaiParser(state_->context.ingress_headers));
    for (auto& constraint : parse_constraints) state_->solver->add(constraint);
  }

  // Add ARP constraint.
  {
    ASSERT_OK_AND_ASSIGN(SaiFields fields,
                         GetSaiFields(state_->context.ingress_headers));
    state_->solver->add(fields.headers.arp.valid);
  }

  // Solve and deparse.
  ASSERT_EQ(state_->solver->check(), z3::check_result::sat);
  auto model = state_->solver->get_model();
  ASSERT_OK_AND_ASSIGN(std::string raw_packet,
                       SaiDeparser(state_->context.ingress_headers, model));

  // Check we indeed got an ARP packet.
  packetlib::Packet packet = packetlib::ParsePacket(raw_packet);
  LOG(INFO) << "Z3-generated packet = " << packet.DebugString();
  ASSERT_GE(packet.headers_size(), 2);
  ASSERT_TRUE(packet.headers(0).has_ethernet_header());
  ASSERT_TRUE(packet.headers(1).has_arp_header());
  ASSERT_THAT(packet.payload(), IsEmpty());
}

TEST_P(SaiDeparserTest, IcmpPacketParserIntegrationTest) {
  // Add parse constraints.
  {
    ASSERT_OK_AND_ASSIGN(auto parse_constraints,
                         EvaluateSaiParser(state_->context.ingress_headers));
    for (auto& constraint : parse_constraints) state_->solver->add(constraint);
  }

  // Add ICMP constraint.
  {
    ASSERT_OK_AND_ASSIGN(SaiFields fields,
                         GetSaiFields(state_->context.ingress_headers));
    state_->solver->add(fields.headers.icmp.valid);
  }

  // Solve and deparse.
  ASSERT_EQ(state_->solver->check(), z3::check_result::sat);
  auto model = state_->solver->get_model();
  ASSERT_OK_AND_ASSIGN(std::string raw_packet,
                       SaiDeparser(state_->context.ingress_headers, model));

  // Check we indeed got an ARP packet.
  packetlib::Packet packet = packetlib::ParsePacket(raw_packet);
  LOG(INFO) << "Z3-generated packet = " << packet.DebugString();
  ASSERT_GE(packet.headers_size(), 3);
  ASSERT_TRUE(packet.headers(0).has_ethernet_header());
  ASSERT_TRUE(packet.headers(1).has_ipv4_header() ||
              packet.headers(1).has_ipv6_header());
  ASSERT_TRUE(packet.headers(2).has_icmp_header());
  ASSERT_THAT(packet.payload(), IsEmpty());
}

TEST_P(SaiDeparserTest, PacketInHeaderIsNeverParsedIntegrationTest) {
  // Add parse constraints.
  {
    ASSERT_OK_AND_ASSIGN(auto parse_constraints,
                         EvaluateSaiParser(state_->context.ingress_headers));
    for (auto& constraint : parse_constraints) state_->solver->add(constraint);
  }

  // Add packet_in constraint.
  {
    ASSERT_OK_AND_ASSIGN(SaiFields fields,
                         GetSaiFields(state_->context.ingress_headers));
    // TODO: Execute the test unconditionally one we add the
    // packet-in header to SAI P4.
    if (!fields.headers.packet_in.has_value()) {
      GTEST_SKIP() << "test does not apply, as program has no packet-in header";
    }
    state_->solver->add(fields.headers.packet_in.value().valid);
  }

  // Should be unsatisifiable, because we never parse a packet-in header.
  ASSERT_EQ(state_->solver->check(), z3::check_result::unsat);
}

TEST_P(SaiDeparserTest, DISABLED_PacketInPacketParserIntegrationTest) {
  // Add packet_in constraint.
  {
    ASSERT_OK_AND_ASSIGN(SaiFields fields,
                         GetSaiFields(state_->context.ingress_headers));
    // TODO: Execute the test unconditionally one we add the
    // packet-in header to SAI P4.
    if (!fields.headers.packet_in.has_value()) {
      GTEST_SKIP() << "test does not apply, as program has no packet-in header";
    }
    state_->solver->add(fields.headers.packet_in.value().valid);
  }

  // Solve and deparse.
  ASSERT_EQ(state_->solver->check(), z3::check_result::sat);
  auto model = state_->solver->get_model();
  ASSERT_OK_AND_ASSIGN(std::string raw_packet,
                       SaiDeparser(state_->context.ingress_headers, model));

  // Check we indeed got a packet_in packet.
  packetlib::Packet packet = packetlib::ParsePacket(raw_packet);
  LOG(INFO) << "Z3-generated packet = " << packet.DebugString();
  ASSERT_GE(packet.headers_size(), 0);
  ASSERT_TRUE(packet.headers(0).has_sai_p4_bmv2_packet_in_header());
}

INSTANTIATE_TEST_SUITE_P(Instantiation, SaiDeparserTest,
                         testing::ValuesIn(sai::AllSaiInstantiations()));

}  // namespace
}  // namespace p4_symbolic
