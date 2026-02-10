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

#include "p4_symbolic/packet_synthesizer/packet_synthesizer.h"

#include <optional>

#include "absl/log/log.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/test_artifact_writer.h"
#include "gutil/gutil/testing.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_infra/p4_pdpi/pd.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesizer.pb.h"
#include "p4_symbolic/sai/sai.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_nonstandard_platforms.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"

namespace p4_symbolic::packet_synthesizer {
namespace {

// Returns packet synthesis parameters with the pipeline config for FBR and a
// simple table entry.
// If `in_port_match` is not null, the added entry matches on the provided
// ingress port.
PacketSynthesisParams GetParams(
    std::optional<std::string> in_port_match = std::nullopt) {
  const sai::Instantiation instantiation =
      sai::Instantiation::kFabricBorderRouter;
  const pdpi::IrP4Info ir_p4info = sai::GetIrP4Info(instantiation);
  const p4::v1::ForwardingPipelineConfig pipeline_config =
      sai::GetNonstandardForwardingPipelineConfig(
          instantiation, sai::NonstandardPlatform::kP4Symbolic);

  PacketSynthesisParams params;
  *params.mutable_pipeline_config() = pipeline_config;
  auto pd_entry = gutil::ParseProtoOrDie<sai::TableEntry>(R"pb(
    acl_pre_ingress_table_entry {
      match {}
      action { set_vrf { vrf_id: "vrf-80" } }
      priority: 1
    })pb");
  if (in_port_match.has_value())
    pd_entry.mutable_acl_pre_ingress_table_entry()
        ->mutable_match()
        ->mutable_in_port()
        ->set_value(*in_port_match);
  const auto pi_entry =
      pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, pd_entry);

  CHECK_OK(pi_entry.status());
  *params.add_pi_entities()->mutable_table_entry() = *pi_entry;

  return params;
}

TEST(PacketSynthesizerTest, SynthesizePacketSatisfiableCriteriaYieldsAPacket) {
  // Get a packet synthesizer object.
  ASSERT_OK_AND_ASSIGN(auto synthesizer,
                       PacketSynthesizer::Create(GetParams()));

  // Synthesize Packet.
  ASSERT_OK_AND_ASSIGN(
      const PacketSynthesisResult result,
      synthesizer->SynthesizePacket(
          gutil::ParseProtoOrDie<PacketSynthesisCriteria>(
              R"pb(
                output_criteria { drop_expected: True }
                table_reachability_criteria {
                  table_name: "ingress.acl_pre_ingress.acl_pre_ingress_table"
                }
                table_entry_reachability_criteria {
                  table_name: "ingress.acl_pre_ingress.acl_pre_ingress_table"
                  match_index: 0
                }
              )pb")));

  // Check the synthesized packet.
  ASSERT_TRUE(result.has_synthesized_packet());
}

TEST(PacketSynthesizerTest, SynthesizePacketYieldsPackets) {
  // Get a packet synthesizer object.
  ASSERT_OK_AND_ASSIGN(
      const PacketSynthesisResults results,
      PacketSynthesizer::SynthesizePacketsForPathCoverage(GetParams()));
  gutil::BazelTestArtifactWriter artifact_writer;
  ASSERT_OK(artifact_writer.AppendToTestArtifact(
      "results.txtpb", gutil::PrintTextProto(results)));
  // Keeping it at 500 to make the test less brittle with changing SAI-P4.
  ASSERT_GT(results.results_size(), 500);
}

TEST(PacketSynthesizerTest,
     SynthesizePacketWithUnsatisfiableCriteriaDoesNotYieldAPacket) {
  // Get a packet synthesizer object.
  ASSERT_OK_AND_ASSIGN(auto synthesizer,
                       PacketSynthesizer::Create(GetParams()));

  // Synthesize Packet.
  ASSERT_OK_AND_ASSIGN(
      const PacketSynthesisResult result,
      synthesizer->SynthesizePacket(
          gutil::ParseProtoOrDie<PacketSynthesisCriteria>(
              R"pb(
                table_reachability_criteria {
                  table_name: "ingress.acl_pre_ingress.acl_pre_ingress_table"
                }
                table_entry_reachability_criteria {
                  table_name: "ingress.acl_pre_ingress.acl_pre_ingress_table"
                  match_index: -1
                }
              )pb")));

  // Check the synthesized packet.
  ASSERT_FALSE(result.has_synthesized_packet());
}

TEST(PacketSynthesizerTest,
     SynthesizePacketWithIpv4ValidCriteriaYieldsIpv4Packet) {
  // Get a packet synthesizer object.
  ASSERT_OK_AND_ASSIGN(auto synthesizer,
                       PacketSynthesizer::Create(GetParams()));

  // Synthesize Packet.
  ASSERT_OK_AND_ASSIGN(const PacketSynthesisResult result,
                       synthesizer->SynthesizePacket(
                           gutil::ParseProtoOrDie<PacketSynthesisCriteria>(
                               R"pb(
                                 output_criteria { drop_expected: True }
                                 input_packet_header_criteria {
                                   field_criteria {
                                     field_match {
                                       name: "ipv4.$valid$"
                                       exact { hex_str: "0x1" }
                                     }
                                   }
                                   # No VLAN header
                                   field_criteria {
                                     field_match {
                                       name: "vlan.$valid$"
                                       exact { hex_str: "0x0" }
                                     }
                                   }
                                 }
                               )pb")));

  // Check the synthesized packet.
  ASSERT_TRUE(result.has_synthesized_packet());
  const auto& synthesized_packet = result.synthesized_packet();
  LOG(INFO) << synthesized_packet.DebugString();
  ASSERT_TRUE(packetlib::ParsePacket(synthesized_packet.packet())
                  .headers(1)
                  .has_ipv4_header());
}

TEST(PacketSynthesizerTest,
     SynthesizePacketWithIpv4DstAddrCriteriaYieldsProperPacket) {
  // Get a packet synthesizer object.
  ASSERT_OK_AND_ASSIGN(auto synthesizer,
                       PacketSynthesizer::Create(GetParams()));

  // Synthesize Packet.
  ASSERT_OK_AND_ASSIGN(const PacketSynthesisResult result,
                       synthesizer->SynthesizePacket(
                           gutil::ParseProtoOrDie<PacketSynthesisCriteria>(
                               R"pb(
                                 output_criteria { drop_expected: True }
                                 input_packet_header_criteria {
                                   field_criteria {
                                     field_match {
                                       name: "ipv4.$valid$"
                                       exact { hex_str: "0x1" }
                                     }
                                   }
                                   field_criteria {
                                     field_match {
                                       name: "ipv4.dst_addr"
                                       lpm {
                                         value { ipv4: "10.0.0.0" }
                                         prefix_length: 8
                                       }
                                     }
                                   }
                                   # No VLAN header
                                   field_criteria {
                                     field_match {
                                       name: "vlan.$valid$"
                                       exact { hex_str: "0x0" }
                                     }
                                   }
                                 }
                               )pb")));

  // Check the synthesized packet.
  ASSERT_TRUE(result.has_synthesized_packet());
  const auto& synthesized_packet = result.synthesized_packet();
  LOG(INFO) << synthesized_packet.DebugString();
  packetlib::Packet packet =
      packetlib::ParsePacket(synthesized_packet.packet());
  const auto& second_header = packet.headers(1);
  ASSERT_TRUE(second_header.has_ipv4_header());
  ASSERT_TRUE(
      absl::StartsWith(second_header.ipv4_header().ipv4_destination(), "10."));
}

TEST(PacketSynthesizerTest,
     SynthesizePacketWithTernaryIpv4DstAddrCriteriaYieldsProperPacket) {
  // Get a packet synthesizer object.
  ASSERT_OK_AND_ASSIGN(auto synthesizer,
                       PacketSynthesizer::Create(GetParams()));

  // Synthesize Packet.
  ASSERT_OK_AND_ASSIGN(const PacketSynthesisResult result,
                       synthesizer->SynthesizePacket(
                           gutil::ParseProtoOrDie<PacketSynthesisCriteria>(
                               R"pb(
                                 output_criteria { drop_expected: True }
                                 input_packet_header_criteria {
                                   field_criteria {
                                     field_match {
                                       name: "ipv4.$valid$"
                                       exact { hex_str: "0x1" }
                                     }
                                   }
                                   field_criteria {
                                     field_match {
                                       name: "ipv4.dst_addr"
                                       ternary {
                                         value { ipv4: "10.0.0.0" }
                                         mask { ipv4: "255.0.0.0" }
                                       }
                                     }
                                   }
                                   # No VLAN header
                                   field_criteria {
                                     field_match {
                                       name: "vlan.$valid$"
                                       exact { hex_str: "0x0" }
                                     }
                                   }
                                 }
                               )pb")));

  // Check the synthesized packet.
  ASSERT_TRUE(result.has_synthesized_packet());
  const auto& synthesized_packet = result.synthesized_packet();
  LOG(INFO) << synthesized_packet.DebugString();
  packetlib::Packet packet =
      packetlib::ParsePacket(synthesized_packet.packet());
  const auto& second_header = packet.headers(1);
  ASSERT_TRUE(second_header.has_ipv4_header());
  ASSERT_TRUE(
      absl::StartsWith(second_header.ipv4_header().ipv4_destination(), "10."));
}

TEST(PacketSynthesizerTest,
     SynthesizePacketWithIngressPortCriteriaYieldsProperPacket) {
  constexpr int kPortCount = 10;

  // Get basic parameters to create packet synthesizer object.
  // TODO: If no entry matches on ingress port, P4-Symbolic misses
  // that local_metadata.ingress_port is p4runtime_translated. In such cases,
  // the synthesizer will return empty string ("") as the ingress port. Here we
  // add a match on in_port to prevent such a scenario.
  PacketSynthesisParams params = GetParams(/*in_port_match=*/"7");

  // Prepare v1model ports and P4RT <-> v1model port translation.
  TranslationData& port_translation =
      (*params.mutable_translation_per_type())[p4_symbolic::kPortIdTypeName];
  for (int port = 1; port <= kPortCount; port++) {
    params.add_physical_port(port);
    TranslationData::StaticMapping& static_mapping =
        *port_translation.add_static_mapping();
    static_mapping.set_string_value(absl::StrCat(port));
    static_mapping.set_integer_value(port);
  }

  // Get a packet synthesizer object.
  ASSERT_OK_AND_ASSIGN(auto synthesizer, PacketSynthesizer::Create(params));

  // Synthesize Packet.
  ASSERT_OK_AND_ASSIGN(const PacketSynthesisResult result,
                       synthesizer->SynthesizePacket(
                           gutil::ParseProtoOrDie<PacketSynthesisCriteria>(
                               R"pb(
                                 output_criteria { drop_expected: True }
                                 ingress_port_criteria { v1model_port: 5 }
                               )pb")));

  // Check the synthesized packet's port.
  ASSERT_TRUE(result.has_synthesized_packet());
  const auto& synthesized_packet = result.synthesized_packet();
  LOG(INFO) << synthesized_packet.DebugString();
  ASSERT_EQ(synthesized_packet.ingress_port(), "5");
}

}  // namespace
}  // namespace p4_symbolic::packet_synthesizer
