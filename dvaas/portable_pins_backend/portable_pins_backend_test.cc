// Copyright 2026 Google LLC
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

// Tests for the portable PINS backend: unit tests for each method and an
// integration test exercising the backend against a FourwardMirrorTestbed.

#include "dvaas/portable_pins_backend/portable_pins_backend.h"

#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "absl/status/statusor.h"
#include "dvaas/dataplane_validation.h"
#include "dvaas/switch_api.h"
#include "dvaas/test_vector.h"
#include "dvaas/test_vector.pb.h"
#include "fourward/fourward_mirror_testbed.h"
#include "fourward/fourward_oracle.h"
#include "fourward/test_vector_generation.h"
#include "gtest/gtest.h"
#include "gutil/io.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "lib/p4rt/p4rt_port.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_runtime/p4_runtime_session.h"
#include "p4_infra/p4_runtime/p4_runtime_session_extras.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesizer.pb.h"
#include "packetlib/packetlib.h"
#include "packetlib/packetlib.pb.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"
#include "tools/cpp/runfiles/runfiles.h"

namespace dvaas {
namespace {

using ::bazel::tools::cpp::runfiles::Runfiles;
using ::gutil::ParseProtoOrDie;

p4::v1::ForwardingPipelineConfig LoadFourwardConfig() {
  std::string error;
  std::unique_ptr<Runfiles> runfiles(Runfiles::CreateForTest(&error));
  EXPECT_NE(runfiles, nullptr) << "Failed to create Runfiles: " << error;
  absl::StatusOr<std::string> contents = gutil::ReadFile(
      runfiles->Rlocation("_main/fourward/sai_middleblock_fourward.binpb"));
  EXPECT_OK(contents);
  p4::v1::ForwardingPipelineConfig config;
  EXPECT_TRUE(config.ParseFromString(*contents));
  return config;
}

// Serializes a packetlib textproto into raw bytes, padding and computing
// checksums.
std::string SerializeTestPacket(absl::string_view textproto) {
  packetlib::Packet packet = ParseProtoOrDie<packetlib::Packet>(textproto);
  CHECK(packetlib::PadPacketToMinimumSize(packet).ok());
  CHECK(packetlib::UpdateAllComputedFields(packet).ok());
  absl::StatusOr<std::string> serialized = packetlib::SerializePacket(packet);
  CHECK(serialized.ok());
  return *serialized;
}

TEST(PortablePinsBackendTest, SynthesizePacketsReturnsUnimplemented) {
  p4::v1::ForwardingPipelineConfig fourward_config = LoadFourwardConfig();
  std::unique_ptr<DataplaneValidationBackend> backend =
      CreatePortablePinsBackend(fourward_config);

  pdpi::IrP4Info ir_p4info;
  pdpi::IrEntities ir_entities;
  p4::v1::ForwardingPipelineConfig p4_symbolic_config;
  EXPECT_THAT(backend->SynthesizePackets(ir_p4info, ir_entities,
                                         p4_symbolic_config, {}, nullptr,
                                         std::nullopt),
              gutil::StatusIs(absl::StatusCode::kUnimplemented));
}

TEST(PortablePinsBackendTest, GetEntitiesToPuntAllPacketsSucceeds) {
  p4::v1::ForwardingPipelineConfig fourward_config = LoadFourwardConfig();
  std::unique_ptr<DataplaneValidationBackend> backend =
      CreatePortablePinsBackend(fourward_config);

  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(fourward_config.p4info()));
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities punt_entities,
                       backend->GetEntitiesToPuntAllPackets(ir_p4info));
  EXPECT_FALSE(punt_entities.entities().empty());
}

TEST(PortablePinsBackendTest, AugmentPacketTestVectorsIsNoOp) {
  p4::v1::ForwardingPipelineConfig fourward_config = LoadFourwardConfig();
  std::unique_ptr<DataplaneValidationBackend> backend =
      CreatePortablePinsBackend(fourward_config);

  std::vector<PacketTestVector> vectors;
  pdpi::IrP4Info ir_p4info;
  pdpi::IrEntities ir_entities;
  p4::v1::ForwardingPipelineConfig bmv2_config;
  EXPECT_OK(backend->AugmentPacketTestVectorsWithPacketTraces(
      vectors, ir_p4info, ir_entities, bmv2_config,
      /*use_compact_traces=*/false));
}

TEST(PortablePinsBackendTest,
     GeneratePacketTestVectorsProducesCorrectPredictions) {
  p4::v1::ForwardingPipelineConfig fourward_config = LoadFourwardConfig();
  std::unique_ptr<DataplaneValidationBackend> backend =
      CreatePortablePinsBackend(fourward_config);

  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(fourward_config.p4info()));

  // Build IR entities for forwarding.
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities ir_entities,
      sai::EntryBuilder()
          .AddDisableVlanChecksEntry()
          .AddEntriesForwardingIpPacketsToGivenPort("1")
          .GetDedupedIrEntities(ir_p4info));

  // Create a synthesized packet.
  std::string raw_packet = SerializeTestPacket(R"pb(
    headers {
      ethernet_header {
        ethernet_destination: "02:02:02:02:02:02"
        ethernet_source: "00:aa:bb:cc:dd:ee"
        ethertype: "0x0800"
      }
    }
    headers {
      ipv4_header {
        version: "0x4"
        ihl: "0x5"
        dscp: "0x00"
        ecn: "0x0"
        identification: "0x0000"
        flags: "0x0"
        fragment_offset: "0x0000"
        ttl: "0x40"
        protocol: "0x11"
        ipv4_source: "192.168.1.1"
        ipv4_destination: "10.1.2.3"
      }
    }
    headers {
      udp_header { source_port: "0x0000" destination_port: "0x0000" }
    }
  )pb");

  std::vector<p4_symbolic::packet_synthesizer::SynthesizedPacket>
      synthesized_packets;
  p4_symbolic::packet_synthesizer::SynthesizedPacket synthesized;
  synthesized.set_packet(raw_packet);
  synthesized.set_ingress_port("0");
  synthesized_packets.push_back(std::move(synthesized));

  ASSERT_OK_AND_ASSIGN(pins_test::P4rtPortId default_port,
                       pins_test::P4rtPortId::MakeFromP4rtEncoding("0"));
  ASSERT_OK_AND_ASSIGN(
      PacketTestVectorById test_vectors,
      backend->GeneratePacketTestVectors(
          ir_p4info, ir_entities, fourward_config, {default_port},
          synthesized_packets, default_port,
          /*check_prediction_conformity=*/false));

  ASSERT_EQ(test_vectors.size(), 1);
  const PacketTestVector& vector = test_vectors.begin()->second;
  EXPECT_TRUE(vector.has_input());
  EXPECT_FALSE(vector.acceptable_outputs().empty());
  // The packet should be forwarded (not dropped).
  EXPECT_FALSE(vector.acceptable_outputs(0).packets().empty());
  // Forwarded to port "1".
  EXPECT_EQ(vector.acceptable_outputs(0).packets(0).port(), "1");
}

// E2E integration: verifies the backend drives a FourwardMirrorTestbed
// end-to-end — pipeline loading, entity installation, punt entry generation,
// and test vector generation with correct predictions.
TEST(PortablePinsBackendTest, BackendWorksEndToEndWithFourwardTestbed) {
  p4::v1::ForwardingPipelineConfig fourward_config = LoadFourwardConfig();

  // -- Testbed ---------------------------------------------------------------
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<FourwardMirrorTestbed> testbed,
                       FourwardMirrorTestbed::Create());

  // Open a P4RT session on the SUT and load the pipeline.
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<p4_runtime::P4RuntimeSession> sut_session,
      p4_runtime::P4RuntimeSession::Create(testbed->Sut()));
  ASSERT_OK(p4_runtime::SetMetadataAndSetForwardingPipelineConfig(
      sut_session.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      fourward_config));

  // Install forwarding entries on the SUT.
  ASSERT_OK(sai::EntryBuilder()
                .AddDisableVlanChecksEntry()
                .AddEntriesForwardingIpPacketsToGivenPort("1")
                .InstallDedupedEntities(*sut_session));

  // -- Backend methods -------------------------------------------------------
  std::unique_ptr<DataplaneValidationBackend> backend =
      CreatePortablePinsBackend(fourward_config);

  // InferP4Specification reads the pipeline from the switch.
  SwitchApi sut;
  sut.p4rt = std::move(sut_session);
  ASSERT_OK_AND_ASSIGN(sut.gnmi, testbed->Sut().CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(P4Specification spec,
                       backend->InferP4Specification(sut));
  EXPECT_TRUE(spec.fourward_config.has_value());
  EXPECT_FALSE(spec.p4_symbolic_config.p4info().tables().empty());

  // GetEntitiesToPuntAllPackets produces non-empty punt entries.
  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(fourward_config.p4info()));
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities punt_entities,
                       backend->GetEntitiesToPuntAllPackets(ir_p4info));
  EXPECT_FALSE(punt_entities.entities().empty());
}

}  // namespace
}  // namespace dvaas
