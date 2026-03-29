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

#include "dvaas/portable_pins_backend/portable_pins_backend.h"

#include <memory>
#include <optional>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "dvaas/dataplane_validation.h"
#include "dvaas/output_writer.h"
#include "dvaas/switch_api.h"
#include "dvaas/test_vector.h"
#include "dvaas/test_vector.pb.h"
#include "fourward/fourward_oracle.h"
#include "fourward/test_vector_generation.h"
#include "gutil/status.h"
#include "lib/p4rt/p4rt_port.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_runtime/p4_runtime_session.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_symbolic/packet_synthesizer/coverage_goal.pb.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesizer.pb.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"
#include "sai_p4/tools/auxiliary_entries_for_v1model_targets.h"
#include "github.com/openconfig/gnmi/proto/gnmi/gnmi.grpc.pb.h"

namespace dvaas {
namespace {

class PortablePinsBackend : public DataplaneValidationBackend {
 public:
  explicit PortablePinsBackend(p4::v1::ForwardingPipelineConfig fourward_config)
      : fourward_config_(std::move(fourward_config)) {}

  absl::StatusOr<PacketSynthesisResult> SynthesizePackets(
      const pdpi::IrP4Info& ir_p4info, const pdpi::IrEntities& ir_entities,
      const p4::v1::ForwardingPipelineConfig& p4_symbolic_config,
      absl::Span<const pins_test::P4rtPortId> ports,
      const OutputWriterFunctionType& write_stats,
      const std::optional<p4_symbolic::packet_synthesizer::CoverageGoals>&
          coverage_goals_override,
      std::optional<absl::Duration> time_limit) const override {
    return absl::UnimplementedError(
        "Packet synthesis is not yet implemented in the portable PINS "
        "backend. Use DataplaneValidationParams::packet_test_vector_override "
        "to provide test vectors manually.");
  }

  absl::StatusOr<PacketTestVectorById> GeneratePacketTestVectors(
      const pdpi::IrP4Info& ir_p4info, const pdpi::IrEntities& ir_entities,
      const p4::v1::ForwardingPipelineConfig& bmv2_config,
      absl::Span<const pins_test::P4rtPortId> ports,
      std::vector<p4_symbolic::packet_synthesizer::SynthesizedPacket>&
          synthesized_packets,
      const pins_test::P4rtPortId& default_ingress_port,
      bool check_prediction_conformity) const override {
    ASSIGN_OR_RETURN(std::unique_ptr<FourwardOracle> oracle,
                     FourwardOracle::Create(fourward_config_));
    RETURN_IF_ERROR(oracle->InstallIrEntities(ir_entities));
    return GeneratePacketTestVectorsUsingFourward(*oracle, synthesized_packets,
                                                  default_ingress_port);
  }

  absl::StatusOr<pdpi::IrEntities> GetEntitiesToPuntAllPackets(
      const pdpi::IrP4Info& switch_p4info) const override {
    return sai::EntryBuilder()
        .AddEntryPuntingAllPackets(sai::PuntAction::kCopy)
        .GetDedupedIrEntities(switch_p4info);
  }

  absl::StatusOr<P4Specification> InferP4Specification(
      SwitchApi& sut) const override {
    ASSIGN_OR_RETURN(
        p4::v1::GetForwardingPipelineConfigResponse response,
        p4_runtime::GetForwardingPipelineConfig(sut.p4rt.get()));
    const p4::config::v1::P4Info& p4info = response.config().p4info();
    P4Specification spec;
    // p4_symbolic_config and bmv2_config are unused when fourward_config is
    // set, but P4Info must still be populated for DVaaS internals that read it.
    *spec.p4_symbolic_config.mutable_p4info() = p4info;
    *spec.bmv2_config.mutable_p4info() = p4info;
    spec.fourward_config = fourward_config_;
    return spec;
  }

  absl::Status AugmentPacketTestVectorsWithPacketTraces(
      std::vector<PacketTestVector>& packet_test_vectors,
      const pdpi::IrP4Info& ir_p4info, const pdpi::IrEntities& ir_entities,
      const p4::v1::ForwardingPipelineConfig& bmv2_compatible_config,
      bool use_compact_traces) const override {
    // 4ward attaches traces during output prediction in
    // GeneratePacketTestVectorsUsingFourward, so no separate step is needed.
    return absl::OkStatus();
  }

  absl::StatusOr<pdpi::IrEntities> CreateV1ModelAuxiliaryEntities(
      const pdpi::IrEntities& ir_entities, const pdpi::IrP4Info& ir_p4info,
      gnmi::gNMI::StubInterface& gnmi_stub) const override {
    return sai::CreateV1ModelAuxiliaryEntities(ir_entities, gnmi_stub);
  }

 private:
  p4::v1::ForwardingPipelineConfig fourward_config_;
};

}  // namespace

std::unique_ptr<DataplaneValidationBackend> CreatePortablePinsBackend(
    p4::v1::ForwardingPipelineConfig fourward_config) {
  return std::make_unique<PortablePinsBackend>(std::move(fourward_config));
}

}  // namespace dvaas
