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

#include "dvaas/arriba_test_vector_validation.h"

#include <string>
#include <utility>
#include <vector>

#include "absl/container/btree_set.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "dvaas/label.h"
#include "dvaas/packet_injection.h"
#include "dvaas/port_id_map.h"
#include "dvaas/test_insights.h"
#include "dvaas/test_run_validation.h"
#include "dvaas/test_vector.h"
#include "dvaas/test_vector.pb.h"
#include "dvaas/validation_result.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/test_artifact_writer.h"
#include "lib/p4rt/p4rt_port.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/p4_runtime_session_extras.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"
#include "tests/lib/switch_test_setup_helpers.h"

namespace dvaas {

absl::StatusOr<ArribaTestVector> GetUpdatedArribaTestVector(
    const ArribaTestVector& arriba_test_vector) {
  if (arriba_test_vector.has_ir_entities()) {
    if (arriba_test_vector.has_ir_table_entries())
      return absl::InvalidArgumentError(
          "ArribaTestVector has both ir_entities and ir_table_entries set.");
    return arriba_test_vector;
  }
  ArribaTestVector updated_test_vector = arriba_test_vector;
  for (const auto& table_entry :
       arriba_test_vector.ir_table_entries().entries()) {
    *updated_test_vector.mutable_ir_entities()
         ->add_entities()
         ->mutable_table_entry() = table_entry;
  }
  updated_test_vector.clear_ir_table_entries();
  return updated_test_vector;
}

absl::StatusOr<absl::btree_set<pins_test::P4rtPortId>> GetUsedP4rtPortIds(
    const ArribaTestVector& arriba_test_vector,
    const pdpi::IrP4Info& ir_p4_info) {
  ASSIGN_OR_RETURN(ArribaTestVector updated_arriba_test_vector,
                   GetUpdatedArribaTestVector(arriba_test_vector));
  std::vector<pdpi::IrEntity> used_entities_list(
      updated_arriba_test_vector.ir_entities().entities().begin(),
      updated_arriba_test_vector.ir_entities().entities().end());
  ASSIGN_OR_RETURN(absl::btree_set<pins_test::P4rtPortId> used_p4rt_port_ids,
                   pins_test::GetPortsUsed(ir_p4_info, used_entities_list));

  for (const auto& [_, packet_test_vector] :
       updated_arriba_test_vector.packet_test_vector_by_id()) {
    ASSIGN_OR_RETURN(pins_test::P4rtPortId p4rt_port_id,
                     pins_test::P4rtPortId::MakeFromP4rtEncoding(
                         packet_test_vector.input().packet().port()));
    used_p4rt_port_ids.insert(p4rt_port_id);
  }
  return used_p4rt_port_ids;
}

absl::StatusOr<ValidationResult> ValidateAgainstArribaTestVector(
    pdpi::P4RuntimeSession& sut, pdpi::P4RuntimeSession& control_switch,
    const ArribaTestVector& arriba_test_vector,
    const ArribaTestVectorValidationParams& params) {
  ASSIGN_OR_RETURN(ArribaTestVector updated_arriba_test_vector,
                   GetUpdatedArribaTestVector(arriba_test_vector));
  // Store the test vector as a test artifact.
  gutil::BazelTestArtifactWriter artifact_writer;
  RETURN_IF_ERROR(artifact_writer.AppendToTestArtifact(
      "arriba_test_vector.txtpb", updated_arriba_test_vector));

  // Prepare the control switch.
  LOG(INFO) << "Installing entires to punt all packets on the control switch";
  ASSIGN_OR_RETURN(p4::v1::GetForwardingPipelineConfigResponse config,
                   GetForwardingPipelineConfig(&control_switch));
  ASSIGN_OR_RETURN(pdpi::IrP4Info ir_p4info,
                   pdpi::CreateIrP4Info(config.config().p4info()));
  ASSIGN_OR_RETURN(std::vector<p4::v1::Entity> punt_entities,
                   sai::EntryBuilder()
                       .AddEntryPuntingAllPackets(sai::PuntAction::kTrap)
                       .GetDedupedPiEntities(ir_p4info));

  RETURN_IF_ERROR(pdpi::ClearEntities(control_switch));
  RETURN_IF_ERROR(pdpi::InstallPiEntities(control_switch, punt_entities));

  // Prepare the SUT.
  LOG(INFO) << "Installing entries from the given test vector on the SUT";
  RETURN_IF_ERROR(pdpi::ClearEntities(sut));
  RETURN_IF_ERROR(
      pdpi::InstallIrEntities(sut, updated_arriba_test_vector.ir_entities()));

  LOG(INFO) << "Installed entries successfully";

  // Prepare single packet test vectors.
  PacketTestVectorById test_vector_by_id;
  std::vector<PacketTestVector> packet_test_vectors;
  for (const auto& [id, packet_test_vector] :
       updated_arriba_test_vector.packet_test_vector_by_id()) {
    test_vector_by_id[id] = packet_test_vector;
    packet_test_vectors.push_back(packet_test_vector);
  }

  PacketStatistics packet_statistics;

  // Send tests to switch and collect results.
  ASSIGN_OR_RETURN(
      PacketTestRuns test_runs,
      SendTestPacketsAndCollectOutputs(
          sut, control_switch, test_vector_by_id,
          {
              .max_packets_to_send_per_second =
                  params.max_packets_to_send_per_second,
              .is_expected_unsolicited_packet =
                  params.is_expected_unsolicited_packet,
              .mirror_testbed_port_map =
                  params.mirror_testbed_port_map_override.has_value()
                      ? *params.mirror_testbed_port_map_override
                      : MirrorTestbedP4rtPortIdMap::CreateIdentityMap(),
              .enable_sut_packet_in_collection =
                  params.enable_sut_packet_in_collection,
              .max_expected_packet_in_flight_duration =
                  params.max_expected_packet_in_flight_duration,
              .max_in_flight_packets = params.max_in_flight_packets,
          },
          packet_statistics));

  ASSIGN_OR_RETURN(const pdpi::IrEntities installed_entities_sut,
                   pdpi::ReadIrEntities(sut));
  RETURN_IF_ERROR(artifact_writer.AppendToTestArtifact(
      "sut_installed_entities.txtpb",
      gutil::PrintTextProto(installed_entities_sut)));

  ASSIGN_OR_RETURN(const pdpi::IrEntities installed_entities_control,
                   pdpi::ReadIrEntities(control_switch));
  RETURN_IF_ERROR(artifact_writer.AppendToTestArtifact(
      "control_installed_entities.txtpb",
      gutil::PrintTextProto(installed_entities_control)));

  LOG(INFO) << "Number of packets injected: "
            << packet_statistics.total_packets_injected;
  LOG(INFO) << "packet forwarded: "
            << packet_statistics.total_packets_forwarded;
  LOG(INFO) << "packet punted: " << packet_statistics.total_packets_punted;

  // Compare the switch output with expected output for each test vector.
  LOG(INFO) << "Validating test runs";
  ASSIGN_OR_RETURN(
      PacketTestOutcomes test_outcomes,
      ValidateTestRuns(test_runs, params.switch_output_diff_params));

  // Use labelers to add labels to test outcomes.
  auto status = AugmentTestOutcomesWithLabels(test_outcomes, params.labelers);
  if (!status.ok()) {
    LOG(ERROR) << "Failed to augment test outcomes with labels: "
               << status.message();
  }

  // Store test outcomes.
  RETURN_IF_ERROR(artifact_writer.AppendToTestArtifact(
      "test_outcomes.txtpb", gutil::PrintTextProto(test_outcomes)));

  // Store test insights.
  ASSIGN_OR_RETURN(const std::string insights_csv,
                   GetTestInsightsTableAsCsv(test_outcomes, ir_p4info));
  RETURN_IF_ERROR(
      artifact_writer.AppendToTestArtifact("test_insights.csv", insights_csv));

  ValidationResult validation_result(std::move(test_outcomes),
                                     /*packet_synthesis_result=*/{});
  RETURN_IF_ERROR(artifact_writer.AppendToTestArtifact(
      "test_vector_failures.txt",
      absl::StrJoin(validation_result.GetAllFailures(), "\n\n")));

  validation_result.LogStatistics();
  return validation_result;
}
}  // namespace dvaas
