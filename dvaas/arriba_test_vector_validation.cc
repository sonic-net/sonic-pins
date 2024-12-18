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
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
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

absl::StatusOr<absl::btree_set<pins_test::P4rtPortId>> GetUsedP4rtPortIds(
    const ArribaTestVector& arriba_test_vector,
    const pdpi::IrP4Info& ir_p4_info) {
  std::vector<pdpi::IrTableEntry> used_entries_list(
      arriba_test_vector.ir_table_entries().entries().begin(),
      arriba_test_vector.ir_table_entries().entries().end());
  ASSIGN_OR_RETURN(absl::btree_set<pins_test::P4rtPortId> used_p4rt_port_ids,
                   pins_test::GetPortsUsed(ir_p4_info, used_entries_list));

  for (const auto& [_, packet_test_vector] :
       arriba_test_vector.packet_test_vector_by_id()) {
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

  RETURN_IF_ERROR(pdpi::ClearTableEntries(&control_switch));
  RETURN_IF_ERROR(pdpi::InstallPiEntities(control_switch, punt_entities));

  // Prepare the SUT.
  LOG(INFO) << "Installing entries from the given test vector on the SUT";
  RETURN_IF_ERROR(pdpi::ClearTableEntries(&sut));
  RETURN_IF_ERROR(
      pdpi::InstallIrTableEntries(sut, arriba_test_vector.ir_table_entries()));

  // Prepare single packet test vectors.
  PacketTestVectorById test_vector_by_id;
  std::vector<PacketTestVector> packet_test_vectors;
  for (const auto& [id, packet_test_vector] :
       arriba_test_vector.packet_test_vector_by_id()) {
    test_vector_by_id[id] = packet_test_vector;
    packet_test_vectors.push_back(packet_test_vector);
  }

  PacketStatistics packet_statistics;
  gutil::BazelTestArtifactWriter artifact_writer;

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
          },
          packet_statistics));

  ASSIGN_OR_RETURN(const pdpi::IrTableEntries installed_entries_sut,
                   pdpi::ReadIrTableEntries(sut));
  RETURN_IF_ERROR(artifact_writer.AppendToTestArtifact(
      "sut_installed_entries.txtpb",
      gutil::PrintTextProto(installed_entries_sut)));

  ASSIGN_OR_RETURN(const pdpi::IrTableEntries installed_entries_control,
                   pdpi::ReadIrTableEntries(control_switch));
  RETURN_IF_ERROR(artifact_writer.AppendToTestArtifact(
      "control_installed_entries.txtpb",
      gutil::PrintTextProto(installed_entries_control)));

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
