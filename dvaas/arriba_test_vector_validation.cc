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

#include <vector>

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "dvaas/packet_injection.h"
#include "dvaas/port_id_map.h"
#include "dvaas/test_run_validation.h"
#include "dvaas/test_vector.h"
#include "dvaas/test_vector.pb.h"
#include "glog/logging.h"
#include "gutil/status.h"
#include "gutil/test_artifact_writer.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/p4_runtime_session_extras.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"

namespace dvaas {

absl::Status ValidateAgainstArribaTestVector(
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
  for (const auto& [id, packet_test_vector] :
       arriba_test_vector.packet_test_vector_by_id()) {
    test_vector_by_id[id] = packet_test_vector;
  }

  PacketStatistics packet_statistics;
  gutil::BazelTestArtifactWriter artifact_writer;

  // Send tests to switch and collect results.
  ASSIGN_OR_RETURN(PacketTestRuns test_runs,
                   SendTestPacketsAndCollectOutputs(
                       sut, control_switch, test_vector_by_id,
                       {
                           .max_packets_to_send_per_second =
                               params.max_packets_to_send_per_second,
                           .mirror_testbed_port_map =
                               MirrorTestbedP4rtPortIdMap::CreateIdentityMap(),
                       },
                       packet_statistics));

  // Compare the switch output with expected output for each test vector.
  return ValidateTestRuns(test_runs, params.switch_output_diff_params,
                          /*write_failures=*/[&](absl::string_view failures) {
                            return artifact_writer.AppendToTestArtifact(
                                "test_failures.txt", failures);
                          });
}
}  // namespace dvaas
