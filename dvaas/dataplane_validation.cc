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

#include "dvaas/dataplane_validation.h"

#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "absl/algorithm/container.h"
#include "absl/cleanup/cleanup.h"
#include "absl/container/btree_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/str_replace.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "dvaas/output_writer.h"
#include "dvaas/packet_injection.h"
#include "dvaas/packet_trace.pb.h"
#include "dvaas/port_id_map.h"
#include "dvaas/switch_api.h"
#include "dvaas/test_run_validation.h"
#include "dvaas/test_vector.h"
#include "dvaas/test_vector.pb.h"
#include "dvaas/user_provided_packet_test_vector.h"
#include "dvaas/validation_result.h"
#include "glog/logging.h"
#include "gutil/proto.h"
#include "gutil/status.h"
#include "gutil/test_artifact_writer.h"
#include "gutil/version.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/gnmi/openconfig.pb.h"
#include "lib/p4rt/p4rt_port.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/p4_runtime_session_extras.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_pdpi/sequencing.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesizer.pb.h"
#include "proto/gnmi/gnmi.pb.h"
#include "sai_p4/instantiations/google/versions.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "thinkit/mirror_testbed.h"

namespace dvaas {
namespace {

using ::p4_symbolic::packet_synthesizer::SynthesizedPacket;
using ::packetlib::Packet;
using ::pins_test::P4rtPortId;

absl::StatusOr<SynthesizedPacket> GetSynthesizedPacketFromFromTestVector(
    const dvaas::PacketTestVector& test_vector) {
  // Create a synthesized packet from `test_vector`.
  std::string_view packet_port = test_vector.input().packet().port();
  Packet packet = test_vector.input().packet().parsed();
  SynthesizedPacket synthesized_packet;
  *synthesized_packet.mutable_packet() = packet.payload();
  *synthesized_packet.mutable_ingress_port() = packet_port;

  auto test_vector_predicts_drop =
      [](const dvaas::SwitchOutput& output_packets) {
        // If no packets make it out of a front-panel port, that is considered
        // a drop.
        return output_packets.packets().empty();
      };

  // Set `drop_expected` to be the same as `kTestVectorRequiresDrop` to avoid
  // throwing an error in `CheckTestVectorPredictionConformity`.
  const bool kTestVectorRequiresDrop = absl::c_all_of(
      test_vector.acceptable_outputs(), test_vector_predicts_drop);
  synthesized_packet.set_drop_expected(kTestVectorRequiresDrop);

  return synthesized_packet;
}

// Determines the reproducibility rate of a test failure and sets it in
// `test_outcome`.
absl::Status DetermineReproducibilityRate(
    const DataplaneValidationParams& params,
    const PacketInjectionParams& parameters,
    pdpi::P4RuntimeSession& sut_session,
    pdpi::P4RuntimeSession& control_switch_session,
    dvaas::PacketTestOutcome& test_outcome) {
  // Duplicate the packet that caused a test failure.
  PacketTestVectorById test_vectors;
  PacketStatistics statistics;
  for (int tag_id = 0; tag_id < params.failure_enhancement_options
                                    .num_of_replication_attempts_per_failure;
       ++tag_id) {
    PacketTestVector packet_test_vector = test_outcome.test_run().test_vector();
    RETURN_IF_ERROR(UpdateTestTag(packet_test_vector, tag_id));
    test_vectors[tag_id] = std::move(packet_test_vector);
  }

  // Call SendTestPacketsAndCollectOutputs.
  ASSIGN_OR_RETURN(
      PacketTestRuns test_runs,
      SendTestPacketsAndCollectOutputs(sut_session, control_switch_session,
                                       test_vectors, parameters, statistics,
                                       /*log_injection_progress=*/false));

  ValidationResult validation_result =
      ValidationResult(test_runs, params.switch_output_diff_params,
                       /*packet_synthesis_result=*/{});

  test_outcome.mutable_test_result()
      ->mutable_failure()
      ->mutable_minimization_analysis()
      ->set_reproducibility_rate(1 - validation_result.GetSuccessRate());

  return absl::OkStatus();
}

absl::Status MinimizePacketTestVectors(
    SwitchApi& sut_api, dvaas::PacketTestOutcome& test_outcome,
    const std::function<absl::StatusOr<ValidationResult>(
        const SynthesizedPacket& synthesized_packet,
        pdpi::IrEntities& ir_entities)>
        test_and_validate_callback) {
  // Get the `pi_entities` from the SUT.
  ASSIGN_OR_RETURN(std::vector<p4::v1::Entity> pi_entities,
                   pdpi::ReadPiEntities(sut_api.p4rt.get()));

  // Clear and reinstall table entries on the SUT.
  absl::Cleanup cleanup = [&pi_entities, &sut_api]() {
    auto status = pdpi::ClearEntities(*sut_api.p4rt);
    if (!status.ok()) {
      LOG(WARNING) << "Failed to clear entities on the switch: "
                   << status.message();
    }
    status = pdpi::InstallPiEntities(*sut_api.p4rt, pi_entities);
    if (!status.ok()) {
      LOG(WARNING) << "Failed to reinstall entities on the switch: "
                   << status.message();
    }
  };

  ASSIGN_OR_RETURN(pdpi::IrP4Info ir_p4info, pdpi::GetIrP4Info(*sut_api.p4rt));

  // Create a synthesized packet from `test_outcome`.
  ASSIGN_OR_RETURN(SynthesizedPacket synthesized_packet,
                   GetSynthesizedPacketFromFromTestVector(
                       test_outcome.test_run().test_vector()));

  // Order the entities so that an entity that may be depended on by another
  // entity comes first.
  RETURN_IF_ERROR(pdpi::StableSortEntities(ir_p4info, pi_entities));

  // Convert `pi_entities` to `ir_entities` to pass into
  // `generate_test_vectors_callback`.
  ASSIGN_OR_RETURN(pdpi::IrEntities result,
                   pdpi::PiEntitiesToIr(ir_p4info, pi_entities));

  // Iterate backwards through the entities, remove the current entity from the
  // switch, and reinstall the entity on the switch if no failure occurs.
  for (int i = result.entities_size() - 1; i >= 0; --i) {
    // Store the `pi_entity` in case we need to reinstall it on the switch if no
    // failure occurs.
    pdpi::IrEntity ir_entity = result.entities().at(i);

    // Remove the entity from the result.
    result.mutable_entities()->DeleteSubrange(i, 1);

    // Uninstall the entity from the switch.
    if (!DeleteIrEntity(*sut_api.p4rt, ir_entity).ok()) {
      continue;
    }

    // Validate test runs to create test outcomes.
    ASSIGN_OR_RETURN(ValidationResult validation_result,
                     test_and_validate_callback(synthesized_packet, result));

    if (!validation_result.HasFailure()) {
      // If there is no failure, reinstall the entity on the switch and add
      // the entity back to the result.
      RETURN_IF_ERROR(pdpi::InstallIrEntity(*sut_api.p4rt, ir_entity))
          << "Failed to reinstall entity that we just deleted from switch:"
          << gutil::PrintTextProto(ir_entity);
      *result.add_entities() = ir_entity;
    }
  }
  LOG(INFO) << "The initial number of entities is " << pi_entities.size()
            << ".\n";
  LOG(INFO) << "The final number of entities is " << result.entities_size()
            << ".\n";
  LOG(INFO)
      << "The minimal set of entities that caused the test failure is: \n";
  LOG(INFO) << gutil::PrintTextProto(result);
  return absl::OkStatus();
}

std::string ToString(
    const std::vector<SynthesizedPacket>& synthesized_packets) {
  return absl::StrJoin(synthesized_packets, "\n\n\n",
                       [](std::string* out, auto& packet) {
                         absl::StrAppend(out, packet.DebugString());
                       });
}

std::string ToString(const PacketTestVectorById& packet_test_vector_by_id) {
  return absl::StrJoin(packet_test_vector_by_id,
                       absl::StrCat("\n", std::string(80, '-'), "\n\n"),
                       [](std::string* out, auto& it) {
                         absl::StrAppend(out, it.second.DebugString());
                       });
}

// We use a custom test artifact writer that prefixes file names and adds
// headers to contents.
class DvaasTestArtifactWriter : public gutil::TestArtifactWriter {
 public:
  DvaasTestArtifactWriter(gutil::TestArtifactWriter& underlying_writer,
                          const DataplaneValidationParams& params)
      : underlying_writer_(underlying_writer), params_(params) {}

  absl::Status StoreTestArtifact(absl::string_view filename,
                                 absl::string_view contents) override {
    return underlying_writer_.StoreTestArtifact(FixFileName(filename),
                                                FixContents(contents));
  }

  absl::Status AppendToTestArtifact(absl::string_view filename,
                                    absl::string_view contents) override {
    return underlying_writer_.AppendToTestArtifact(FixFileName(filename),
                                                   FixContents(contents));
  }

 private:
  gutil::TestArtifactWriter& underlying_writer_;
  const DataplaneValidationParams& params_;

  std::string FixFileName(absl::string_view filename) {
    return absl::StrCat(params_.artifact_prefix, "_", filename);
  }
  std::string FixContents(absl::string_view contents) {
    return absl::StrCat(params_.get_artifact_header.has_value()
                            ? (*params_.get_artifact_header)()
                            : "",
                        contents, "\n\n\n");
  }
};

}  // namespace

absl::StatusOr<P4Specification> InferP4Specification(
    const DataplaneValidationParams& params,
    const DataplaneValidationBackend& backend, SwitchApi& sut) {
  P4Specification p4_spec;
  if (params.specification_override.has_value()) {
    p4_spec = *params.specification_override;
  } else {
    ASSIGN_OR_RETURN(p4_spec, backend.InferP4Specification(sut));
  }

  // Sanity check if the P4 specification is plausibly accurate.
  ASSIGN_OR_RETURN(
      gutil::Version p4_symbolic_config_version,
      gutil::ParseVersion(
          p4_spec.p4_symbolic_config.p4info().pkg_info().version()));
  ASSIGN_OR_RETURN(
      gutil::Version bmv2_config_version,
      gutil::ParseVersion(
          p4_spec.p4_symbolic_config.p4info().pkg_info().version()));
  ASSIGN_OR_RETURN(gutil::Version sut_config_version,
                   pdpi::GetPkgInfoVersion(sut.p4rt.get()));
  if (p4_symbolic_config_version != bmv2_config_version) {
    if (params.specification_override.has_value()) {
      LOG(WARNING) << "P4 specification override you provided is inconsistent: "
                      "P4Info versions for p4-symbolic and BMv2 do not match: "
                   << p4_symbolic_config_version << " vs "
                   << bmv2_config_version;
    } else {
      return gutil::InternalErrorBuilder()
             << "P4 specification inferred by DVaaS backend is inconsistent: "
                "P4Info versions for p4-symbolic and BMv2 do not match: "
             << p4_symbolic_config_version << " vs " << bmv2_config_version;
    }
  }
  if (bmv2_config_version != sut_config_version) {
    if (params.specification_override.has_value()) {
      LOG(WARNING) << "P4 specification override you provided is inconsistent "
                      "with the P4Info version of the SUT: override version "
                   << p4_symbolic_config_version << " vs SUT version "
                   << sut_config_version;
    } else {
      return gutil::InternalErrorBuilder()
             << "P4 specification inferred by DVaaS backend is inconsistent "
                "with the P4Info version of the SUT: inferred version "
             << p4_symbolic_config_version << " vs SUT version"
             << sut_config_version;
    }
  }
  return p4_spec;
}

absl::StatusOr<std::string> GetPacketTraceSummary(
    dvaas::PacketTrace& packet_trace) {
  std::string summarized_packet_trace;

  auto indent = [](std::string_view text) {
    return absl::StrReplaceAll(text, {{"\n", "\n  "}});
  };

  for (const dvaas::Event& event : packet_trace.events()) {
    switch (event.event_case()) {
      case Event::kTableApply: {
        if (event.table_apply().hit().has_table_entry()) {
          absl::StrAppend(&summarized_packet_trace, "Table '",
                          event.table_apply().table_name(), "': hit\n  ",
                          indent(gutil::PrintTextProto(
                              event.table_apply().hit().table_entry())),
                          "\n");
        } else {
          absl::StrAppend(&summarized_packet_trace,
                          indent(event.table_apply().hit_or_miss_textual_log()),
                          "\n\n");
        }
        break;
      }
      case Event::kMarkToDrop: {
        absl::StrAppend(&summarized_packet_trace, "Primitive: 'mark_to_drop' (",
                        event.mark_to_drop().source_location(), ")\n\n");
        break;
      }
      case Event::kPacketReplication: {
        absl::StrAppend(
            &summarized_packet_trace, "Packet replication: ",
            event.packet_replication().number_of_packets_replicated(),
            " replicas\n\n");
        break;
      }
      default: {
        LOG(WARNING) << "Event " << event.ShortDebugString()
                     << " not supported.";
        break;
      }
    }
  }
  return summarized_packet_trace;
}

// Generates and returns test vectors using the backend functions
// `SynthesizePackets` and `GeneratePacketTestVectors`. Reads the table entries,
// P4Info, and relevant P4RT port IDs from the switch.
absl::StatusOr<GenerateTestVectorsResult> GenerateTestVectors(
    const DataplaneValidationParams& params, SwitchApi& sut,
    DataplaneValidationBackend& backend, gutil::TestArtifactWriter& writer) {
  // Determine the P4 specification to test against.
  ASSIGN_OR_RETURN(P4Specification p4_spec,
                   InferP4Specification(params, backend, sut));
  RETURN_IF_ERROR(writer.AppendToTestArtifact(
      "sut_p4_symbolic_config.txt", p4_spec.p4_symbolic_config.DebugString()));
  RETURN_IF_ERROR(writer.AppendToTestArtifact(
      "sut_bmv2_config.txt", p4_spec.bmv2_config.DebugString()));

  ASSIGN_OR_RETURN(pdpi::IrP4Info ir_p4info, pdpi::GetIrP4Info(*sut.p4rt));

  // Read P4Info and control plane entities from SUT, sorted for determinism.
  ASSIGN_OR_RETURN(pdpi::IrEntities entities,
                   pdpi::ReadIrEntitiesSorted(*sut.p4rt));
  // Retrieve auxiliary entries for v1model targets.
  ASSIGN_OR_RETURN(
      pdpi::IrEntities v1model_auxiliary_table_entries,
      backend.CreateV1ModelAuxiliaryEntities(entities, ir_p4info, *sut.gnmi));

  RETURN_IF_ERROR(writer.AppendToTestArtifact(
      "v1model_auxiliary_table_entries.txt",
      gutil::PrintTextProto(v1model_auxiliary_table_entries)));

  entities.MergeFrom(v1model_auxiliary_table_entries);

  RETURN_IF_ERROR(
      writer.AppendToTestArtifact("ir_entities_used_in_packet_synthesis.txt",
                                  absl::StrCat(gutil::PrintTextProto(entities),
                                               std::string(80, '-'), "\n")));

  // Get enabled Ethernet ports from SUT's GNMI config.
  ASSIGN_OR_RETURN(std::vector<pins_test::P4rtPortId> ports,
                   pins_test::GetMatchingP4rtPortIds(
                       *sut.gnmi, pins_test::IsEnabledEthernetInterface));
  if (ports.empty()) {
    return absl::InvalidArgumentError("Set of available P4RT ports is empty");
  }
  const P4rtPortId& default_ingress_port = ports[0];
  GenerateTestVectorsResult generate_test_vectors_result;

  // Synthesize test packets.
  LOG(INFO) << "Synthesizing test packets";
  ASSIGN_OR_RETURN(
      generate_test_vectors_result.packet_synthesis_result,
      backend.SynthesizePackets(
          ir_p4info, entities, p4_spec.p4_symbolic_config, ports,
          [&](absl::string_view stats) {
            return writer.AppendToTestArtifact("test_packet_stats.txt", stats);
          },
          params.coverage_goals_override, params.packet_synthesis_time_limit));

  RETURN_IF_ERROR(writer.AppendToTestArtifact(
      "synthesized_packets.txt",
      ToString(generate_test_vectors_result.packet_synthesis_result
                   .synthesized_packets)));

  // Generate test vectors with output prediction from the synthesized
  // packets.
  LOG(INFO) << "Generating test vectors with output prediction";
  ASSIGN_OR_RETURN(generate_test_vectors_result.packet_test_vector_by_id,
                   backend.GeneratePacketTestVectors(
                       ir_p4info, entities, p4_spec.bmv2_config, ports,
                       generate_test_vectors_result.packet_synthesis_result
                           .synthesized_packets,
                       default_ingress_port));

  RETURN_IF_ERROR(writer.AppendToTestArtifact(
      "generated_test_vectors.txt",
      ToString(generate_test_vectors_result.packet_test_vector_by_id)));

  return generate_test_vectors_result;
}

absl::Status AttachPacketTrace(
    dvaas::PacketTestOutcome& failed_packet_test,
    absl::btree_map<std::string, std::vector<dvaas::PacketTrace>>&
        packet_traces,
    gutil::TestArtifactWriter& dvaas_test_artifact_writer) {
  // Store the full BMv2 textual log as test artifact.
  const std::string& packet_hex =
      failed_packet_test.test_run().test_vector().input().packet().hex();
  ASSIGN_OR_RETURN(int test_id,
                   dvaas::ExtractIdFromTaggedPacketInHex(packet_hex));
  const std::string filename =
      "packet_" + std::to_string(test_id) + ".trace.txt";
  RETURN_IF_ERROR(dvaas_test_artifact_writer.AppendToTestArtifact(
      filename, packet_traces[packet_hex][0].bmv2_textual_log()));

  auto it = packet_traces.find(packet_hex);
  if (it == packet_traces.end() || it->second.empty()) {
    return absl::InternalError(
        absl::StrCat("Packet trace not found for packet ", packet_hex));
  }

  // Augment failure description with packet trace summary.
  ASSIGN_OR_RETURN(std::string summarized_packet_trace,
                   GetPacketTraceSummary(it->second[0]));
  failed_packet_test.mutable_test_result()->mutable_failure()->set_description(
      absl::StrCat(
          failed_packet_test.test_result().failure().description(),
          "\n== EXPECTED INPUT-OUTPUT TRACE (P4 SIMULATION) SUMMARY"
          " =========================\n",
          "DISCLAIMER: The following trace is produced from a simulation based "
          "on the P4 model of the switch. Its sole purpose is to explain why "
          "the test expects the output it expects. It does NOT necessarily "
          "represent the behavior of the actual hardware under test. ",
          "Moreover, this is a summary of the full trace and does not contain "
          "all details. The full trace can be found in '",
          filename, "'.\n\n", summarized_packet_trace));

  return absl::OkStatus();
}

absl::Status PostProcessTestVectorFailure(
    const DataplaneValidationParams& params,
    const PacketInjectionParams& packet_injection_params, int failure_count,
    SwitchApi& sut_api, SwitchApi& control_switch_api,
    dvaas::PacketTestOutcome& test_outcome,
    absl::btree_map<std::string, std::vector<dvaas::PacketTrace>>&
        packet_traces,
    gutil::TestArtifactWriter& dvaas_test_artifact_writer,
    const std::function<absl::StatusOr<ValidationResult>(
        const SynthesizedPacket& synthesized_packet,
        pdpi::IrEntities& ir_entities)>
        test_and_validate_callback) {
  // Duplicate packet that caused test failure.
  if (failure_count <
      params.failure_enhancement_options.max_failures_to_attempt_to_replicate) {
    RETURN_IF_ERROR(DetermineReproducibilityRate(
        params, packet_injection_params, *sut_api.p4rt,
        *control_switch_api.p4rt, test_outcome));
  }

  // Only try to minimize the set of entities when the failure is perfectly
  // reproducible.
  if (test_outcome.test_result()
              .failure()
              .minimization_analysis()
              .reproducibility_rate() == 1.0 &&
      failure_count < params.failure_enhancement_options
                          .max_number_of_failures_to_minimize) {
    RETURN_IF_ERROR(MinimizePacketTestVectors(sut_api, test_outcome,
                                              test_and_validate_callback))
            .SetPrepend()
        << "When minimizing failure: ";
  }

  // Print packet traces.
  if (params.failure_enhancement_options.collect_packet_trace) {
    RETURN_IF_ERROR(AttachPacketTrace(test_outcome, packet_traces,
                                      dvaas_test_artifact_writer));
  }
  return absl::OkStatus();
}

absl::Status IncreasePerEntryRateLimitsToAvoidBogusDrops(
    const std::vector<p4::v1::Entity>& original_entities, SwitchApi& sut) {
  ASSIGN_OR_RETURN(gutil::Version switch_p4_version,
                   pdpi::GetPkgInfoVersion(sut.p4rt.get()));
  ASSIGN_OR_RETURN(
      gutil::Version minimum_version,
      gutil::ParseVersion(SAI_P4_PKGINFO_VERSION_METER_CONFIG_USES_INT64));

  // TODO: Remove when backwards compatibility is no longer
  // required.
  if (switch_p4_version < minimum_version) return absl::OkStatus();

  // Loop through the entities and modify those with MeterConfigs such that
  // the MeterConfig has 1000Gbps as the rate limit and 128Mb as the burst
  // limit.
  constexpr int64_t kHighRateLimit = 125000000000;
  constexpr int64_t kHighBurstLimit = 16000000;
  std::vector<p4::v1::Update> pi_updates;

  for (const auto& entity : original_entities) {
    if (entity.has_table_entry() && entity.table_entry().has_meter_config()) {
      p4::v1::Update update;
      update.set_type(p4::v1::Update::MODIFY);
      *update.mutable_entity() = entity;
      update.mutable_entity()
          ->mutable_table_entry()
          ->mutable_meter_config()
          ->set_cir(kHighRateLimit);
      update.mutable_entity()
          ->mutable_table_entry()
          ->mutable_meter_config()
          ->set_pir(kHighRateLimit);
      update.mutable_entity()
          ->mutable_table_entry()
          ->mutable_meter_config()
          ->set_cburst(kHighBurstLimit);
      update.mutable_entity()
          ->mutable_table_entry()
          ->mutable_meter_config()
          ->set_pburst(kHighBurstLimit);
      pi_updates.push_back(std::move(update));
    }
  }
  // Send MODIFY updates to the switch.
  return pdpi::SendPiUpdates(sut.p4rt.get(), pi_updates);
}

absl::StatusOr<ValidationResult>
DataplaneValidator::ValidateDataplaneUsingExistingSwitchApis(
    SwitchApi& sut, SwitchApi& control_switch,
    const DataplaneValidationParams& params) {
  // Read all entities.
  ASSIGN_OR_RETURN(std::vector<p4::v1::Entity> original_entities,
                   pdpi::ReadPiEntitiesSorted(*sut.p4rt));

  RETURN_IF_ERROR(
      IncreasePerEntryRateLimitsToAvoidBogusDrops(original_entities, sut));

  // Set up custom writer that prefixes artifact names and adds headers.
  DvaasTestArtifactWriter dvaas_test_artifact_writer(artifact_writer_, params);

  // Configure control switch.
  {
    // Read P4Info from control switch.
    ASSIGN_OR_RETURN(pdpi::IrP4Info ir_info,
                     pdpi::GetIrP4Info(*control_switch.p4rt));

    // Clear control switch entities and install punt entries instead.
    RETURN_IF_ERROR(pdpi::ClearEntities(*control_switch.p4rt));
    ASSIGN_OR_RETURN(pdpi::IrEntities punt_entries,
                     backend_->GetEntitiesToPuntAllPackets(ir_info));
    RETURN_IF_ERROR(
        pdpi::InstallIrEntities(*control_switch.p4rt, punt_entries));
  }

  // Clear counters prior to test packet injection, so the final counters are
  // more meaningful.
  //
  // CAUTION: As of 2024, this is a not supported by SONIC PINS, and behaves as
  // a no-op on such switches.
  RETURN_IF_ERROR(pdpi::ClearTableEntryCounters(*sut.p4rt));

  // Read and store table entries on SUT as an artifact.
  ASSIGN_OR_RETURN(pdpi::IrEntities entities,
                   pdpi::ReadIrEntitiesSorted(*sut.p4rt));
  RETURN_IF_ERROR(dvaas_test_artifact_writer.AppendToTestArtifact(
      "sut_ir_entities.pre_packet_injection.txtpb",
      gutil::PrintTextProto(entities)));

  // Store port mapping as an artifact (identity if not given a value).
  MirrorTestbedP4rtPortIdMap mirror_testbed_port_map =
      params.mirror_testbed_port_map_override.has_value()
          ? *params.mirror_testbed_port_map_override
          : MirrorTestbedP4rtPortIdMap::CreateIdentityMap();
  RETURN_IF_ERROR(CheckAndStoreMappedAndUnmappedPortIds(
      mirror_testbed_port_map, *sut.gnmi, *control_switch.gnmi,
      dvaas_test_artifact_writer));

  // Generate test vectors.
  GenerateTestVectorsResult generate_test_vectors_result;
  PacketTestVectorById& test_vectors =
      generate_test_vectors_result.packet_test_vector_by_id;
  if (params.packet_test_vector_override.empty()) {
    LOG(INFO) << "Auto-generating test vectors";
    ASSIGN_OR_RETURN(generate_test_vectors_result,
                     GenerateTestVectors(params, sut, *backend_,
                                         dvaas_test_artifact_writer));
  } else {
    LOG(INFO) << "Checking user-provided test vectors for well-formedness";
    ASSIGN_OR_RETURN(pdpi::IrP4Info ir_info, pdpi::GetIrP4Info(*sut.p4rt));
    ASSIGN_OR_RETURN(test_vectors,
                     LegitimizeUserProvidedTestVectors(
                         params.packet_test_vector_override, ir_info));
  }
  RETURN_IF_ERROR(dvaas_test_artifact_writer.AppendToTestArtifact(
      "test_vectors.txt", ToString(test_vectors)));

  PacketInjectionParams packet_injection_params = {
      .max_packets_to_send_per_second = params.max_packets_to_send_per_second,
      .is_expected_unsolicited_packet = [&](const packetlib::Packet packet)
          -> bool { return backend_->IsExpectedUnsolicitedPacket(packet); },
      .mirror_testbed_port_map = mirror_testbed_port_map,
  };

  // Send tests to switch and collect results.
  ASSIGN_OR_RETURN(PacketTestRuns test_runs,
                   SendTestPacketsAndCollectOutputs(
                       *sut.p4rt.get(), *control_switch.p4rt.get(),
                       test_vectors, packet_injection_params,
                       packet_statistics_));
  const absl::Time kTimeLastPacketInjected = absl::Now();
  RETURN_IF_ERROR(dvaas_test_artifact_writer.AppendToTestArtifact(
      "test_runs.textproto", gutil::PrintTextProto(test_runs)));

  // Validate test runs to create test outcomes.
  dvaas::PacketTestOutcomes test_outcomes;
  test_outcomes.mutable_outcomes()->Reserve(test_runs.test_runs_size());
  for (const auto& test_run : test_runs.test_runs()) {
    dvaas::PacketTestOutcome& test_outcome = *test_outcomes.add_outcomes();
    *test_outcome.mutable_test_run() = test_run;
    *test_outcome.mutable_test_result() =
        ValidateTestRun(test_run, params.switch_output_diff_params);
  }

  // Store the packet trace for all failed test outcomes.
  ASSIGN_OR_RETURN(P4Specification p4_spec,
                   InferP4Specification(params, *backend_, sut));
  ASSIGN_OR_RETURN(pdpi::IrP4Info ir_p4info, pdpi::GetIrP4Info(*sut.p4rt));
  std::vector<SwitchInput> failed_switch_inputs;
  for (const dvaas::PacketTestOutcome& test_outcome :
       test_outcomes.outcomes()) {
    if (test_outcome.test_result().has_failure()) {
      failed_switch_inputs.push_back(
          test_outcome.test_run().test_vector().input());
    }
  }
  if (!failed_switch_inputs.empty()) {
    absl::btree_map<std::string, std::vector<dvaas::PacketTrace>> packet_traces;
    if (params.failure_enhancement_options.collect_packet_trace) {
      LOG(INFO) << "Storing packet traces for failed test packets";

      // Read P4Info and control plane entities from SUT, sorted for
      // determinism.
      ASSIGN_OR_RETURN(pdpi::IrEntities v1model_augmented_entities,
                       pdpi::ReadIrEntitiesSorted(*sut.p4rt));
      // Retrieve auxiliary entries for v1model targets.
      ASSIGN_OR_RETURN(pdpi::IrEntities v1model_auxiliary_table_entries,
                       backend_->CreateV1ModelAuxiliaryEntities(
                           v1model_augmented_entities, ir_p4info, *sut.gnmi));
      v1model_augmented_entities.MergeFrom(v1model_auxiliary_table_entries);

      ASSIGN_OR_RETURN(packet_traces,
                       backend_->GetPacketTraces(p4_spec.bmv2_config, ir_p4info,
                                                 v1model_augmented_entities,
                                                 failed_switch_inputs));
    } else {
      LOG(INFO) << "Skipping packet trace collection for failed test packets";
    }

    int current_failures_count = 0;
    // Rerun at most `num_failures_to_rerun` to avoid timeouts if there are too
    // many failures.
    for (dvaas::PacketTestOutcome& test_outcome :
         *test_outcomes.mutable_outcomes()) {
      if (test_outcome.test_result().has_failure()) {
        // Tolerate failures.
        // Remove once packet trace, replication, and
        // minimization code is stably integrated.
        absl::Status status = PostProcessTestVectorFailure(
            params, packet_injection_params, current_failures_count++, sut,
            control_switch, test_outcome, packet_traces,
            dvaas_test_artifact_writer,
            /*test_and_validate_callback=*/
            [&](const SynthesizedPacket& synthesized_packet,
                pdpi::IrEntities& ir_entities)
                -> absl::StatusOr<ValidationResult> {
              std::string_view packet_port =
                  test_outcome.test_run().test_vector().input().packet().port();
              ASSIGN_OR_RETURN(pins_test::P4rtPortId default_ingress_port,
                               P4rtPortId::MakeFromP4rtEncoding(packet_port));

              // Retrieve auxiliary entries for v1model targets.
              ASSIGN_OR_RETURN(pdpi::IrEntities v1model_auxiliary_table_entries,
                               backend_->CreateV1ModelAuxiliaryEntities(
                                   ir_entities, ir_p4info, *sut.gnmi));
              ir_entities.MergeFrom(v1model_auxiliary_table_entries);

              // Get enabled Ethernet ports from SUT's GNMI config.
              ASSIGN_OR_RETURN(
                  std::vector<pins_test::P4rtPortId> ports,
                  pins_test::GetMatchingP4rtPortIds(
                      *sut.gnmi, pins_test::IsEnabledEthernetInterface));
              std::vector<p4_symbolic::packet_synthesizer::SynthesizedPacket>
                  synthesized_packets = {synthesized_packet};
              // TODO: Move to using `ValidateDataplane` once the
              // bug is fixed.
              ASSIGN_OR_RETURN(
                  PacketTestVectorById test_vectors,
                  backend_->GeneratePacketTestVectors(
                      ir_p4info, ir_entities, p4_spec.bmv2_config, ports,
                      synthesized_packets, default_ingress_port));

              // Send packets to the switch and collect results.
              PacketStatistics statistics;
              ASSIGN_OR_RETURN(
                  PacketTestRuns test_runs,
                  SendTestPacketsAndCollectOutputs(
                      *sut.p4rt, *control_switch.p4rt, test_vectors,
                      packet_injection_params, statistics,
                      /*log_injection_progress=*/false));
              // Validate test runs to create test outcomes.
              return ValidationResult(test_runs,
                                      params.switch_output_diff_params,
                                      /*packet_synthesis_result=*/{});
            });
        if (!status.ok()) {
          LOG(WARNING) << "Got error when post-processing failure: "
                       << status.message();
        }
      }
    }
  }

  ValidationResult validation_result(
      std::move(test_outcomes),
      generate_test_vectors_result.packet_synthesis_result);
  RETURN_IF_ERROR(dvaas_test_artifact_writer.AppendToTestArtifact(
      "test_vector_failures.txt",
      absl::StrJoin(validation_result.GetAllFailures(), "\n\n")));

  // We read and store all table entries at the very end of the test. This is
  // useful, e.g., for checking per-entry ACL counters when debugging.
  {
    // The hardware-level counters are only queried every <= 20 seconds on the
    // switch for performance reasons, so we need to wait to ensure we get the
    // latest values.
    const absl::Time kTimeCountersConverged =
        kTimeLastPacketInjected + absl::Seconds(20);
    const absl::Duration kTimeUntilCountersConverged =
        kTimeCountersConverged - absl::Now();
    if (kTimeUntilCountersConverged > absl::ZeroDuration()) {
      LOG(INFO) << "sleeping " << kTimeUntilCountersConverged
                << " to allow per-entry counters to converge";
      absl::SleepFor(kTimeUntilCountersConverged);
    }

    ASSIGN_OR_RETURN(pdpi::IrEntities entities,
                     pdpi::ReadIrEntitiesSorted(*sut.p4rt));
    RETURN_IF_ERROR(dvaas_test_artifact_writer.AppendToTestArtifact(
        "sut_ir_entities.post_packet_injection.txtpb",
        gutil::PrintTextProto(entities)));
  }

  // After the validation, reinstall the original entities with the original
  // meter configs.
  RETURN_IF_ERROR(pdpi::ClearEntities(*sut.p4rt));
  RETURN_IF_ERROR(pdpi::InstallPiEntities(*sut.p4rt, original_entities));

  return validation_result;
}

absl::StatusOr<ValidationResult> DataplaneValidator::ValidateDataplane(
    thinkit::MirrorTestbed& testbed, const DataplaneValidationParams& params) {
  // Set up connections.
  SwitchApi sut, control_switch;
  ASSIGN_OR_RETURN(sut.p4rt, pdpi::P4RuntimeSession::Create(testbed.Sut()));
  ASSIGN_OR_RETURN(sut.gnmi, testbed.Sut().CreateGnmiStub());

  ASSIGN_OR_RETURN(control_switch.p4rt,
                   pdpi::P4RuntimeSession::Create(testbed.ControlSwitch()));
  ASSIGN_OR_RETURN(control_switch.gnmi,
                   testbed.ControlSwitch().CreateGnmiStub());

  std::optional<pins_test::openconfig::Interfaces> original_control_interfaces;
  if (!params.mirror_testbed_port_map_override.has_value()) {
    // TODO: Infer port ID mapping from mirror testbed interface
    // names instead of changing control switch's port configuration.

    // Store the original control switch gNMI interface config before changing
    // it.
    ASSIGN_OR_RETURN(original_control_interfaces,
                     pins_test::GetInterfacesAsProto(*control_switch.gnmi,
                                                     gnmi::GetRequest::CONFIG));
    // Set up control switch to be a mirror of SUT.
    RETURN_IF_ERROR(pdpi::ClearEntities(*sut.p4rt));
    // Mirror testbed ports.
    RETURN_IF_ERROR(
        pins_test::MirrorSutP4rtPortIdConfigToControlSwitch(testbed));

    // Ensure that all enabled ports are up for control switch.
    RETURN_IF_ERROR(
        pins_test::WaitForEnabledInterfacesToBeUp(testbed.ControlSwitch()))
            .SetPrepend()
        << "expected enabled interfaces on control switch to be up: ";
  }

  // Ensure that all enabled ports are up for SUT.
  RETURN_IF_ERROR(pins_test::WaitForEnabledInterfacesToBeUp(testbed.Sut()))
          .SetPrepend()
      << "expected enabled interfaces on SUT to be up: ";

  // Do not return on error in order to restore the original control switch
  // gNMI interface config's P4RT IDs.
  absl::StatusOr<ValidationResult> result =
      ValidateDataplaneUsingExistingSwitchApis(sut, control_switch, params);

  if (original_control_interfaces.has_value()) {
    RETURN_IF_ERROR(pins_test::SetInterfaceP4rtIds(
        *control_switch.gnmi, *original_control_interfaces));
  }
  return result;
}

}  // namespace dvaas
