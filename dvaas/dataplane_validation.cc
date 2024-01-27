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

#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "dvaas/output_writer.h"
#include "dvaas/packet_injection.h"
#include "dvaas/port_id_map.h"
#include "dvaas/switch_api.h"
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
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/p4_runtime_session_extras.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesizer.pb.h"
#include "proto/gnmi/gnmi.pb.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "thinkit/mirror_testbed.h"

namespace dvaas {
namespace {

using ::p4_symbolic::packet_synthesizer::SynthesizedPacket;
using ::pins_test::P4rtPortId;

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

// Determines the P4 specification DVaaS should use, and performs some sanity
// checks to ensure the specification is compatible with the SUT.
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

}  // namespace

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

  // Read P4Info and control plane entities from SUT, sorted for determinism.
  ASSIGN_OR_RETURN(pdpi::IrP4Info ir_p4info, pdpi::GetIrP4Info(*sut.p4rt));
  ASSIGN_OR_RETURN(pdpi::IrEntities entities,
                   pdpi::ReadIrEntitiesSorted(*sut.p4rt));

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
  ASSIGN_OR_RETURN(generate_test_vectors_result.packet_synthesis_result,
                   backend.SynthesizePackets(
                       ir_p4info, entities, p4_spec.p4_symbolic_config, ports,
                       [&](absl::string_view stats) {
                         return writer.AppendToTestArtifact(
                             "test_packet_stats.txt", stats);
                       },
                       params.packet_synthesis_time_limit));

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

  return generate_test_vectors_result;
}

absl::StatusOr<ValidationResult> DataplaneValidator::ValidateDataplane(
    SwitchApi& sut, SwitchApi& control_switch,
    const DataplaneValidationParams& params) {
  // Set up custom writer that prefixes artifact names and adds headers.
  std::unique_ptr<gutil::TestArtifactWriter> writer =
      std::make_unique<DvaasTestArtifactWriter>(artifact_writer_, params);

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

  // Read and store table entries on SUT as an artifact.
  ASSIGN_OR_RETURN(pdpi::IrEntities entities,
                   pdpi::ReadIrEntitiesSorted(*sut.p4rt));
  RETURN_IF_ERROR(writer->AppendToTestArtifact(
      "sut_ir_entities.txtpb", gutil::PrintTextProto(entities)));

  // Store port mapping as an artifact (identity if not given a value).
  MirrorTestbedP4rtPortIdMap mirror_testbed_port_map =
      params.mirror_testbed_port_map_override.has_value()
          ? *params.mirror_testbed_port_map_override
          : MirrorTestbedP4rtPortIdMap::CreateIdentityMap();
  RETURN_IF_ERROR(CheckAndStoreMappedAndUnmappedPortIds(
      mirror_testbed_port_map, *sut.gnmi, *control_switch.gnmi, *writer));

  // Generate test vectors.
  GenerateTestVectorsResult generate_test_vectors_result;
  PacketTestVectorById& test_vectors =
      generate_test_vectors_result.packet_test_vector_by_id;
  if (params.packet_test_vector_override.empty()) {
    LOG(INFO) << "Auto-generating test vectors";
    ASSIGN_OR_RETURN(generate_test_vectors_result,
                     GenerateTestVectors(params, sut, *backend_, *writer));
  } else {
    LOG(INFO) << "Checking user-provided test vectors for well-formedness";
    ASSIGN_OR_RETURN(pdpi::IrP4Info ir_info, pdpi::GetIrP4Info(*sut.p4rt));
    ASSIGN_OR_RETURN(test_vectors,
                     LegitimizeUserProvidedTestVectors(
                         params.packet_test_vector_override, ir_info));
  }
  RETURN_IF_ERROR(
      writer->AppendToTestArtifact("test_vectors.txt", ToString(test_vectors)));

  // Send tests to switch and collect results.
  ASSIGN_OR_RETURN(
      PacketTestRuns test_runs,
      SendTestPacketsAndCollectOutputs(
          *sut.p4rt.get(), *control_switch.p4rt.get(), test_vectors,
          {
              .max_packets_to_send_per_second =
                  params.max_packets_to_send_per_second,
              .is_expected_unsolicited_packet =
                  [&](const packetlib::Packet packet) -> bool {
                return backend_->IsExpectedUnsolicitedPacket(packet);
              },
              .mirror_testbed_port_map = mirror_testbed_port_map,
          },
          packet_statistics_));
  RETURN_IF_ERROR(writer->AppendToTestArtifact("test_runs.textproto",
                                               test_runs.DebugString()));

  ValidationResult validation_result(
      std::move(test_runs), params.switch_output_diff_params,
      generate_test_vectors_result.packet_synthesis_result);
  RETURN_IF_ERROR(writer->AppendToTestArtifact(
      "test_vector_failures.txt",
      absl::StrJoin(validation_result.GetAllFailures(), "\n\n")));
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
    RETURN_IF_ERROR(pdpi::ClearTableEntries(control_switch.p4rt.get()));
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

  // Do not return on error in order to restore the original control switch gNMI
  // interface config's P4RT IDs.
  absl::StatusOr<ValidationResult> result =
      ValidateDataplane(sut, control_switch, params);

  if (original_control_interfaces.has_value()) {
    RETURN_IF_ERROR(pins_test::SetInterfaceP4rtIds(
        *control_switch.gnmi, *original_control_interfaces));
  }
  return result;
}

}  // namespace dvaas
