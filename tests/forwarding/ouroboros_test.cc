// Copyright 2025 Google LLC
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

#include "tests/forwarding/ouroboros_test.h"

#include <memory>
#include <optional>
#include <string>
#include <tuple>
#include <utility>

#include "absl/log/log.h"
#include "absl/random/random.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "dvaas/dataplane_validation.h"
#include "dvaas/packet_injection.h"
#include "dvaas/switch_api.h"
#include "dvaas/validation_result.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status.h"  // IWYU pragma: keep
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"  // IWYU pragma: keep
#include "lib/gnmi/gnmi_helper.h"
#include "lib/gnmi/openconfig.pb.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_fuzzer/annotation_util.h"
#include "p4_fuzzer/fuzz_util.h"
#include "p4_fuzzer/fuzzer.pb.h"
#include "p4_fuzzer/fuzzer_config.h"
#include "p4_fuzzer/switch_state.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4_infra/p4_pdpi/p4_runtime_session_extras.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.pb.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/test_environment.h"

namespace pins_test {
namespace {

using ::dvaas::SwitchApi;
using ::p4_fuzzer::FuzzerConfig;

// -- Auxiliary functions ------------------------------------------------------

std::string CreateHeader(absl::string_view title) {
  return absl::StrCat(std::string(80, '#'), "\n### ", title, "\n",
                      std::string(80, '#'), "\n");
}

// Reads table entries on `sut` and outputs them into an artifact given by
// `artifact_name`.
absl::Status OutputTableEntriesToArtifact(SwitchApi& sut,
                                          thinkit::TestEnvironment& environment,
                                          absl::string_view artifact_name,
                                          int iteration) {
  RETURN_IF_ERROR(environment.AppendToTestArtifact(
      artifact_name,
      CreateHeader(absl::StrCat("Entries after iteration ", iteration))));
  // Read sorted entries back (for determinism) and store in an artifact.
  ASSIGN_OR_RETURN(pdpi::IrTableEntries entries,
                   pdpi::ReadIrTableEntriesSorted(*sut.p4rt));
  return environment.AppendToTestArtifact(artifact_name, entries.DebugString());
}

// Augments the given FuzzerConfig to fit the `sut` and Ouroboros Test by
// replacing the IrP4Info and available ports with those read from the switch
// and setting mutation probability to 0.
absl::Status AugmentFuzzerConfig(SwitchApi& sut, FuzzerConfig& fuzzer_config) {
  ASSIGN_OR_RETURN(p4::v1::GetForwardingPipelineConfigResponse response,
                   pdpi::GetForwardingPipelineConfig(sut.p4rt.get()));

  RETURN_IF_ERROR(fuzzer_config.SetP4Info(response.config().p4info()));
  ASSIGN_OR_RETURN(auto port_ids,
                   pins_test::GetMatchingP4rtPortIds(
                       *sut.gnmi, pins_test::IsEnabledEthernetInterface));
  fuzzer_config.SetPorts(port_ids);
  fuzzer_config.SetMutateUpdateProbability(0.0);
  fuzzer_config.SetNoEmptyActionProfileGroups(true);
  return absl::OkStatus();
}

// Creates connections to the SUT and Control switch and configures them with a
// `gnmi_config` and `p4info` (if given).
// If `mirror_sut_ports_to_control_switch` is true then it mirrors the SUTs
// interfaces on the control switch.
// Either way, the function waits for the enabled interfaces to be Up.
// Returns a configured (SUT, Control Switch) pair.
absl::StatusOr<std::pair<SwitchApi, SwitchApi>> ConfigureMirrorTestbed(
    thinkit::MirrorTestbed& testbed, bool mirror_sut_ports_to_control_switch,
    std::optional<std::string> gnmi_config,
    std::optional<p4::config::v1::P4Info> p4info) {
  // Configure both switches and set up gNMI and P4Runtime sessions to them.
  SwitchApi sut;
  SwitchApi control_switch;
  ASSIGN_OR_RETURN(sut.gnmi, testbed.Sut().CreateGnmiStub());
  ASSIGN_OR_RETURN(control_switch.gnmi,
                   testbed.ControlSwitch().CreateGnmiStub());
  // TODO: Update to use whole ForwardingPipelineConfig when the
  // function supports that.
  ASSIGN_OR_RETURN(
      std::tie(sut.p4rt, control_switch.p4rt),
      ConfigureSwitchPairAndReturnP4RuntimeSessionPair(
          testbed.Sut(), testbed.ControlSwitch(), gnmi_config, p4info));

  if (mirror_sut_ports_to_control_switch) {
    // Mirror testbed ports.
    RETURN_IF_ERROR(MirrorSutP4rtPortIdConfigToControlSwitch(testbed));
    // TODO: Always check that control switch interfaces are up
    // once the model is correctly captured in the gNMI config. I.e. move this
    // to outside of the if-statement.
    RETURN_IF_ERROR(WaitForEnabledInterfacesToBeUp(testbed.ControlSwitch()))
            .SetPrepend()
        << "expected enabled interfaces on control switch to be up: ";
  }

  // Ensure that all enabled ports are up.
  RETURN_IF_ERROR(WaitForEnabledInterfacesToBeUp(testbed.Sut())).SetPrepend()
      << "expected enabled interfaces on SUT to be up: ";

  return std::make_pair(std::move(sut), std::move(control_switch));
}

// -- Main functions -----------------------------------------------------------

// Generates updates to switch state using the P4-Fuzzer and sends them to the
// switch.
absl::Status FuzzSwitchState(absl::BitGen& gen, SwitchApi& sut,
                             thinkit::TestEnvironment& environment,
                             int iteration, const FuzzerConfig& fuzzer_config,
                             int min_num_updates,
                             p4_fuzzer::SwitchState& state) {
  int num_updates = 0;
  int num_fuzzing_cycles = 0;
  while (num_updates < min_num_updates) {
    num_fuzzing_cycles++;
    p4_fuzzer::AnnotatedWriteRequest annotated_request =
        p4_fuzzer::FuzzWriteRequest(&gen, fuzzer_config, state);
    p4::v1::WriteRequest request =
        p4_fuzzer::RemoveAnnotations(annotated_request);
    num_updates += request.updates_size();

    // Send to switch.
    ASSIGN_OR_RETURN(pdpi::IrWriteRpcStatus response,
                     pdpi::SendPiUpdatesAndReturnPerUpdateStatus(
                         *sut.p4rt, request.updates()));

    RETURN_IF_ERROR(p4_fuzzer::OutputInterleavedRequestAndResponseToArtifact(
        environment, /*artifact_name=*/"ouroboros_requests_and_responses.txt",
        /*identifying_prefix=*/
        absl::StrCat("Iteration ", iteration, ".", num_fuzzing_cycles),
        annotated_request, response));

    // Update the switch state to reflect any accepted updates.
    for (int i = 0; i < request.updates_size(); ++i) {
      if (response.rpc_response().statuses(i).code() == google::rpc::OK) {
        RETURN_IF_ERROR(state.ApplyUpdate(request.updates(i)));
      }
    }
  }

  constexpr absl::string_view kSwitchStateArtifactName =
      "ouroboros_switch_state_after_iterations.txt";
  RETURN_IF_ERROR(environment.AppendToTestArtifact(
      kSwitchStateArtifactName,
      CreateHeader(absl::StrCat("SwitchState after iteration ", iteration))));
  RETURN_IF_ERROR(environment.AppendToTestArtifact(kSwitchStateArtifactName,
                                                   state.SwitchStateSummary()));
  RETURN_IF_ERROR(
      environment.AppendToTestArtifact(kSwitchStateArtifactName, "\n\n"));
  return absl::OkStatus();
}

TEST_P(
    OuroborosTest,
    SwitchUnderTestConformsToP4ModelUnderSyntheticStreamOfEntriesAndPackets) {
  thinkit::MirrorTestbed& testbed =
      GetParam().mirror_testbed->GetMirrorTestbed();
  thinkit::TestEnvironment& environment = testbed.Environment();

  // Get the start time to determine when to stop the test.
  const absl::Time deadline = absl::Now() + GetParam().target_test_time;

  // Empty and unused unless the test mirrors testbed ports.
  pins_test::openconfig::Interfaces original_control_interfaces;
  if (!GetParam().dvaas_params.mirror_testbed_port_map_override.has_value()) {
    // Store the original control switch gNMI interface config before changing
    // it.
    // WARNING: This may fail if a gNMI config has not been pushed.
    ASSERT_OK_AND_ASSIGN(
        std::unique_ptr<gnmi::gNMI::StubInterface> control_gnmi_stub,
        testbed.ControlSwitch().CreateGnmiStub());
    ASSERT_OK_AND_ASSIGN(original_control_interfaces,
                         pins_test::GetInterfacesAsProto(
                             *control_gnmi_stub, gnmi::GetRequest::CONFIG));
  }

  std::optional<p4::config::v1::P4Info> p4info =
      GetParam().config.has_value()
          ? std::make_optional(GetParam().config->p4info())
          : std::nullopt;

  if (!p4info.has_value()) {
    LOG(INFO)
        << "Not pushing a P4Info to either switch and instead assuming "
           "they have one. Both switches' P4Infos are stored as artifacts.";
  }

  SwitchApi sut, control_switch;
  ASSERT_OK_AND_ASSIGN(
      std::tie(sut, control_switch),
      ConfigureMirrorTestbed(
          testbed,
          /*mirror_sut_ports_to_control_switch=*/
          !GetParam().dvaas_params.mirror_testbed_port_map_override.has_value(),
          GetParam().gnmi_config, p4info));

  {  // Log P4Infos for debugging purposes.
    ASSERT_OK_AND_ASSIGN(auto sut_ir_p4info, pdpi::GetIrP4Info(*sut.p4rt));
    ASSERT_OK_AND_ASSIGN(auto control_switch_ir_p4info,
                         pdpi::GetIrP4Info(*control_switch.p4rt));
    ASSERT_OK(environment.AppendToTestArtifact("sut_initial_ir_p4info.txt",
                                               sut_ir_p4info.DebugString()));
    ASSERT_OK(environment.AppendToTestArtifact(
        "control_switch_initial_ir_p4info.txt",
        control_switch_ir_p4info.DebugString()));
  }

  // Set up SUT with initial entries.
  ASSERT_OK(
      pdpi::InstallIrEntities(*sut.p4rt, GetParam().initial_sut_entities));

  FuzzerConfig fuzzer_config = GetParam().fuzzer_config;
  ASSERT_OK(AugmentFuzzerConfig(sut, fuzzer_config));
  p4_fuzzer::SwitchState fuzzer_switch_state(fuzzer_config.GetIrP4Info());

  absl::BitGen gen;

  LOG(INFO) << "Running Ouroboros for up to " << GetParam().target_test_time
            << " or " << GetParam().max_iterations << " iterations.";

  // We keep track of the last iteration time to run the test for as close to
  // `target_test_time` while ensuring we don't go above it. We expect that the
  // next iteration will take no more than 2x the time of the last iteration.
  absl::Duration last_iteration_time = absl::ZeroDuration();
  int iteration = 0;
  while (iteration < GetParam().max_iterations &&
         deadline - absl::Now() > 2 * last_iteration_time) {
    iteration++;
    SCOPED_TRACE(absl::StrCat("Iteration: ", iteration));

    absl::Time iteration_start_time = absl::Now();

    ASSERT_OK(FuzzSwitchState(gen, sut, environment, iteration, fuzzer_config,
                              GetParam().min_num_updates_per_loop,
                              fuzzer_switch_state));

    ASSERT_OK(OutputTableEntriesToArtifact(
        sut, environment, /*artifact_name=*/"ouroboros_table_entries.txt",
        iteration));

    // Configure `get_artifact_header` for current iteration.
    dvaas::DataplaneValidationParams dvaas_params = GetParam().dvaas_params;

    dvaas_params.get_artifact_header = [=]() {
      std::string iteration_header =
          CreateHeader(absl::StrCat("Iteration ", iteration));
      if (dvaas_params.get_artifact_header.has_value()) {
        return absl::StrCat(iteration_header,
                            (*dvaas_params.get_artifact_header)());
      } else {
        return iteration_header;
      }
    };

    ASSERT_OK_AND_ASSIGN(
        dvaas::ValidationResult validation_result,
        GetParam().validator->ValidateDataplaneUsingExistingSwitchApis(
            sut, control_switch, testbed.Environment(), dvaas_params));
    validation_result.LogStatistics();

    ASSERT_OK(validation_result.HasSuccessRateOfAtLeast(1.0));

    last_iteration_time = absl::Now() - iteration_start_time;
  }

  dvaas::PacketStatistics statistics =
      GetParam().validator->GetCurrentPacketStatistics();

  LOG(INFO) << "Ran for " << iteration << " iterations.";
  LOG(INFO) << "The last iteration took " << last_iteration_time << ".";
  LOG(INFO) << "Total number of packets sent: "
            << statistics.total_packets_injected;
  LOG(INFO) << "Total number of packets forwarded: "
            << statistics.total_packets_forwarded;
  LOG(INFO) << "Total number of packets punted: "
            << statistics.total_packets_punted;
  LOG(INFO) << "Final switch forwarding state is:\n"
            << fuzzer_switch_state.SwitchStateSummary();

  if (!GetParam().dvaas_params.mirror_testbed_port_map_override.has_value()) {
    // Restore the original control switch gNMI interface config's P4RT IDs.
    ASSERT_OK(pins_test::SetInterfaceP4rtIds(*control_switch.gnmi,
                                             original_control_interfaces));
  }
}

}  // namespace

}  // namespace pins_test
