// Copyright (c) 2024, Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "dvaas/traffic_generator.h"

#include <memory>
#include <optional>
#include <thread>  // NOLINT: third_party code.
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/synchronization/mutex.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "dvaas/dataplane_validation.h"
#include "dvaas/mirror_testbed_config.h"
#include "dvaas/packet_injection.h"
#include "dvaas/port_id_map.h"
#include "dvaas/switch_api.h"
#include "dvaas/test_vector.pb.h"
#include "dvaas/validation_result.h"
#include "glog/logging.h"
#include "gutil/status.h"
#include "gutil/test_artifact_writer.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/p4_runtime_session_extras.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesizer.pb.h"
#include "thinkit/mirror_testbed_fixture.h"

// Crash if `status` is not okay. Only use in tests.
#define CHECK_OK(val) CHECK_EQ(::absl::OkStatus(), (val))  // Crash OK.

namespace dvaas {

SimpleTrafficGenerator::State SimpleTrafficGenerator::GetState() {
  absl::MutexLock lock(&state_mutex_);
  return state_;
}

void SimpleTrafficGenerator::SetState(State state) {
  absl::MutexLock lock(&state_mutex_);
  state_ = state;
}

absl::StatusOr<PacketSynthesisStats> SimpleTrafficGenerator::Init(
    std::shared_ptr<thinkit::MirrorTestbedInterface> testbed,
    const TrafficGenerator::Params& params) {
  if (GetState() == kTrafficFlowing) {
    return absl::FailedPreconditionError(
        "Cannot initialize while traffic is flowing");
  }

  params_ = params;

  // Configure testbed.
  ASSIGN_OR_RETURN(auto mirror_testbed_configurator,
                   MirrorTestbedConfigurator::Create(testbed));
  testbed_configurator_ = std::make_unique<MirrorTestbedConfigurator>(
      std::move(mirror_testbed_configurator));
  RETURN_IF_ERROR(testbed_configurator_->ConfigureForForwardingTest({
      .mirror_sut_ports_ids_to_control_switch =
          !params_.validation_params.mirror_testbed_port_map_override
               .has_value(),
  }));
  // Install punt entries on control switch.
  // TODO: Use testbed configurator to do this, instead.
  pdpi::P4RuntimeSession& control_p4rt =
      *testbed_configurator_->ControlSwitchApi().p4rt;
  RETURN_IF_ERROR(pdpi::ClearEntities(control_p4rt));
  ASSIGN_OR_RETURN(const pdpi::IrP4Info ir_p4info,
                   pdpi::GetIrP4Info(control_p4rt));
  ASSIGN_OR_RETURN(const pdpi::IrEntities punt_entries,
                   backend_->GetEntitiesToPuntAllPackets(ir_p4info));
  RETURN_IF_ERROR(pdpi::InstallIrEntities(control_p4rt, punt_entries));

  // Generate test vectors.
  gutil::BazelTestArtifactWriter writer;
  ASSIGN_OR_RETURN(
      generate_test_vectors_result_,
      GenerateTestVectors(params.validation_params,
                          testbed_configurator_->SutApi(), *backend_, writer));

  SetState(kInitialized);

  return PacketSynthesisStats{};
}

absl::Status SimpleTrafficGenerator::StartTraffic() {
  State state = GetState();
  if (state == kUninitialized) {
    return absl::FailedPreconditionError(
        "Cannot start traffic before initialization.");
  }
  if (state == kTrafficFlowing) {
    return absl::FailedPreconditionError(
        "Traffic injection has already started");
  }

  // Spawn traffic injection thread.
  traffic_injection_thread_ =
      std::thread(&SimpleTrafficGenerator::InjectTraffic, this);

  // Wait for state to change before returning.
  while (GetState() != kTrafficFlowing) {
    absl::SleepFor(absl::Seconds(1));
  }

  return absl::OkStatus();
}

absl::Status SimpleTrafficGenerator::StopTraffic() {
  if (GetState() != kTrafficFlowing) {
    return absl::FailedPreconditionError(
        "Cannot stop traffic if not already flowing.");
  }

  // Change state.
  SetState(kInitialized);

  // Wait for traffic injection thread to stop before returning.
  traffic_injection_thread_.join();

  return absl::OkStatus();
}

void SimpleTrafficGenerator::InjectTraffic() {
  // Change state.
  SetState(kTrafficFlowing);

  LOG(INFO) << "Starting to inject traffic";
  int iterations = 0;
  while (GetState() == kTrafficFlowing) {
    ++iterations;
    LOG_EVERY_T(INFO, 10) << "Traffic injection iteration #" << iterations;

    // Inject and collect.
    PacketStatistics statistics;
    absl::StatusOr<PacketTestRuns> test_runs = SendTestPacketsAndCollectOutputs(
        *testbed_configurator_->SutApi().p4rt,
        *testbed_configurator_->ControlSwitchApi().p4rt,
        generate_test_vectors_result_.packet_test_vector_by_id,
        {
            .max_packets_to_send_per_second =
                params_.validation_params.max_packets_to_send_per_second,
            .mirror_testbed_port_map =
                params_.validation_params.mirror_testbed_port_map_override
                    .value_or(MirrorTestbedP4rtPortIdMap::CreateIdentityMap()),
        },
        statistics);
    CHECK_OK(test_runs.status());  // Crash OK.

    // Add results to test_runs_.
    absl::MutexLock lock(&test_runs_mutex_);
    test_runs_.mutable_test_runs()->Add(test_runs->test_runs().begin(),
                                        test_runs->test_runs().end());
  }

  LOG(INFO) << "Stopped traffic injection";
}

absl::StatusOr<ValidationResult> SimpleTrafficGenerator::GetValidationResult() {
  test_runs_mutex_.Lock();
  PacketTestRuns test_runs = test_runs_;
  test_runs_mutex_.Unlock();
  return ValidationResult(
      test_runs, params_.validation_params.switch_output_diff_params,
      generate_test_vectors_result_.packet_synthesis_result);
}

absl::StatusOr<ValidationResult>
SimpleTrafficGenerator::GetAndClearValidationResult() {
  test_runs_mutex_.Lock();
  PacketTestRuns test_runs = test_runs_;
  test_runs_.clear_test_runs();
  test_runs_mutex_.Unlock();

  return ValidationResult(
      test_runs, params_.validation_params.switch_output_diff_params,
      generate_test_vectors_result_.packet_synthesis_result);
}

}  // namespace dvaas
