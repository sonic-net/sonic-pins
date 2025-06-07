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

#include "absl/container/btree_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/escaping.h"
#include "absl/strings/string_view.h"
#include "absl/synchronization/mutex.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "dvaas/dataplane_validation.h"
#include "dvaas/mirror_testbed_config.h"
#include "dvaas/packet_injection.h"
#include "dvaas/port_id_map.h"
#include "dvaas/switch_api.h"
#include "dvaas/test_vector.h"
#include "dvaas/test_vector.pb.h"
#include "dvaas/validation_result.h"
#include "glog/logging.h"
#include "gutil/status.h"
#include "gutil/test_artifact_writer.h"
#include "lib/p4rt/p4rt_port.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/p4_runtime_session_extras.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesizer.pb.h"
#include "tests/forwarding/util.h"
#include "thinkit/mirror_testbed.h"

// Crash if `status` is not okay. Only use in tests.
#define CHECK_OK(val) CHECK_EQ(::absl::OkStatus(), (val))  // Crash OK.

namespace dvaas {

// ============================= SimpleTrafficGen ==============================

SimpleTrafficGenerator::State SimpleTrafficGenerator::GetState() {
  absl::MutexLock lock(&state_mutex_);
  return state_;
}

void SimpleTrafficGenerator::SetState(State state) {
  absl::MutexLock lock(&state_mutex_);
  state_ = state;
}

absl::StatusOr<PacketSynthesisStats> SimpleTrafficGenerator::Init(
    thinkit::MirrorTestbed* testbed, const TrafficGenerator::Params& params) {
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
            .is_expected_unsolicited_packet =
                [&](const packetlib::Packet packet) -> bool {
              return backend_->IsExpectedUnsolicitedPacket(packet);
            },
            .mirror_testbed_port_map =
                params_.validation_params.mirror_testbed_port_map_override
                    .value_or(MirrorTestbedP4rtPortIdMap::CreateIdentityMap()),
            .enable_sut_packet_in_collection =
                !params_.validation_params.switch_output_diff_params
                     .treat_expected_and_actual_outputs_as_having_no_packet_ins,
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

SimpleTrafficGenerator::~SimpleTrafficGenerator() {
  if (GetState() == kTrafficFlowing) {
    LOG(WARNING)
        << "SimpleTrafficGenerator destructed while traffic is flowing. "
           "Stopping traffic.";
    absl::Status status = StopTraffic();
    if (!status.ok()) {
      LOG(FATAL) << "Failed to stop traffic: " << status;  // Crash OK.
    }
  }
}

// ======================= TrafficGenWithGuaranteedRate ========================

TrafficGeneratorWithGuaranteedRate::~TrafficGeneratorWithGuaranteedRate() {
  if (GetState() == kTrafficInjectionAndCollection) {
    LOG(ERROR) << "TrafficGeneratorWithGuaranteedRate destructed while traffic "
                  "is flowing with the state: "
               << GetState() << ". Stopping traffic.";
    absl::Status status = StopTraffic();
    if (!status.ok()) {
      LOG(FATAL) << "Failed to stop traffic: " << status;  // Crash OK
    }
  }
  if (GetState() == kTrafficCollection) {
    LOG(FATAL) << "Unexpected kTrafficCollection state in call to "  // Crash OK
                  "destructor of TrafficGeneratorWithGuaranteedRate.";
  }
}

TrafficGeneratorWithGuaranteedRate::State
TrafficGeneratorWithGuaranteedRate::GetState() {
  absl::MutexLock lock(&state_mutex_);
  return state_;
}

void TrafficGeneratorWithGuaranteedRate::SetState(State state) {
  absl::MutexLock lock(&state_mutex_);
  state_ = state;
}

absl::StatusOr<PacketSynthesisStats> TrafficGeneratorWithGuaranteedRate::Init(
    thinkit::MirrorTestbed* testbed, const TrafficGenerator::Params& params) {
  if (GetState() == kTrafficInjectionAndCollection) {
    return absl::FailedPreconditionError(
        "Cannot initialize while traffic is being injected and collected.");
  }
  if (GetState() == kTrafficCollection) {
    return absl::InternalError(
        "Unexpected kTrafficCollection state in call to Init.");
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

absl::Status TrafficGeneratorWithGuaranteedRate::StartTraffic() {
  State state = GetState();
  if (state == kUninitialized) {
    return absl::FailedPreconditionError(
        "Cannot start traffic before initialization.");
  }
  if (state == kTrafficInjectionAndCollection) {
    return absl::FailedPreconditionError(
        "Traffic injection has already started");
  }
  if (state == kTrafficCollection) {
    return absl::InternalError(
        "Unexpected kTrafficCollection state in call to StartTraffic");
  }

  // Spawn traffic injection thread.
  traffic_injection_thread_ = std::thread([&]() {
    CHECK_OK(  // Crash OK
        TrafficGeneratorWithGuaranteedRate::InjectInputTraffic());
  });

  // Spawn traffic collection thread.
  traffic_collection_thread_ = std::thread([&]() {
    CHECK_OK(  // Crash OK
        TrafficGeneratorWithGuaranteedRate::CollectOutputTraffic());
  });

  // Wait for state to change before returning.
  while (GetState() != kTrafficInjectionAndCollection) {
    absl::SleepFor(absl::Seconds(1));
  }

  return absl::OkStatus();
}

absl::Status TrafficGeneratorWithGuaranteedRate::StopTraffic() {
  if (GetState() != kTrafficInjectionAndCollection) {
    return absl::FailedPreconditionError(
        "Cannot stop traffic if not already flowing.");
  }

  // Change state.
  SetState(kTrafficCollection);

  // Wait for traffic injection thread to stop.
  traffic_injection_thread_.join();

  // Must wait for kMaxPacketInFlightDuration to ensure there are no more
  // in-flight packets after finishing packet injection so they can all be
  // collected and processed.
  absl::SleepFor(kMaxPacketInFlightDuration);

  // Change state.
  SetState(kInitialized);

  // Wait for traffic collection thread to stop.
  traffic_collection_thread_.join();
  return absl::OkStatus();
}

absl::Status TrafficGeneratorWithGuaranteedRate::InjectInputTraffic() {
  // Change state.
  SetState(kTrafficInjectionAndCollection);

  pdpi::P4RuntimeSession& control_switch =
      *testbed_configurator_->ControlSwitchApi().p4rt;
  const PacketTestVectorById& packet_test_vector_by_id =
      generate_test_vectors_result_.packet_test_vector_by_id;
  const MirrorTestbedP4rtPortIdMap mirror_testbed_port_map =
      params_.validation_params.mirror_testbed_port_map_override.value_or(
          MirrorTestbedP4rtPortIdMap::CreateIdentityMap());

  ASSIGN_OR_RETURN(pdpi::IrP4Info control_ir_p4info,
                   GetIrP4Info(control_switch));

  // Compute per packet injection delay.
  std::optional<absl::Duration> injection_delay;
  if (params_.validation_params.max_packets_to_send_per_second.has_value()) {
    injection_delay = absl::Milliseconds(
        1e3 / *params_.validation_params.max_packets_to_send_per_second);
  }

  LOG(INFO) << "Starting to inject traffic";
  int iterations = 0;
  int total_packets_injected = 0;
  while (GetState() == kTrafficInjectionAndCollection) {
    ++iterations;
    LOG_EVERY_T(INFO, 10) << "Traffic injection iteration #" << iterations;

    // Send the packets.
    for (auto [_, packet_test_vector] : packet_test_vector_by_id) {
      int new_tag = packet_tag_id_;
      packet_tag_id_++;
      LOG_EVERY_T(INFO, 10) << "Injecting test packet #" << new_tag;

      if (packet_test_vector.input().type() == SwitchInput::DATAPLANE) {
        // Update tag.
        RETURN_IF_ERROR(UpdateTestTag(packet_test_vector, new_tag));

        // Get corresponding control switch port for the packet's ingress port.
        ASSIGN_OR_RETURN(pins_test::P4rtPortId sut_ingress_port,
                         pins_test::P4rtPortId::MakeFromP4rtEncoding(
                             packet_test_vector.input().packet().port()));
        ASSIGN_OR_RETURN(
            pins_test::P4rtPortId control_switch_port,
            mirror_testbed_port_map.GetControlSwitchPortConnectedToSutPort(
                sut_ingress_port));

        // Inject to egress of control switch.
        RETURN_IF_ERROR(pins::InjectEgressPacket(
            control_switch_port.GetP4rtEncoding(),
            absl::HexStringToBytes(packet_test_vector.input().packet().hex()),
            control_ir_p4info, &control_switch, injection_delay));

        absl::MutexLock lock(&injected_traffic_mutex_);
        injected_traffic_.push_back({
            .tag = new_tag,
            .packet_test_vector = std::move(packet_test_vector),
        });
      } else {
        LOG(ERROR) << "Test vector input type not supported\n"
                   << packet_test_vector.input().DebugString();
      }
    }
    total_packets_injected += packet_test_vector_by_id.size();
  }
  LOG(INFO) << "Stopped traffic injection";
  statistics_.total_packets_injected += total_packets_injected;
  return absl::OkStatus();
}

absl::Status TrafficGeneratorWithGuaranteedRate::CollectOutputTraffic() {
  absl::SleepFor(kMaxPacketInFlightDuration);
  pdpi::P4RuntimeSession& sut = *testbed_configurator_->SutApi().p4rt;
  pdpi::P4RuntimeSession& control_switch =
      *testbed_configurator_->ControlSwitchApi().p4rt;
  bool enable_sut_packet_in_collection =
      !params_.validation_params.switch_output_diff_params
           .treat_expected_and_actual_outputs_as_having_no_packet_ins;
  auto is_expected_unsolicited_packet =
      [&](const packetlib::Packet packet) -> bool {
    return backend_->IsExpectedUnsolicitedPacket(packet);
  };

  MirrorTestbedP4rtPortIdMap mirror_testbed_port_map =
      params_.validation_params.mirror_testbed_port_map_override.value_or(
          MirrorTestbedP4rtPortIdMap::CreateIdentityMap());

  ASSIGN_OR_RETURN(pdpi::IrP4Info control_ir_p4info,
                   GetIrP4Info(control_switch));
  ASSIGN_OR_RETURN(pdpi::IrP4Info sut_ir_p4info, GetIrP4Info(sut));

  int iterations = 0;
  int total_packets_forwarded = 0;
  int total_packets_punted = 0;
  LOG(INFO) << "Starting to collect traffic results";
  while (GetState() == kTrafficInjectionAndCollection ||
         GetState() == kTrafficCollection) {
    ++iterations;
    LOG_EVERY_T(INFO, 10) << "Traffic collection iteration #" << iterations;

    ASSIGN_OR_RETURN(std::vector<TaggedPacketIn> control_packet_ins,
                     CollectStreamMessageResponsesAndReturnTaggedPacketIns(
                         control_switch, kCollectOutputTrafficDuration,
                         is_expected_unsolicited_packet));

    absl::StatusOr<std::vector<TaggedPacketIn>> sut_packet_ins =
        std::vector<TaggedPacketIn>();
    if (enable_sut_packet_in_collection) {
      ASSIGN_OR_RETURN(sut_packet_ins,
                       CollectStreamMessageResponsesAndReturnTaggedPacketIns(
                           sut, kCollectOutputTrafficDuration,
                           is_expected_unsolicited_packet));
    }

    // Processing the output of the control switch.
    for (TaggedPacketIn& packet_in : control_packet_ins) {
      // Add to (forwarded) switch output for ID.
      absl::MutexLock lock(&collected_traffic_mutex_);
      Packet& forwarded_output =
          *collected_traffic_by_id_[packet_in.tag].add_packets();

      // Set hex and parsed packet.
      forwarded_output.set_hex(
          absl::BytesToHexString(packet_in.packet_in.payload()));
      *forwarded_output.mutable_parsed() = packet_in.parsed_inner_packet;

      // Set port.
      ASSIGN_OR_RETURN(
          pdpi::IrPacketIn ir_packet_in,
          pdpi::PiPacketInToIr(control_ir_p4info, packet_in.packet_in));
      ASSIGN_OR_RETURN(pins_test::P4rtPortId sut_egress_port,
                       GetSutEgressPortFromControlSwitchPacketIn(
                           ir_packet_in, mirror_testbed_port_map));
      *forwarded_output.mutable_port() = sut_egress_port.GetP4rtEncoding();
    }

    // Processing the output of SUT.
    for (const TaggedPacketIn& packet_in : *sut_packet_ins) {
      absl::MutexLock lock(&collected_traffic_mutex_);

      // Add to (punted) switch output for ID.
      PacketIn& punted_output =
          *collected_traffic_by_id_[packet_in.tag].add_packet_ins();

      // Set hex and parsed packet.
      punted_output.set_hex(
          absl::BytesToHexString(packet_in.packet_in.payload()));
      *punted_output.mutable_parsed() = packet_in.parsed_inner_packet;

      // Set metadata.
      ASSIGN_OR_RETURN(
          pdpi::IrPacketIn ir_packet_in,
          pdpi::PiPacketInToIr(sut_ir_p4info, packet_in.packet_in));
      *punted_output.mutable_metadata() = ir_packet_in.metadata();
    }

    total_packets_forwarded += control_packet_ins.size();
    total_packets_punted += sut_packet_ins->size();
    LOG_EVERY_T(INFO, 10) << "Total control switch packets: "
                          << total_packets_forwarded
                          << ", Total SUT packets: " << total_packets_punted;
  }
  LOG(INFO) << "Stopped traffic collection";

  statistics_.total_packets_forwarded += total_packets_forwarded;
  statistics_.total_packets_punted += total_packets_punted;
  return absl::OkStatus();
}

absl::StatusOr<ValidationResult>
TrafficGeneratorWithGuaranteedRate::GetValidationResult() {
  LOG(INFO) << "Getting validation result";
  // Swap `injected_traffic_vector` and `injected_traffic_` and add the
  // `residual_injected_traffic_` to `injected_traffic_`.
  std::vector<InjectedTraffic> injected_traffic_vector;
  injected_traffic_mutex_.Lock();
  injected_traffic_.swap(injected_traffic_vector);
  injected_traffic_mutex_.Unlock();
  for (const InjectedTraffic& injected_traffic : residual_injected_traffic_) {
    injected_traffic_vector.push_back(injected_traffic);
  }
  residual_injected_traffic_.clear();

  const absl::Time kPacketInjectionCutoffTimeForValidation = absl::Now();
  // Wait to ensure all in-flight packets have arrived so the results can be
  // aggregated with the injected_traffic_.
  absl::SleepFor(kMaxPacketInFlightDuration);

  // Swap `collected_traffic_by_id` and `collected_traffic_by_id_` and add
  // the `residual_collected_traffic_by_id_` to `collected_traffic_by_id_`.
  absl::btree_map<int, SwitchOutput> collected_traffic_by_id;
  collected_traffic_mutex_.Lock();
  collected_traffic_by_id_.swap(collected_traffic_by_id);
  collected_traffic_mutex_.Unlock();
  for (const auto& [id, switch_output] : residual_collected_traffic_by_id_) {
    collected_traffic_by_id[id].mutable_packets()->Add(
        switch_output.packets().begin(), switch_output.packets().end());
    collected_traffic_by_id[id].mutable_packet_ins()->Add(
        switch_output.packet_ins().begin(), switch_output.packet_ins().end());
  }
  residual_collected_traffic_by_id_.clear();

  test_runs_.mutable_test_runs()->Reserve(test_runs_.test_runs_size() +
                                          injected_traffic_vector.size());

  // Only consider traffic injected before the cut off time for validation. This
  // is done to ensure in-flight packets are accounted for. The remaining
  // injected/collected traffic are kept in `residual_*` for subsequent calls to
  // this function.
  for (const InjectedTraffic& injected_traffic : injected_traffic_vector) {
    if (injected_traffic.injection_time <
        kPacketInjectionCutoffTimeForValidation) {
      // Add results to test_runs_.
      PacketTestRun* packet_test_run = test_runs_.mutable_test_runs()->Add();
      *packet_test_run->mutable_test_vector() =
          injected_traffic.packet_test_vector;
      if (collected_traffic_by_id.contains(injected_traffic.tag)) {
        *packet_test_run->mutable_actual_output() =
            collected_traffic_by_id[injected_traffic.tag];
        collected_traffic_by_id.erase(injected_traffic.tag);
      }
    } else {
      residual_injected_traffic_.push_back(injected_traffic);
    }
  }

  // Empty remaining collected_traffic_map items into
  // residual_collected_traffic_by_id_.
  for (const auto& [id, switch_output] : collected_traffic_by_id) {
    residual_collected_traffic_by_id_[id] = switch_output;
  }

  return ValidationResult(
      test_runs_, params_.validation_params.switch_output_diff_params,
      generate_test_vectors_result_.packet_synthesis_result);
}

absl::StatusOr<ValidationResult>
TrafficGeneratorWithGuaranteedRate::GetAndClearValidationResult() {
  test_runs_.clear_test_runs();
  return GetValidationResult();
}
}  // namespace dvaas
