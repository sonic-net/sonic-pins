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

#ifndef PINS_DVAAS_TRAFFIC_GENERATOR_H_
#define PINS_DVAAS_TRAFFIC_GENERATOR_H_

#include <memory>
#include <optional>
#include <thread>  // NOLINT: third_party code.
#include <utility>
#include <vector>

#include "absl/base/thread_annotations.h"
#include "absl/container/btree_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/synchronization/mutex.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "dvaas/dataplane_validation.h"
#include "dvaas/mirror_testbed_config.h"
#include "dvaas/packet_injection.h"
#include "dvaas/test_run_validation.h"
#include "dvaas/test_vector.pb.h"
#include "dvaas/validation_result.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "thinkit/mirror_testbed.h"

namespace dvaas {

// Various statistics about test packet synthesis.
struct PacketSynthesisStats {
  // TODO: Add unreachable entries to stats.
  // List of entries deemed unreachable by the packet synthesizer.
  // std::vector<pdpi::IrTableEntry> unreachable_entries;
};

// Interface for generating traffic and validating it.
class TrafficGenerator {
 public:
  // Traffic generation and validation parameters.
  struct Params {
    // See dataplane_validation.h for details.
    DataplaneValidationParams validation_params;

    // TODO: Provide a knob to say I only want L3 forwarded packets.
  };

  // Initialises the traffic generator (and the testbed) with the given params,
  // including synthesising test packets. Does NOT start traffic.
  // On success, returns statistic about packet synthesis.
  //
  // Note: TrafficGenerator does not take ownership of the given testbed, and
  // the caller is responsible for ensuring it outlives the created
  // configurator.
  //
  // NOTE: The table entries, P4Info, and gNMI configuration used in packets
  // synthesis will be read from the SUT itself.
  // It is the client's responsibility to ensure the correctness of these
  // artifacts.
  //
  // NOTE: Synthesizing test packets that are used in the traffic is a
  // computationaly heavy operation and may take a long time (tens of minutes)
  // depending on the coverage goals, the number of entries on SUT, and the
  // allocated compute resources. This function *blocks* until packet synthesis
  // is finished.
  //
  // NOTE: Packet synthesis is done only once and during the
  // call to `Init`. `StartTraffic` does NOT synthesize new test packets,
  // instead it uses test packets synthesized during the call to `Init`. If the
  // switch configuration or entries change after the call to `Init`, the
  // validation results would be inaccurate.
  //
  // Preconditions:
  // - The switches in the testbed must be configured (i.e. have
  //   proper gNMI and P4Info).
  // - SUT must contain the table desired entries.
  // - SUT and its ports must be in a state such that the function can
  //   connect to SUT to read the gNMI config, P4Info, and table entries.
  // - Control switch and its ports must be in a state such that the function
  //   can modify its table entries through a P4RT session.
  //
  // Postconditions (on a successful return):
  // - SUT's entries will be unchanged.
  // - The control switch will have the same entries as
  //   `GetEntriesToPuntAllPackets`.
  // - Any preexisting P4RT connections to SUT and control switch will be
  //   non-primary.
  // - The gNMI configs will be unchanged.
  virtual absl::StatusOr<PacketSynthesisStats> Init(
      thinkit::MirrorTestbed* testbed, const Params& params) = 0;

  // Asynchronously starts injecting traffic (and validating the result) using
  // test packets that were synthesized during `Init`.
  //
  // Precondition: Init must already be called before calling start. Traffic
  // must NOT be already started. Otherwise an error will be returned.
  // Postcondition: Traffic injection is started when the function returns.
  virtual absl::Status StartTraffic() = 0;

  // Stops sending traffic.
  // Blocks until traffic injection/collection fully stops.
  //
  // Precondition: Traffic must be already started.
  // Postcondition: Traffic is stopped when the function returns.
  virtual absl::Status StopTraffic() = 0;

  // Returns various information about the injected traffic including
  // result of dataplane validation.
  // See validation_result.h for details.
  //
  // NOTE: The validation is performed against test packets and expected outputs
  // synthesized during the call to `Init` (with configuration and table
  // entries on SUT at the time of calling `Init`). If the configuration or
  // table entries change after that call, the validation result would be
  // inaccurate.
  //
  // NOTE: If called while traffic flowing, the function may block for a while
  // to collect in-flight packets and validate results.
  //
  // If an optional `diff_params_override` is provided, overrides the
  // `params.validation_params.switch_output_diff_params` passed during the call
  // to Init while validating the switch output for pending test packets.
  // Note: The override is only effective for the pending test packets. It does
  // NOT affect the result of test packets that were validated during the
  // previous calls to `GetValidationResult`. It does NOT affect future calls to
  // `Get*ValidationResult` after the current call, either.
  virtual absl::StatusOr<ValidationResult> GetValidationResult(
      const std::optional<SwitchOutputDiffParams>& diff_params_override =
          std::nullopt) = 0;

  // Similar to `GetValidationResult` but (on a successful return) resets the
  // old results before returning, in the sense that the future calls to
  // Get*ValidationResult will not include the results returned by
  // the current call.
  virtual absl::StatusOr<ValidationResult> GetAndClearValidationResult(
      const std::optional<SwitchOutputDiffParams>& diff_params_override =
          std::nullopt) = 0;

  // Returns the TrafficGenerator's P4RT sessions to SUT or error if the session
  // is not established. Note that the session is only available after a
  // successful call to Init and is a primary connection. The session object
  // gets destroyed on destruction of the object. Client is responsible for
  // handling the risk of dangling pointers.
  // Also note that P4RuntimeSession class is not explicitly stating that it is
  // threadsafe for all of its function, but from the implementation it seems it
  // is indeed threadsafe.
  // TODO: Further investigate whether P4RuntimeSession object is
  // threadsafe or create another wrapper that is explicitly thread safe.
  virtual absl::StatusOr<pdpi::P4RuntimeSession*> SutP4rtSession() = 0;

  // Returns the TrafficGenerator's P4RT sessions to Control Switch or error if
  // the session is not established. Note that the session is only available
  // after a successful call to Init and is a primary connection. The session
  // object gets destroyed on destruction of the object. Client is responsible
  // for handling the risk of dangling pointers.
  // Also note that P4RuntimeSession class is not explicitly stating that it is
  // threadsafe for all of its function, but from the implementation it seems it
  // is indeed threadsafe.
  // TODO: Further investigate whether P4RuntimeSession object is
  // threadsafe or create another wrapper that is explicitly thread safe.
  virtual absl::StatusOr<pdpi::P4RuntimeSession*>
  ControlSwitchP4rtSession() = 0;

  virtual ~TrafficGenerator() = default;
};

// The duration needed to wait to ensure packets are no longer in-flight during
// packet injection.
const absl::Duration kMaxPacketInFlightDuration = absl::Seconds(3);
// The duration of how long to wait before collecting all unread stream messages
// responses from the P4RT session.
const absl::Duration kCollectOutputTrafficDuration = absl::Seconds(1);

// An implementation of `TrafficGenerator` interface that provides a consistent
// traffic injection rate guarantee (see `InjectInputTraffic` function comments
// for more details).
class TrafficGeneratorWithGuaranteedRate : public TrafficGenerator {
 public:
  TrafficGeneratorWithGuaranteedRate() = delete;
  explicit TrafficGeneratorWithGuaranteedRate(
      std::unique_ptr<DataplaneValidationBackend> backend)
      : backend_(std::move(backend)) {}

  absl::StatusOr<PacketSynthesisStats> Init(thinkit::MirrorTestbed* testbed,
                                            const Params& params) override;
  absl::Status StartTraffic() override;
  absl::Status StopTraffic() override;
  absl::StatusOr<ValidationResult> GetValidationResult(
      const std::optional<SwitchOutputDiffParams>& diff_params_override =
          std::nullopt) override;
  absl::StatusOr<ValidationResult> GetAndClearValidationResult(
      const std::optional<SwitchOutputDiffParams>& diff_params_override =
          std::nullopt) override;
  ~TrafficGeneratorWithGuaranteedRate();

  absl::StatusOr<pdpi::P4RuntimeSession*> SutP4rtSession() override {
    if (testbed_configurator_ != nullptr) {
      return testbed_configurator_->SutApi().p4rt.get();
    }
    return absl::FailedPreconditionError(
        "Testbed configurator is not initialized.");
  }

  absl::StatusOr<pdpi::P4RuntimeSession*> ControlSwitchP4rtSession()
      override {
    if (testbed_configurator_ != nullptr) {
      return testbed_configurator_->ControlSwitchApi().p4rt.get();
    }
    return absl::FailedPreconditionError(
        "Testbed configurator is not initialized.");
  }

 private:
  std::unique_ptr<DataplaneValidationBackend> backend_;
  std::unique_ptr<MirrorTestbedConfigurator> testbed_configurator_;

  // The P4Specification, P4Info, and entities from SUT are stored to maintain
  // consistency between when test vector expectations are generated and when
  // packet traces are created.
  P4Specification sut_p4_spec_;
  pdpi::IrP4Info sut_ir_p4info_;
  pdpi::IrEntities sut_augmented_entities_;

  // Test vectors created as a result of (latest) call to `Init`. Calls to
  // `StartTraffic` use these test vectors.
  GenerateTestVectorsResult generate_test_vectors_result_;

  struct InjectedTraffic {
    int tag;
    PacketTestVector packet_test_vector;
    absl::Time injection_time = absl::Now();
  };

  enum State {
    // The object has been created but `Init` has not been called.
    kUninitialized,
    // `Init` has been called, but no input packets are injected and no output
    // is being collected (either `StartTraffic` has not been called or
    // `StopTraffic` has been called and finished after that).
    kInitialized,
    // Input packets are being injected and the output is being collected
    // (`StartTraffic` is called and `StopTraffic` has NOT been called after
    // that).
    kTrafficInjectionAndCollection,
    // No new input packets is being injected but the output is still being
    // collected to account for in-flight packets (transient state during call
    // to `StopTraffic` for kMaxPacketInFlightDuration).
    kTrafficCollection,
    // The unrecoverable error state that happens when either
    // `InjectInputTraffic` or `CollectOutputTraffic` thread returns an error
    // status.
    kError,
  };
  // The state of the TrafficGeneratorWithGuaranteedRate object.
  State state_ ABSL_GUARDED_BY(state_mutex_) = kUninitialized;
  // Mutex to synchronize access to state_;
  absl::Mutex state_mutex_;

  // Thread safe getter for state_.
  State GetState() ABSL_LOCKS_EXCLUDED(state_mutex_);
  // Thread safe setter for state_.
  void SetState(State state) ABSL_LOCKS_EXCLUDED(state_mutex_);

  // The same test vectors are reused multiple times so we use a counter to
  // produce unique tag ids and retag test vectors per each use.
  int packet_tag_id_ = 1;

  // The number of packet traces collected during `GetValidationResult`.
  int packet_trace_count_ = 0;

  PacketStatistics statistics_;

  // Traffic injected after latest call to `Get*ValidationResult`.
  std::vector<InjectedTraffic> injected_traffic_
      ABSL_GUARDED_BY(injected_traffic_mutex_);
  absl::Mutex injected_traffic_mutex_;
  // Injected traffic not validated during previous calls to
  // `Get*ValidationResult` based on injection timestamp (to account for
  // in-flight packets).
  std::vector<InjectedTraffic> residual_injected_traffic_;

  // Traffic collected (from control switch and SUT)  after latest call to
  // `Get*ValidationResult`.
  absl::btree_map<int, SwitchOutput> collected_traffic_by_id_
      ABSL_GUARDED_BY(collected_traffic_mutex_);
  absl::Mutex collected_traffic_mutex_;
  // Residual collected traffic from `collected_traffic_by_id_` not validated
  // during previous calls to `Get*ValidationResult` when there is not a
  // InjectedTraffic with a matching tag.
  absl::btree_map<int, SwitchOutput> residual_collected_traffic_by_id_;

  // The thread that is spawned during the call to `StartTraffic` and runs
  // `InjectInputTraffic` function. The thread continues until `StopTraffic` is
  // called.
  std::thread traffic_injection_thread_;
  // Runs in a separate thread and loops so long as state is
  // kTrafficInjectionAndCollection. It injects packets until traffic is
  // stopped. In each iteration of the loop, it retags and injects packets from
  // `generate_test_vectors_result_.packet_test_vector_by_id` at the rate
  // specified by `params_`. Timestamps and records injected packets in
  // `injected_traffic_` for processing during calls to `Get*ValidationResult`.
  absl::Status InjectInputTraffic()
      ABSL_LOCKS_EXCLUDED(injected_traffic_mutex_);

  // The thread that is spawned during the call to `StartTraffic` and runs
  // `CollectOutputTraffic` function. The thread continues until `StopTraffic`
  // is called.
  std::thread traffic_collection_thread_;
  // Runs in a separate thread and loops so long as state is
  // kTrafficInjectionAndCollection or kTrafficCollection. It retrieves and
  // processes packets from the control switch and SUT until traffic is stopped.
  // In each iteration of the loop, collects packets for
  // kCollectOutputTrafficDuration. The result is stored in
  // `collected_traffic_by_id_` for processing during calls to
  // `Get*ValidationResult`.
  absl::Status CollectOutputTraffic()
      ABSL_LOCKS_EXCLUDED(collected_traffic_mutex_);

  // Result of packet injection, collection, and validation (i.e. test vector +
  // switch output + validation result), produced and used by
  // `GetValidationStats` by processing `injected_traffic_` and
  // `collected_traffic_by_id_` (and residues).
  PacketTestOutcomes test_outcomes_;

  // Parameters received in the (latest) call to `Init`.
  TrafficGenerator::Params params_;
};
}  // namespace dvaas

#endif  // PINS_DVAAS_TRAFFIC_GENERATOR_H_
