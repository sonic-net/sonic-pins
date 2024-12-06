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
#include <thread>  // NOLINT: third_party code.
#include <utility>
#include <vector>

#include "absl/base/thread_annotations.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/synchronization/mutex.h"
#include "dvaas/dataplane_validation.h"
#include "dvaas/mirror_testbed_config.h"
#include "dvaas/test_vector.h"
#include "dvaas/test_vector.pb.h"
#include "dvaas/validation_result.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/mirror_testbed_fixture.h"

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

    // TODO: Implement ignore_punted_packets_for_validation.
    // If true, ignores punting behavior during validation.
    // bool ignore_punting_for_validation;
    // TODO: Provide a knob to say I only want L3 forwarded packets.
  };

  // Initialises the traffic generator (and the testbed) with the given params,
  // including synthesising test packets. Does NOT start traffic.
  // On success, returns statistic about packet synthesis.
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
      std::shared_ptr<thinkit::MirrorTestbedInterface> testbed,
      const Params& params) = 0;

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
  virtual absl::StatusOr<ValidationResult> GetValidationResult() = 0;
  // Similar to `GetValidationResult` but (on a successful return) resets the
  // old results before returning, in the sense that the future calls to
  // Get*ValidationResult will not include the results returned by
  // the current call.
  virtual absl::StatusOr<ValidationResult> GetAndClearValidationResult() = 0;

  virtual ~TrafficGenerator() = default;
};

// A simple implementation of `TrafficGenerator` interface that can be used as a
// proof of concept. This implementation does NOT provide a consistent traffic
// injection rate guarantee (see `InjectTraffic` function comments for more
// details).
class SimpleTrafficGenerator : public TrafficGenerator {
 public:
  SimpleTrafficGenerator() = delete;
  explicit SimpleTrafficGenerator(
      std::unique_ptr<DataplaneValidationBackend> backend)
      : backend_(std::move(backend)) {}

  absl::StatusOr<PacketSynthesisStats> Init(
      std::shared_ptr<thinkit::MirrorTestbedInterface> testbed,
      const Params& params) override;
  absl::Status StartTraffic() override;
  absl::Status StopTraffic() override;
  absl::StatusOr<ValidationResult> GetValidationResult() override;
  absl::StatusOr<ValidationResult> GetAndClearValidationResult() override;

 private:
  std::unique_ptr<DataplaneValidationBackend> backend_;
  std::unique_ptr<MirrorTestbedConfigurator> testbed_configurator_;
  // Test vectors created as a result of (latest) call to `Init`. Calls to
  // `StartTraffic` use these test vectors.
  PacketTestVectorById test_vector_by_id_;

  enum State {
    // The object has been created but `Init` has not been called.
    kUninitialized,
    // `Init` has been called, but no traffic is flowing (either `StartTraffic`
    // has not been called or `StopTraffic` has been called after that).
    kInitialized,
    // Traffic is flowing (`StartTraffic` has been called and `StopTraffic` has
    // NOT been called after that).
    kTrafficFlowing,
  };
  // The state of the SimpleTrafficGenerator object.
  State state_ ABSL_GUARDED_BY(state_mutex_) = kUninitialized;
  // Mutex to synchronize access to state_;
  absl::Mutex state_mutex_;

  // Thread safe getter for state_.
  State GetState() ABSL_LOCKS_EXCLUDED(state_mutex_);
  // Thread safe setter for state_.
  void SetState(State state) ABSL_LOCKS_EXCLUDED(state_mutex_);

  // The thread that is spawned during the call to `StartTraffic` and runs
  // `InjectTraffic` function. The thread continues until `StopTraffic` is
  // called.
  std::thread traffic_injection_thread_;
  // Runs in a separate thread, as a loop that injects and collects packets
  // until traffic is stopped.
  // In each iteration of the loop, injects packets in `test_vector_by_id_` at
  // the rate specified by `params_`. At the end of each iteration, WAITS UP TO
  // 3 SECONDS to collect any in-flight packets, before moving on to next
  // iteration.
  void InjectTraffic() ABSL_LOCKS_EXCLUDED(test_runs_mutex_);

  // Result of packet injection and collection (i.e. test vector + switch
  // output). Populated by `InjectTraffic`. Used during the call to
  // `Get*ValidationStats`.
  PacketTestRuns test_runs_ ABSL_GUARDED_BY(test_runs_mutex_);
  // Mutex to synchronize access to test_runs_;
  absl::Mutex test_runs_mutex_;

  // Parameters received in the (latest) call to `Init`.
  TrafficGenerator::Params params_;
};

}  // namespace dvaas

#endif  // PINS_DVAAS_TRAFFIC_GENERATOR_H_
