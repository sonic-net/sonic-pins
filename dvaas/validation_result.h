// Tools to analyze and consume the result of dataplane validation, as returned
// to DVaaS users.

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

#ifndef PINS_DVAAS_VALIDATION_RESULT_H_
#define PINS_DVAAS_VALIDATION_RESULT_H_

#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "dvaas/test_run_validation.h"
#include "dvaas/test_vector.pb.h"
#include "dvaas/test_vector_stats.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesizer.pb.h"

namespace dvaas {

// Result of automated test packet synthesis (using P4-Symbolic)
struct PacketSynthesisResult {
  std::vector<p4_symbolic::packet_synthesizer::SynthesizedPacket>
      synthesized_packets;
  // True if and only if packet synthesis runs with a time limit and does not
  // finish within that time limit. If true, `synthesized_packets` may not
  // fully cover the target coverage goals.
  bool packet_synthesis_timed_out = false;
};

// The result of dataplane validation, as returned to DVaaS users.
class [[nodiscard]] ValidationResult {
public:
  // Asserts that at least an `expected_success_rate` fraction of test vectors
  // succeeded, returning either:
  // * an `Ok` status if that is the case, or
  // * an `OutOfRange` error with details to assist debugging otherwise.
  //
  // Example uses:
  // ```
  //   // Expect all tests to pass, e.g. when the switch is stable.
  //   EXPECT_OK(validation_result.HasSuccessRateOfAtLeast(1.0));
  //
  //   // Expect at least 70% of tests to pass, e.g. during development.
  //   EXPECT_OK(validation_result.HasSuccessRateOfAtLeast(0.75));
  // ```
  absl::Status HasSuccessRateOfAtLeast(double expected_success_rate) const;

  // Returns the fraction of test vectors that passed.
  double GetSuccessRate() const;

  // Returns true if there is any test failure, and false otherwise.
  bool HasFailure() const;

  // Logs various statistics about the number of test vectors and how many of
  // them passed.
  const ValidationResult& LogStatistics() const;
  ValidationResult& LogStatistics();
  void RecordStatisticsAsTestProperties() const;

  // Returns a list of all test failures. Prefer using `HasSuccessRateOfAtLeast`
  // as it includes additional information to ease debugging.
  std::vector<std::string> GetAllFailures() const;

  // Returns the raw validation result stored in the object, which contains
  // information about each individual packet test run, including the test
  // vector (input, expected output), actual output, result of comparison,
  // packet traces, etc. See `PacketTestOutcomes`'s proto definition for
  // details.
  // Note: It is best to use the higher-level functions like
  // `HasSuccessRateOfAtLeast` and `GetAllFailures` to analyze the validation
  // result and only use the raw data for advanced use cases.
  PacketTestOutcomes GetRawPacketTestOutcomes() const;

  // Constructs a `ValidationResult` from the given `test_outcomes` and
  // `packet_synthesis_result`.
  ValidationResult(const PacketTestOutcomes& test_outcomes,
                   const PacketSynthesisResult& packet_synthesis_result);

  // Constructs a `absl::StatusOr<ValidationResult>` from the given `test_runs`
  // and `packet_synthesis_result`. Uses `diff_params` while validating the test
  // runs. See `test_run_validation.h` for details.
  static absl::StatusOr<ValidationResult> Create(
      PacketTestRuns& test_runs, const SwitchOutputDiffParams& diff_params,
      const PacketSynthesisResult& packet_synthesis_result);

  // Returns true if and only if packet synthesis runs with a time limit and
  // does not finish within that time limit.
  // NOTE: If true, dataplane validation did not fully cover the target coverage
  // goals (in the worst case, it may have not tested dataplane at all). This
  // should be taken into account when interpreting the results of other
  // functions like `HasSuccessRateOfAtLeast` and `GetAllFailures`.
  bool PacketSynthesizerTimedOut() const;

 private:
  ValidationResult(const PacketSynthesisResult& packet_synthesis_result,
                   const PacketTestOutcomes& test_outcomes)
      : test_outcomes_(test_outcomes),
        test_vector_stats_(ComputeTestVectorStats(test_outcomes_)),
        packet_synthesis_result_(packet_synthesis_result) {}

  PacketTestOutcomes test_outcomes_;
  TestVectorStats test_vector_stats_;
  PacketSynthesisResult packet_synthesis_result_;
};

} // namespace dvaas

#endif // PINS_DVAAS_VALIDATION_RESULT_H_
