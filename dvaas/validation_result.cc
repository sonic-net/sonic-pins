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

#include "dvaas/validation_result.h"

#include <string>
#include <vector>

#include "absl/algorithm/container.h"
#include "absl/status/status.h"
#include "absl/strings/str_format.h"
#include "dvaas/test_run_validation.h"
#include "dvaas/test_vector.pb.h"
#include "dvaas/test_vector_stats.h"
#include "glog/logging.h"
#include "gutil/gutil/status.h"

namespace dvaas {

ValidationResult::ValidationResult(
    const PacketTestOutcomes& test_outcomes,
    const PacketSynthesisResult& packet_synthesis_result)
    : test_outcomes_(test_outcomes),
      test_vector_stats_(ComputeTestVectorStats(test_outcomes)),
      packet_synthesis_result_(packet_synthesis_result) {}

absl::StatusOr<ValidationResult> ValidationResult::Create(
    PacketTestRuns& test_runs, const SwitchOutputDiffParams& diff_params,
    const PacketSynthesisResult& packet_synthesis_result) {
  ASSIGN_OR_RETURN(PacketTestOutcomes test_outcomes,
                   ValidateTestRuns(test_runs, diff_params));
  return ValidationResult(packet_synthesis_result, test_outcomes);
}

std::string ExplainFailure(const PacketTestValidationResult::Failure& failure) {
  if (failure.has_minimization_analysis()) {
    return absl::StrFormat(
        "Sending the same input packet reproduces this error %.2f%% of the "
        "time\n%s",
        failure.minimization_analysis().reproducibility_rate() * 100,
        failure.description());
  } else {
    return failure.description();
  }
}

absl::Status ValidationResult::HasSuccessRateOfAtLeast(
    double expected_success_rate) const {
  double success_rate = GetSuccessRate();
  if (success_rate < expected_success_rate) {
    auto it =
        absl::c_find_if(test_outcomes_.outcomes(), [](const auto& outcome) {
          return outcome.test_result().has_failure();
        });
    if (it == test_outcomes_.outcomes().end()) return absl::OkStatus();
    return gutil::OutOfRangeErrorBuilder()
           << ExplainTestVectorStats(test_vector_stats_)
           << "\nShowing the first failure only. Refer to the test artifacts "
              "for the full list of errors.\n"
           << ExplainFailure(it->test_result().failure());
  }
  return absl::OkStatus();
}

double ValidationResult::GetSuccessRate() const {
  // Avoid division by 0.
  if (test_vector_stats_.num_vectors == 0) return 1.0;
  return static_cast<double>(test_vector_stats_.num_vectors_passed) /
         static_cast<double>(test_vector_stats_.num_vectors);
}

bool ValidationResult::HasFailure() const {
  return test_vector_stats_.num_vectors_passed < test_vector_stats_.num_vectors;
}

const ValidationResult& ValidationResult::LogStatistics() const {
  LOG(INFO) << ExplainTestVectorStats(test_vector_stats_);
  return *this;
}
ValidationResult& ValidationResult::LogStatistics() {
  LOG(INFO) << ExplainTestVectorStats(test_vector_stats_);
  return *this;
}

void ValidationResult::RecordStatisticsAsGoogleTestProperties() const {
  RecordStatsAsGoogleTestProperties(test_vector_stats_);
}

std::vector<std::string> ValidationResult::GetAllFailures() const {
  std::vector<std::string> failures;
  failures.reserve(test_vector_stats_.num_vectors -
                   test_vector_stats_.num_vectors_passed);
  for (const auto& outcome : test_outcomes_.outcomes()) {
    if (outcome.test_result().has_failure()) {
      failures.push_back(ExplainFailure(outcome.test_result().failure()));
    }
  }
  return failures;
}

bool ValidationResult::PacketSynthesizerTimedOut() const {
  return packet_synthesis_result_.packet_synthesis_timed_out;
}

}  // namespace dvaas
