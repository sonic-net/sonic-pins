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
#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "dvaas/test_run_validation.h"
#include "dvaas/test_vector.pb.h"
#include "dvaas/test_vector_stats.h"
#include "glog/logging.h"
#include "google/protobuf/descriptor.h"
#include "gutil/status.h"

namespace dvaas {

ValidationResult::ValidationResult(const PacketTestRuns& test_runs,
                                   const SwitchOutputDiffParams& diff_params) {
  test_outcomes_.mutable_outcomes()->Reserve(test_runs.test_runs_size());
  for (const auto& test_run : test_runs.test_runs()) {
    PacketTestOutcome& outcome = *test_outcomes_.add_outcomes();
    *outcome.mutable_test_run() = test_run;
    *outcome.mutable_test_result() = ValidateTestRun(test_run, diff_params);
  }

  test_vector_stats_ = ComputeTestVectorStats(test_outcomes_);
}

absl::Status ValidationResult::HasSuccessRateOfAtLeast(
    double expected_success_rate) const {
  // Avoid division by 0.
  if (test_vector_stats_.num_vectors == 0) return absl::OkStatus();

  double success_rate =
      static_cast<double>(test_vector_stats_.num_vectors_passed) /
      static_cast<double>(test_vector_stats_.num_vectors);
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
           << it->test_result().failure().description();
  }
  return absl::OkStatus();
}

const ValidationResult& ValidationResult::LogStatistics() const {
  LOG(INFO) << ExplainTestVectorStats(test_vector_stats_);
  return *this;
}
ValidationResult& ValidationResult::LogStatistics() {
  LOG(INFO) << ExplainTestVectorStats(test_vector_stats_);
  return *this;
}

std::vector<std::string> ValidationResult::GetAllFailures() const {
  std::vector<std::string> failures;
  failures.reserve(test_vector_stats_.num_vectors -
                   test_vector_stats_.num_vectors_passed);
  for (const auto& outcome : test_outcomes_.outcomes()) {
    if (outcome.test_result().has_failure()) {
      failures.push_back(outcome.test_result().failure().description());
    }
  }
  return failures;
}

}  // namespace dvaas
