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
#include <utility>
#include <vector>

#include "absl/algorithm/container.h"
#include "absl/container/flat_hash_set.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/strings/str_format.h"
#include "dvaas/packet_trace.h"
#include "dvaas/packet_trace.pb.h"
#include "dvaas/test_run_validation.h"
#include "dvaas/test_vector.pb.h"
#include "dvaas/test_vector_stats.h"
#include "gtest/gtest.h"
#include "gutil/status.h"

namespace dvaas {

ValidationResult::ValidationResult(
    const PacketTestOutcomes& test_outcomes,
    const PacketSynthesisResult& packet_synthesis_result)
    : test_outcomes_(test_outcomes),
      overall_test_vector_stats_(ComputeTestVectorStats(test_outcomes)),
      packet_synthesis_result_(packet_synthesis_result),
      label_to_test_vector_stats_(
          ComputeTestVectorStatsPerLabel(test_outcomes)) {}

absl::StatusOr<ValidationResult> ValidationResult::Create(
    PacketTestRuns& test_runs, const SwitchOutputDiffParams& diff_params,
    const PacketSynthesisResult& packet_synthesis_result) {
  ASSIGN_OR_RETURN(PacketTestOutcomes test_outcomes,
                   ValidateTestRuns(test_runs, diff_params));
  return ValidationResult(test_outcomes, packet_synthesis_result);
}

std::string ExplainFailure(const PacketTestOutcome& test_outcome) {
  const PacketTestValidationResult::Failure& failure =
      test_outcome.test_result().failure();
  std::string failure_message;
  if (failure.has_minimization_analysis()) {
    failure_message = absl::StrFormat(
        "Sending the same input packet reproduces this error %.2f%% of the "
        "time\n%s",
        failure.minimization_analysis().reproducibility_rate() * 100,
        failure.description());
  } else {
    failure_message = absl::StrCat(failure.description());
  }
  std::string trace_summary;
  const auto& acceptable_outputs =
      test_outcome.test_run().test_vector().acceptable_outputs();
  auto packet_trace_it = absl::c_find_if(
      acceptable_outputs,
      [](const auto& output) { return output.has_packet_trace(); });
  if (packet_trace_it != acceptable_outputs.end()) {
    std::string trace =
        dvaas::GetPacketTraceSummary(packet_trace_it->packet_trace());
    if (!trace.empty()) {
      trace_summary = absl::StrCat(
          "DISCLAIMER: The following trace is produced from a simulation based "
          "on the P4 model of the switch. Its sole purpose is to explain why "
          "the test expects the output it expects. It does NOT necessarily "
          "represent the behavior of the actual hardware under test. ",
          "Moreover, this is a summary of the full trace and does not contain "
          "all details. The full trace can be found in artifacts.\n\n",
          trace);
    }
  } else {
    trace_summary = "No packet trace found.\n";
  }
  return absl::StrCat(failure_message,
                      "\n== EXPECTED INPUT-OUTPUT TRACE (P4 SIMULATION) SUMMARY"
                      " =========================\n",
                      trace_summary);
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
           << ExplainTestVectorStats(overall_test_vector_stats_) << "\n"
           << "\nShowing the first failure only. Refer to the test artifacts "
              "for the full list of errors.\n"
           << ExplainFailure(*it);
  }
  return absl::OkStatus();
}

absl::Status ValidationResult::HasSuccessRateOfAtLeastForGivenLabels(
    double expected_success_rate,
    const absl::flat_hash_set<std::string>& included_labels) const {
  PacketTestOutcomes filtered_test_outcomes;
  // Filter test outcomes based on the included labels.
  for (const auto& outcome : test_outcomes_.outcomes()) {
    for (const auto& outcome_label : outcome.test_run().labels().labels()) {
      if (included_labels.contains(outcome_label)) {
        *filtered_test_outcomes.add_outcomes() = outcome;
        break;
      }
    }
  }

  ValidationResult filtered_validation_result(std::move(filtered_test_outcomes),
                                              packet_synthesis_result_);
  return filtered_validation_result.HasSuccessRateOfAtLeast(
      expected_success_rate);
}

absl::Status ValidationResult::HasSuccessRateOfAtLeastWithoutGivenLabels(
    double expected_success_rate,
    const absl::flat_hash_set<std::string>& excluded_labels) const {
  return ExcludingLabels(excluded_labels)
      .HasSuccessRateOfAtLeast(expected_success_rate);
}

ValidationResult ValidationResult::ExcludingLabels(
    const absl::flat_hash_set<std::string>& excluded_labels) const {
  // Filter test outcomes based on the excluded labels.
  PacketTestOutcomes filtered_test_outcomes;
  for (const auto& outcome : test_outcomes_.outcomes()) {
    bool has_excluded_label = false;
    for (const auto& outcome_label : outcome.test_run().labels().labels()) {
      if (excluded_labels.contains(outcome_label)) {
        has_excluded_label = true;
        break;
      }
    }
    if (!has_excluded_label) {
      *filtered_test_outcomes.add_outcomes() = outcome;
    }
  }
  return ValidationResult(std::move(filtered_test_outcomes),
                          packet_synthesis_result_);
}

double ValidationResult::GetSuccessRate() const {
  // Avoid division by 0.
  if (overall_test_vector_stats_.num_vectors == 0) return 1.0;
  return static_cast<double>(overall_test_vector_stats_.num_vectors_passed) /
         static_cast<double>(overall_test_vector_stats_.num_vectors);
}

bool ValidationResult::HasFailure() const {
  return overall_test_vector_stats_.num_vectors_passed <
         overall_test_vector_stats_.num_vectors;
}

const ValidationResult& ValidationResult::LogStatistics() const {
  LOG(INFO) << ExplainTestVectorStats(overall_test_vector_stats_);
  LOG(INFO) << ExplainPerLabelStats(label_to_test_vector_stats_);
  return *this;
}
ValidationResult& ValidationResult::LogStatistics() {
  LOG(INFO) << ExplainTestVectorStats(overall_test_vector_stats_);
  LOG(INFO) << ExplainPerLabelStats(label_to_test_vector_stats_);
  return *this;
}

void ValidationResult::RecordStatisticsAsTestProperties() const {
  RecordStatsAsTestProperties(overall_test_vector_stats_);
}

void ValidationResult::RecordPerLabelStatsAsTestProperties() const {
  testing::Test::RecordProperty(
      "dvaas_success_rate_per_label",
      ExplainPerLabelStats(label_to_test_vector_stats_,
                           /*include_title=*/false));
}

std::vector<std::string> ValidationResult::GetAllFailures() const {
  std::vector<std::string> failures;
  failures.reserve(overall_test_vector_stats_.num_vectors -
                   overall_test_vector_stats_.num_vectors_passed);
  for (const auto& outcome : test_outcomes_.outcomes()) {
    if (outcome.test_result().has_failure()) {
      failures.push_back(ExplainFailure(outcome));
    }
  }
  return failures;
}

PacketTestOutcomes ValidationResult::GetRawPacketTestOutcomes() const {
  return test_outcomes_;
}

bool ValidationResult::PacketSynthesizerTimedOut() const {
  return packet_synthesis_result_.packet_synthesis_timed_out;
}

}  // namespace dvaas
