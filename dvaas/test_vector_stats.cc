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

#include "dvaas/test_vector_stats.h"

#include <string>

#include "absl/algorithm/container.h"
#include "absl/strings/str_format.h"
#include "dvaas/test_vector.pb.h"

namespace dvaas {

namespace {

void AddTestVectorStats(const PacketTestOutcome& outcome,
                        TestVectorStats& stats) {
  stats.num_vectors += 1;

  if (outcome.test_result().has_failure()) {
    if (outcome.test_result().failure().reproducibility_rate() == 1.0) {
      stats.num_deterministic_failures += 1;
    }
  } else {
    stats.num_vectors_passed += 1;
  }

  const SwitchOutput& actual_output = outcome.test_run().actual_output();
  const int num_forwarded = actual_output.packets_size();
  const int num_punted = actual_output.packet_ins_size();

  bool has_correct_num_outputs = absl::c_any_of(
      outcome.test_run().test_vector().acceptable_outputs(),
      [&](const SwitchOutput& acceptable_output) {
        return num_forwarded == acceptable_output.packets_size() &&
               num_punted == acceptable_output.packet_ins_size();
      });
  if (has_correct_num_outputs) {
    stats.num_vectors_with_correct_number_of_outputs += 1;
  }

  stats.num_vectors_forwarding += num_forwarded > 0 ? 1 : 0;
  stats.num_vectors_punting += num_punted > 0 ? 1 : 0;
  stats.num_vectors_dropping += num_forwarded == 0 && num_punted == 0;
  stats.num_packets_forwarded += num_forwarded;
  stats.num_packets_punted += num_punted;
}

}  // namespace

TestVectorStats ComputeTestVectorStats(
    const PacketTestOutcomes& test_outcomes) {
  TestVectorStats stats;
  for (const auto& outcome : test_outcomes.outcomes()) {
    AddTestVectorStats(outcome, stats);
  }
  return stats;
}

namespace {

std::string ExplainPercent(double fraction) {
  return absl::StrFormat("%.2f%%", fraction * 100);
}
std::string ExplainPercent(int numerator, int denominator) {
  if (denominator == 0) return "100%";
  return ExplainPercent(static_cast<double>(numerator) / denominator);
}

std::string ExplainFraction(int numerator, int denominator) {
  return absl::StrFormat("%s of %d", ExplainPercent(numerator, denominator),
                         denominator);
}

}  // namespace

std::string ExplainTestVectorStats(const TestVectorStats& stats) {
  std::string result;

  absl::StrAppendFormat(
      &result, "%s test vectors passed\n",
      ExplainFraction(stats.num_vectors_passed, stats.num_vectors));
  absl::StrAppendFormat(
      &result,
      "%s test vectors produced the correct number and type of output "
      "packets\n",
      ExplainFraction(stats.num_vectors_with_correct_number_of_outputs,
                      stats.num_vectors));
  absl::StrAppendFormat(
      &result,
      "%d test vectors forwarded, producing %d forwarded output packets\n",
      stats.num_vectors_forwarding, stats.num_packets_forwarded);
  absl::StrAppendFormat(
      &result, "%d test vectors punted, producing %d punted output packets\n",
      stats.num_vectors_punting, stats.num_packets_punted);
  absl::StrAppendFormat(&result, "%d test vectors produced no output packets\n",
                        stats.num_vectors_dropping);
  absl::StrAppendFormat(&result,
                        "%d of %d test vectors with failures were "
                        "deterministically reproducible\n",
                        stats.num_deterministic_failures,
                        stats.num_vectors - stats.num_vectors_passed);
  return result;
}

}  // namespace dvaas
