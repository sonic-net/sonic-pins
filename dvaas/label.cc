#include "dvaas/label.h"

#include <functional>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "dvaas/test_vector.pb.h"
#include "gutil/status.h"

namespace dvaas {

absl::Status AugmentTestOutcomesWithLabels(
    PacketTestOutcomes& test_outcomes,
    const std::vector<
        std::function<absl::StatusOr<Labels>(const PacketTestRun&)>>&
        labelers) {
  LOG(INFO) << "Augmenting test outcomes with labels (" << labelers.size()
            << " labelers)";
  int failed_labeler_count = 0;
  std::optional<absl::Status> first_failed_labeler_error;
  for (const auto& labeler : labelers) {
    for (PacketTestOutcome& test_outcome : *test_outcomes.mutable_outcomes()) {
      absl::StatusOr<Labels> labels = labeler(test_outcome.test_run());
      // TODO: Extend the logic to include more than just one
      // failure and specify the labeler that failed.
      if (!labels.ok()) {
        failed_labeler_count++;
        if (!first_failed_labeler_error.has_value()) {
          first_failed_labeler_error = labels.status();
        }
        continue;
      }
      for (const std::string& label : labels->labels()) {
        PacketTestRun& test_run = *test_outcome.mutable_test_run();
        *test_run.mutable_labels()->add_labels() = std::move(label);
      }
    }
  }
  if (failed_labeler_count > 0) {
    LOG(WARNING) << "Failed to label " << failed_labeler_count
                 << " test outcomes: " << *first_failed_labeler_error;
  }
  return absl::OkStatus();
}

}  // namespace dvaas

