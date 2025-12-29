#include "dvaas/label.h"

#include <functional>
#include <string>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "dvaas/test_vector.pb.h"
#include "gutil/gutil/status.h"

namespace dvaas {

absl::Status AugmentTestOutcomesWithLabels(
    PacketTestOutcomes& test_outcomes,
    const std::vector<
        std::function<absl::StatusOr<Labels>(const PacketTestRun&)>>&
        labelers) {
  for (const auto& labeler : labelers) {
    for (PacketTestOutcome& test_outcome : *test_outcomes.mutable_outcomes()) {
      ASSIGN_OR_RETURN(Labels labels, labeler(test_outcome.test_run()));
      for (const std::string& label : labels.labels()) {
        PacketTestRun& test_run = *test_outcome.mutable_test_run();
        *test_run.mutable_labels()->add_labels() = std::move(label);
      }
    }
  }
  return absl::OkStatus();
}

}  // namespace dvaas
