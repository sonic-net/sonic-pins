#ifndef PINS_DVAAS_LABEL_H_
#define PINS_DVAAS_LABEL_H_

#include <functional>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "dvaas/test_vector.pb.h"

namespace dvaas {

// Augments the `test_outcomes` with labels.
absl::Status AugmentTestOutcomesWithLabels(
    PacketTestOutcomes& test_outcomes,
    const std::vector<
        std::function<absl::StatusOr<Labels>(const PacketTestRun&)>>& labelers);

}  // namespace dvaas

#endif  // PINS_DVAAS_LABEL_H_
