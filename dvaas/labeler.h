#ifndef PINS_DVAAS_LABELER_H_
#define PINS_DVAAS_LABELER_H_

#include <functional>
#include <vector>

#include "absl/status/statusor.h"
#include "dvaas/test_vector.pb.h"

namespace dvaas {

// List of default labelers.
std::vector<std::function<absl::StatusOr<Labels>(const PacketTestRun&)>>
DefaultPacketTestRunLabelers();

}  // namespace dvaas

#endif  // PINS_DVAAS_LABELER_H_
