#ifndef PINS_DVAAS_FAILURE_POST_PROCESSING_H_
#define PINS_DVAAS_FAILURE_POST_PROCESSING_H_

#include <functional>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "dvaas/test_vector.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesizer.pb.h"

namespace dvaas {

using ::p4_symbolic::packet_synthesizer::SynthesizedPacket;

// Removes entities from `entities_to_minimize` on the switch while still
// maintaining the same failure. The function `test_if_entity_can_be_removed` is
// used to determine if an entity can be removed.
absl::Status EntityMinimizationLoop(
    std::function<
        absl::StatusOr<bool>(const pdpi::IrEntity& entity_to_remove,
                             const pdpi::IrEntities& current_entities)>
        test_if_entity_can_be_removed,
    pdpi::IrEntities& entities_to_minimize);

}  // namespace dvaas

#endif  // PINS_DVAAS_FAILURE_POST_PROCESSING_H_
