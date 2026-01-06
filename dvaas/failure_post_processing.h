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

enum MinimizationAlgorithm {
  kTableBasedBisection,
  kRemoveEntitiesOneByOne,
};

using TestIfEntitiesCanBeRemoved =
    std::function<absl::StatusOr<bool>(const pdpi::IrEntities& entities)>;

// Minimizes the entities in `entities_to_minimize` on the switch using the
// given `minimization_algorithm` while still maintaining the same failure.
// The function `test_if_entity_can_be_removed` is used to determine if an
// entity can be removed.
// Important: This function expects that the entities in
// `entities_to_minimize` are sorted by dependency rank.
// TODO: Sort by dependency rank in this function to avoid
// depending on the caller to do so.
absl::Status DoEntityMinimization(
    TestIfEntitiesCanBeRemoved test_if_entities_can_be_removed,
    const pdpi::IrEntities& entities_to_minimize,
    MinimizationAlgorithm minimization_algorithm = kTableBasedBisection);

// Compares the two test outcomes and returns true if they have the same
// failure, while treating repeated fields as sets and ignoring the
// `packet_trace`, `input_packet_injection_time`, and `labels` fields.
bool HasSameFailure(const dvaas::PacketTestOutcome& original_test_outcome,
                    const dvaas::PacketTestOutcome& new_test_outcome);

// Removes entities from `entities_to_minimize` one by one from the switch and
// checks if the test still fails (optionally with the same failure). The
// function `test_if_entities_can_be_removed` is used to determine if an entity
// can be removed.
// Important: This function expects that the entities in
// `entities_to_minimize` are sorted by dependency rank.
absl::Status RemoveEntitiesOneByOne(
    TestIfEntitiesCanBeRemoved test_if_entities_can_be_removed,
    const pdpi::IrEntities& entities_to_minimize);

// Performs table-based bisection on the entities in `entities_to_minimize` by
// repeatedly removing groups of entities from the switch and checking if the
// test still fails (optionally with the same failure). The function
// `try_to_delete_and_bisect` is used to determine if an entity can be removed.
// Important: This function expects that the entities in `entities_to_minimize`
// are sorted by dependency rank and also that the entities are grouped by
// table, which follows from being sorted by dependency rank.
absl::Status TableBasedBisection(
    TestIfEntitiesCanBeRemoved test_if_entities_can_be_removed,
    const pdpi::IrEntities& entities_to_minimize);

}  // namespace dvaas

#endif  // PINS_DVAAS_FAILURE_POST_PROCESSING_H_
