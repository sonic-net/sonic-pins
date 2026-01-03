#include "dvaas/failure_post_processing.h"

#include <algorithm>
#include <string>
#include <vector>

#include "absl/container/flat_hash_set.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "dvaas/packet_trace.pb.h"
#include "dvaas/test_vector.pb.h"
#include "google/protobuf/util/message_differencer.h"
#include "gutil/gutil/status.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/names.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesizer.pb.h"

namespace dvaas {

using ::google::protobuf::util::MessageDifferencer;

absl::Status DoEntityMinimization(
    TestIfEntitiesCanBeRemoved test_if_entities_can_be_removed,
    const pdpi::IrEntities& entities_to_minimize,
    MinimizationAlgorithm minimization_algorithm) {
  switch (minimization_algorithm) {
    case kTableBasedBisection:
      return TableBasedBisection(test_if_entities_can_be_removed,
                                 entities_to_minimize);
    case kRemoveEntitiesOneByOne:
      return RemoveEntitiesOneByOne(test_if_entities_can_be_removed,
                                    entities_to_minimize);
  }
  return absl::InvalidArgumentError(
      "Expected a valid MinimizationAlgorithm enum.");
}

// Uses the failure description to determine if the new failure is the same as
// the original failure.
// TODO: Come up with a better way to compare failures.
bool HasSameFailure(const dvaas::PacketTestOutcome& original_test_outcome,
                    const dvaas::PacketTestOutcome& new_test_outcome) {
  MessageDifferencer differencer;
  // Ignore ordering of repeated fields.
  differencer.TreatAsSet(
      PacketTestVector::descriptor()->FindFieldByName("acceptable_outputs"));
  differencer.TreatAsSet(
      SwitchOutput::descriptor()->FindFieldByName("packets"));
  differencer.TreatAsSet(
      SwitchOutput::descriptor()->FindFieldByName("packet_ins"));

  // Ignore irrelevant fields.
  differencer.IgnoreField(
      SwitchOutput::descriptor()->FindFieldByName("packet_trace"));
  differencer.IgnoreField(PacketTestRun::descriptor()->FindFieldByName(
      "input_packet_injection_time"));
  differencer.IgnoreField(
      PacketTestRun::descriptor()->FindFieldByName("labels"));
  return differencer.Compare(original_test_outcome.test_run(),
                             new_test_outcome.test_run());
}

absl::Status RemoveEntitiesOneByOne(
    TestIfEntitiesCanBeRemoved test_if_entities_can_be_removed,
    const pdpi::IrEntities& entities_to_minimize) {
  // Iterate backwards through the entities, remove the current entity from the
  // switch, and reinstall the entity on the switch if no failure occurs.
  constexpr int kSecsBetweenLogs = 30;
  int reinstall_attempts = 0;
  int iterations = 0;
  for (int i = entities_to_minimize.entities_size() - 1; i >= 0;
       --i && ++iterations) {
    LOG_EVERY_N_SEC(INFO, kSecsBetweenLogs)
        << "Loop has run " << iterations << " iterations, there are " << i
        << " remaining entities out of " << entities_to_minimize.entities_size()
        << " original ones and we have reinstalled " << reinstall_attempts
        << " of them.";

    // Store the `pi_entity` in case we need to reinstall it on the switch if no
    // failure occurs.
    pdpi::IrEntities entities_to_remove;
    *entities_to_remove.add_entities() = entities_to_minimize.entities(i);

    // Check if the entity can be removed from the switch while still
    // maintaining the same failure. In unit tests, we mock this function to
    // return true or false.
    ASSIGN_OR_RETURN(bool can_be_removed,
                     test_if_entities_can_be_removed(entities_to_remove));

    if (!can_be_removed) {
      reinstall_attempts++;
    }
  }
  return absl::OkStatus();
}

absl::Status TryToDeleteAndBisect(
    TestIfEntitiesCanBeRemoved test_if_entities_can_be_removed,
    const pdpi::IrEntities& entities) {
  if (entities.entities_size() == 0) return absl::OkStatus();

  // Check if the entities can be removed from the switch while still
  // maintaining the same failure.
  ASSIGN_OR_RETURN(bool can_be_removed,
                   test_if_entities_can_be_removed(entities));
  if (can_be_removed || entities.entities_size() == 1) {
    return absl::OkStatus();
  }
  pdpi::IrEntities entities_to_delete_1;
  pdpi::IrEntities entities_to_delete_2;
  {  // TODO: Improve performance by avoiding copying the entities.
    int counter = 0;
    for (const pdpi::IrEntity& entity : entities.entities()) {
      if (counter < entities.entities_size() / 2) {
        *entities_to_delete_1.add_entities() = entity;
      } else {
        *entities_to_delete_2.add_entities() = entity;
      }
      counter++;
    }
  }
  RETURN_IF_ERROR(TryToDeleteAndBisect(test_if_entities_can_be_removed,
                                       entities_to_delete_2));
  RETURN_IF_ERROR(TryToDeleteAndBisect(test_if_entities_can_be_removed,
                                       entities_to_delete_1));
  return absl::OkStatus();
}

absl::Status TableBasedBisection(
    TestIfEntitiesCanBeRemoved test_if_entities_can_be_removed,
    const pdpi::IrEntities& entities_to_minimize) {
  std::vector<pdpi::IrEntities> entities_by_table;
  {
    // Group the entities by table.
    absl::flat_hash_set<std::string> seen_table_names;
    std::string current_table_name;
    for (const pdpi::IrEntity& entity : entities_to_minimize.entities()) {
      if (!entity.has_table_entry() &&
          !entity.has_packet_replication_engine_entry())
        continue;
      // Assumes that the table name is always non-empty.
      ASSIGN_OR_RETURN(std::string table_name, pdpi::EntityToTableName(entity));
      if (table_name == current_table_name) {
        *entities_by_table.back().add_entities() = entity;
      } else {
        auto [it, inserted] = seen_table_names.insert(table_name);
        if (!inserted) {
          return absl::InvalidArgumentError(
              "Expected `entities_to_minimize` to be sorted by table "
              "dependency rank.");
        }
        current_table_name = table_name;
        *entities_by_table.emplace_back().add_entities() = entity;
      }
    }
  }

  // Iterate through the entities by table.
  std::reverse(entities_by_table.begin(), entities_by_table.end());
  for (const pdpi::IrEntities& entities : entities_by_table) {
    RETURN_IF_ERROR(
        TryToDeleteAndBisect(test_if_entities_can_be_removed, entities));
  }
  return absl::OkStatus();
}
}  // namespace dvaas
