#include "dvaas/failure_post_processing.h"

#include <functional>

#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "dvaas/packet_trace.pb.h"
#include "dvaas/test_vector.pb.h"
#include "google/protobuf/util/message_differencer.h"
#include "gutil/gutil/status.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesizer.pb.h"

namespace dvaas {

using ::google::protobuf::util::MessageDifferencer;

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

absl::Status EntityMinimizationLoop(
    const std::function<
        absl::StatusOr<bool>(const pdpi::IrEntity& entity_to_remove,
                             const pdpi::IrEntities& current_entities)>
        test_if_entity_can_be_removed,
    pdpi::IrEntities& entities_to_minimize) {
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
    pdpi::IrEntity entity = entities_to_minimize.entities(i);

    // Remove the entity from the result.
    entities_to_minimize.mutable_entities()->DeleteSubrange(i, 1);

    // Check if the entity can be removed from the switch while still
    // maintaining the same failure. In unit tests, we mock this function to
    // return true or false.
    ASSIGN_OR_RETURN(bool can_be_removed, test_if_entity_can_be_removed(
                                              entity, entities_to_minimize));
    if (!can_be_removed) {
      reinstall_attempts++;
      *entities_to_minimize.add_entities() = entity;
    }
  }
  return absl::OkStatus();
}
}  // namespace dvaas
