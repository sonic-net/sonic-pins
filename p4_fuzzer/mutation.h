#ifndef P4_FUZZER_MUTATION_H_
#define P4_FUZZER_MUTATION_H_

#include "absl/random/random.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_fuzzer/fuzzer.pb.h"
#include "p4_fuzzer/switch_state.h"

namespace p4_fuzzer {

// TODO: implement.
// Takes a valid table entry with N fields, picks fields and changes their value
// to randomly generated ones of the same type. This does not *need* to result
// in an invalid table entry but *may* result in one.
// void MutateInvalidGeneric(p4::v1::TableEntry* entry);

// Sets the table id of the table entry to a value that does no belong to any
// table in the P4 program.
void MutateInvalidTableId(absl::BitGen* gen, p4::v1::TableEntry* entry,
                          const pdpi::IrP4Info& ir_p4_info);

// Sets the action id of the table entry to a value that does not belong to
// any action in the P4 program.
void MutateInvalidActionId(absl::BitGen* gen, p4::v1::TableEntry* entry,
                           const pdpi::IrP4Info& ir_p4_info);

// Sets the id of one of the match fields in the table entry to a value that
// does no belong to any table in the P4 program. Returns an error if the table
// entry contains no match fields.
absl::Status MutateInvalidMatchFieldId(absl::BitGen* gen,
                                       p4::v1::TableEntry* entry,
                                       const pdpi::IrP4Info& ir_p4_info);

// Changes the number of match fields sent via a table entry to an invalid
// smaller value e.g 4 fields sent for a table that matches on 3.
absl::Status MutateMissingMandatoryMatchField(absl::BitGen* gen,
                                              p4::v1::TableEntry* entry);

// Adds a duplicate for an already existing match field e.g two copies of match
// field id 3.
absl::Status MutateDuplicateMatchField(absl::BitGen* gen,
                                       p4::v1::TableEntry* entry);

// Changes a table entry with an ActionProfileActionSet (intended for tables
// that implement one-shot action selector programming) to a table that
// expects a single action and vice versa.
absl::Status MutateInvalidTableImplementation(absl::BitGen* gen,
                                              p4::v1::TableEntry* entry,
                                              const pdpi::IrP4Info& ir_p4_info);

// This picks an action_profile_action and sets its weight to a non-positive
// integer. This is only intended for tables that support one-shot action
// selector programming.
absl::Status MutateInvalidActionSelectorWeight(
    absl::BitGen* gen, p4::v1::TableEntry* entry,
    const pdpi::IrP4Info& ir_p4_info);

// This randomly selects an already inserted table entry from the switch state
// and sets the value of TableEntry* entry to that of the already inserted
// entry.
absl::Status MutateDuplicateInsert(absl::BitGen* gen, p4::v1::Update* update,
                                   const pdpi::IrP4Info& ir_p4_info,
                                   const SwitchState& switch_state);

// This attempts to delete a table entry that does not exist in the switch.
absl::Status MutateNonexistingDelete(absl::BitGen* gen, p4::v1::Update* update,
                                     const pdpi::IrP4Info& ir_p4_info,
                                     const SwitchState& switch_state);

// Applied a given mutation to the update.
absl::Status MutateUpdate(absl::BitGen* gen, p4::v1::Update* update,
                          const pdpi::IrP4Info& ir_p4_info,
                          const SwitchState& switch_state,
                          const Mutation& mutation);
}  // namespace p4_fuzzer

#endif /* P4_FUZZER_MUTATION_H_ */
