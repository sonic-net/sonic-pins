// Copyright 2021 Google LLC
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
#ifndef P4_FUZZER_MUTATION_H_
#define P4_FUZZER_MUTATION_H_

#include "absl/random/random.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_fuzzer/fuzzer.pb.h"
#include "p4_fuzzer/fuzzer_config.h"
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
                          const FuzzerConfig& config);

// Sets the action id of the table entry to a value that does not belong to
// any action in the P4 program.
void MutateInvalidActionId(absl::BitGen* gen, p4::v1::TableEntry* entry,
                           const FuzzerConfig& config);

// Sets the id of one of the match fields in the table entry to a value that
// does no belong to any table in the P4 program. Returns an error if the table
// entry contains no match fields.
absl::Status MutateInvalidMatchFieldId(absl::BitGen* gen,
                                       p4::v1::TableEntry* entry,
                                       const FuzzerConfig& config);

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
                                              const FuzzerConfig& config,
                                              const SwitchState& switch_state);

// This picks an action_profile_action and sets its weight to a non-positive
// integer. This is only intended for tables that support one-shot action
// selector programming.
absl::Status MutateInvalidActionSelectorWeight(absl::BitGen* gen,
                                               p4::v1::TableEntry* entry,
                                               const FuzzerConfig& config);

// This randomly selects an already inserted table entry from the switch state
// and sets the value of TableEntry* entry to that of the already inserted
// entry.
absl::Status MutateDuplicateInsert(absl::BitGen* gen, p4::v1::Update* update,
                                   const FuzzerConfig& config,
                                   const SwitchState& switch_state);

// This attempts to delete a table entry that does not exist in the switch.
absl::Status MutateNonexistingDelete(absl::BitGen* gen, p4::v1::Update* update,
                                     const FuzzerConfig& config,
                                     const SwitchState& switch_state);

// Applied a given mutation to the update.
absl::Status MutateUpdate(absl::BitGen* gen, const FuzzerConfig& config,
                          p4::v1::Update* update,
                          const SwitchState& switch_state,
                          const Mutation& mutation);
}  // namespace p4_fuzzer

#endif /* P4_FUZZER_MUTATION_H_ */
