// Copyright 2023 Google LLC
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

#include "p4_fuzzer/constraints.h"

#include <functional>
#include <string>
#include <utility>

#include "absl/container/flat_hash_map.h"
#include "absl/random/random.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "gutil/collections.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_constraints/backend/constraint_info.h"
#include "p4_constraints/backend/symbolic_interpreter.h"
#include "p4_fuzzer/fuzz_util.h"
#include "p4_fuzzer/fuzzer_config.h"
#include "p4_fuzzer/switch_state.h"
#include "p4_pdpi/ir.pb.h"
#include "z3++.h"

namespace p4_fuzzer {
namespace {

using ::p4::v1::TableEntry;

// Checks whether a key has a P4 runtime translated type.
absl::StatusOr<bool> HasP4RuntimeTranslatedType(
    const pdpi::IrTableDefinition& table, absl::string_view key_name) {
  ASSIGN_OR_RETURN(pdpi::IrMatchFieldDefinition match_field,
                   gutil::FindOrStatus(table.match_fields_by_name(), key_name));
  // It's never a p4runtime translated type if it doesn't have a type name.
  return match_field.match_field().has_type_name() &&
         match_field.format() == pdpi::Format::STRING;
}

}  // namespace

bool UsesP4Constraints(int table_id, const FuzzerConfig& config) {
  auto it = config.GetConstraintInfo().find(table_id);
  if (it == config.GetConstraintInfo().end()) {
    return false;
  }
  return it->second.constraint.has_value();
}

bool UsesP4Constraints(const pdpi::IrTableDefinition& table,
                       const FuzzerConfig& config) {
  return UsesP4Constraints(table.preamble().id(), config);
}

absl::StatusOr<TableEntry> FuzzValidConstrainedTableEntry(
    const FuzzerConfig& config, const SwitchState& switch_state,
    const pdpi::IrTableDefinition& table, absl::BitGen& gen) {
  auto it = config.GetConstraintInfo().find(table.preamble().id());
  if (it == config.GetConstraintInfo().end()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "given table with ID '" << table.preamble().id()
           << "' that does not exist in P4Info: " << table.preamble().alias();
  }
  const p4_constraints::TableInfo& table_info = it->second;
  if (!table_info.constraint.has_value()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "given table without P4-Constraints: "
           << table.preamble().alias();
  }

  // Since the p4_constraints API does not yet support P4 runtime translated
  // types (and will generate an InvalidArgumentError if it gets them). Thus, we
  // skip those keys and ensure they were optional.
  // TODO: Support P4RT translated types.
  auto skip_key = [&](absl::string_view key_name) -> absl::StatusOr<bool> {
    ASSIGN_OR_RETURN(bool has_p4rt_type,
                     HasP4RuntimeTranslatedType(table, key_name));
    if (has_p4rt_type) {
      ASSIGN_OR_RETURN(
          pdpi::IrMatchFieldDefinition match_field,
          gutil::FindOrStatus(table.match_fields_by_name(), key_name));
      if (match_field.match_field().match_type() ==
          p4::config::v1::MatchField::EXACT) {
        return gutil::UnimplementedErrorBuilder()
               << "Given a P4Info where match field '" << key_name
               << "' in table '" << table.preamble().alias()
               << "' was a P4Runtime translated type AND exact. Currently, "
                  "only one of those is supported simultaneously. Table:\n"
               << table.DebugString();
      }
      return true;
    }
    return false;
  };

  // Construct z3 context and solver.
  z3::context solver_context;
  z3::solver solver(solver_context);

  ASSIGN_OR_RETURN(
      p4_constraints::SymbolicEnvironment environment,
      p4_constraints::EncodeValidTableEntryInZ3(table_info, solver, skip_key));

  // Try to add some randomness to get more unique entries by attempting to fuzz
  // priority, skipping if the initial value yields an unsatisfiable constraint.
  if (table.requires_priority()) {
    ASSIGN_OR_RETURN(
        const p4_constraints::SymbolicAttribute symbolic_priority,
        gutil::FindOrStatus(environment.symbolic_attribute_by_name,
                            p4_constraints::kSymbolicPriorityAttributeName));

    solver.push();
    solver.add(symbolic_priority.value ==
               static_cast<int>(FuzzUint64(&gen, /*bits=*/16)));
    if (solver.check() != z3::sat) {
      solver.pop();
    }
  }

  // TODO: Add additional randomness for match fields too before
  // generating a model.

  // Solve and check satisfiability.
  switch (solver.check()) {
    case z3::unsat:
      return gutil::InvalidArgumentErrorBuilder()
             << "unsatisfiable constraint:\n"
             << solver.to_smt2();
    case z3::unknown:
      return gutil::InvalidArgumentErrorBuilder()
             << "Unknown constraint solution";
    case z3::sat:
      // Constraint was satisfiable, so we get a solution from the model.
      break;
  }
  z3::model model = solver.get_model();

  ASSIGN_OR_RETURN(TableEntry table_entry,
                   p4_constraints::ConcretizeEntry(model, table_info,
                                                   environment, skip_key));

  // Fuzz an action.
  // TODO: Potentially remove when ConcretizeEntry returns an
  // action too.
  ASSIGN_OR_RETURN(
      *table_entry.mutable_action(),
      FuzzAction(&gen, config, switch_state, table),
      _.SetPrepend()
          << "while fuzzing action for a P4-Constraint based table entry: ");

  // Set metadata to ensure the field works correctly.
  table_entry.set_metadata(
      absl::StrCat("some_integer_metadata: ", FuzzUint64(&gen, /*bits=*/64)));

  return table_entry;
}

}  // namespace p4_fuzzer
