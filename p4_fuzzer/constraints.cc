// Copyright 2024 Google LLC
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

#include "absl/container/flat_hash_set.h"
#include "absl/random/random.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "gutil/collections.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_constraints/ast.h"
#include "p4_constraints/backend/constraint_info.h"
#include "p4_constraints/backend/symbolic_interpreter.h"
#include "p4_fuzzer/fuzz_util.h"
#include "p4_fuzzer/fuzzer_config.h"
#include "p4_fuzzer/switch_state.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/ir_properties.h"
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
  return pdpi::HasP4RuntimeTranslatedType(match_field);
}

}  // namespace

bool UsesP4Constraints(int table_id, const FuzzerConfig& config) {
  auto* table_info =
      p4_constraints::GetTableInfoOrNull(config.GetConstraintInfo(), table_id);

  return table_info != nullptr && table_info->constraint.has_value() &&
         !config.GetIgnoreConstraintsOnTables().contains(table_info->name);
}

bool UsesP4Constraints(const pdpi::IrTableDefinition& table,
                       const FuzzerConfig& config) {
  return UsesP4Constraints(table.preamble().id(), config);
}

absl::StatusOr<TableEntry> FuzzValidConstrainedTableEntry(
    const FuzzerConfig& config, const SwitchState& switch_state,
    const pdpi::IrTableDefinition& table, absl::BitGen& gen) {
  auto* table_info = p4_constraints::GetTableInfoOrNull(
      config.GetConstraintInfo(), table.preamble().id());

  if (table_info == nullptr) {
    return gutil::InvalidArgumentErrorBuilder()
           << "given table with ID '" << table.preamble().id()
           << "' that does not exist in P4Info: " << table.preamble().alias();
  }
  if (!table_info->constraint.has_value()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "given table without P4-Constraints: "
           << table.preamble().alias();
  }

  absl::flat_hash_set<std::string> constrained_keys =
      p4_constraints::ast::GetVariables(*table_info->constraint);

  // We skip unconstrained keys, they will be fuzzed randomly after. Also, since
  // the p4_constraints API does not yet support P4 runtime translated types
  // (and will generate an InvalidArgumentError if it gets them). Thus, we skip
  // those keys and ensure they were optional.
  // TODO: Support P4RT translated types.
  auto skip_key = [&](absl::string_view key_name) -> absl::StatusOr<bool> {
    ASSIGN_OR_RETURN(bool has_p4rt_translated_type,
                     HasP4RuntimeTranslatedType(table, key_name));
    return !constrained_keys.contains(key_name) || has_p4rt_translated_type;
  };

  // Construct z3 context and solver.
  z3::context solver_context;
  z3::solver solver(solver_context);

  ASSIGN_OR_RETURN(
      p4_constraints::SymbolicEnvironment environment,
      p4_constraints::EncodeValidTableEntryInZ3(*table_info, solver, skip_key));

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
                   p4_constraints::ConcretizeEntry(model, *table_info,
                                                   environment, skip_key));

  // Fuzz all unconstrained keys normally.
  for (const auto& [name, match_field_def] : table.match_fields_by_name()) {
    if (!constrained_keys.contains(name)) {
      ASSIGN_OR_RETURN(
          *table_entry.add_match(),
          FuzzFieldMatch(&gen, config, switch_state, match_field_def));
    }
  }

  // Fuzz an action.
  // TODO: b/324084334 - Potentially remove when ConcretizeEntry returns an
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
