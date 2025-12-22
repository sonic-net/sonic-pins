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
#include <optional>
#include <string>
#include <utility>

#include "absl/container/flat_hash_set.h"
#include "absl/random/random.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "gutil/collections.h"
#include "gutil/ordered_map.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_constraints/ast.h"
#include "p4_constraints/ast.pb.h"
#include "p4_constraints/backend/constraint_info.h"
#include "p4_constraints/backend/symbolic_interpreter.h"
#include "p4_constraints/backend/type_checker.h"
#include "p4_constraints/constraint_source.h"
#include "p4_constraints/frontend/constraint_kind.h"
#include "p4_constraints/frontend/parser.h"
#include "p4_fuzzer/fuzz_util.h"
#include "p4_fuzzer/fuzzer_config.h"
#include "p4_fuzzer/switch_state.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/ir_properties.h"

namespace p4_fuzzer {
namespace {

using ::p4::v1::TableEntry;
using ::p4_constraints::ConstraintKind;
using ::p4_constraints::ConstraintSolver;
using ::p4_constraints::ConstraintSource;
using ::p4_constraints::InferAndCheckTypes;
using ::p4_constraints::ast::Expression;
using ::p4_constraints::ast::SourceLocation;

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
    const pdpi::IrTableDefinition& table, absl::BitGen& gen,
    std::optional<absl::string_view> additional_constraint) {
  auto* table_info = p4_constraints::GetTableInfoOrNull(
      config.GetConstraintInfo(), table.preamble().id());

  if (table_info == nullptr) {
    return gutil::InvalidArgumentErrorBuilder()
           << "given table with ID '" << table.preamble().id()
           << "' that does not exist in P4Info: " << table.preamble().alias();
  }
  if (!table_info->constraint.has_value() &&
      !additional_constraint.has_value()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "given table without P4-Constraints or additional constraint: "
           << table.preamble().alias();
  }

  std::optional<Expression> additional_constraint_ast;
  ConstraintSource additional_constraint_source;
  if (additional_constraint.has_value()) {
    // TODO: - Create a free function to generate the AST and source
    // to avoid duplicating this code across several places.
    SourceLocation location;
    location.set_table_name(table.preamble().alias());
    additional_constraint_source = ConstraintSource{
        .constraint_string = std::string(*additional_constraint),
        .constraint_location = std::move(location),
    };
    ASSIGN_OR_RETURN(additional_constraint_ast,
                     ParseConstraint(ConstraintKind::kTableConstraint,
                                     additional_constraint_source));
    RETURN_IF_ERROR(
        InferAndCheckTypes(&*additional_constraint_ast, *table_info));
  }

  absl::flat_hash_set<std::string> constrained_keys;
  if (table_info->constraint.has_value()) {
    constrained_keys.merge(GetVariables(*table_info->constraint));
  }

  if (additional_constraint_ast.has_value()) {
    constrained_keys.merge(GetVariables(*additional_constraint_ast));
  }

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
  ASSIGN_OR_RETURN(ConstraintSolver constraint_solver,
                   ConstraintSolver::Create(*table_info, skip_key));

  if (additional_constraint_ast.has_value()) {
    ASSIGN_OR_RETURN(bool constraint_added, constraint_solver.AddConstraint(
                                                *additional_constraint_ast,
                                                additional_constraint_source));
    if (!constraint_added) {
      return gutil::InvalidArgumentErrorBuilder()
             << "additional constraint '" << *additional_constraint
             << "' not added. The conjunction of the table constraint and "
                "additional constraint was unsatisfiable.";
    }
  }

  // Try to add some randomness to get more unique entries by attempting to fuzz
  // priority, skipping if the initial value yields an unsatisfiable constraint.
  if (table.requires_priority()) {
    RETURN_IF_ERROR(constraint_solver
                        .AddConstraint(absl::Substitute(
                            "::priority == $0",
                            static_cast<int>(FuzzUint64(&gen, /*bits=*/16))))
                        .status());
  }

  // TODO: Add additional randomness for match fields too before
  // generating a model.

  ASSIGN_OR_RETURN(TableEntry table_entry, constraint_solver.ConcretizeEntry());

  // Construct a set of match field names that are disabled for constraint
  // fuzzing.
  // Disabled match fields are expressed as fully qualified names but
  // constraint solver operates with match field names without table names
  // as prefix so we need this set to translate between the two.
  absl::flat_hash_set<std::string> disabled_keys_for_constraint_solver;
  for (const auto& [name, match_field_def] : table.match_fields_by_name()) {
    ASSIGN_OR_RETURN(std::string fully_qualified_name,
                     GetFullyQualifiedMatchFieldName(table, match_field_def));
    if (IsDisabledForFuzzing(config, fully_qualified_name)) {
      disabled_keys_for_constraint_solver.insert(name);
    }
  }

  TableEntry table_entry_without_disabled_fields = table_entry;
  table_entry_without_disabled_fields.clear_match();
  for (const auto& match : table_entry.match()) {
    if (disabled_keys_for_constraint_solver.contains(
            config.GetIrP4Info()
                .tables_by_id()
                .at(table_entry.table_id())
                .match_fields_by_id()
                .at(match.field_id())
                .match_field()
                .name())) {
      continue;
    }
    *table_entry_without_disabled_fields.add_match() = match;
  }

  // Fuzz all skipped keys normally.
  for (const auto& [name, match_field_def] :
       gutil::AsOrderedView(table.match_fields_by_name())) {
    ASSIGN_OR_RETURN(std::string fully_qualified_name,
                     GetFullyQualifiedMatchFieldName(table, match_field_def));
    if (IsDisabledForFuzzing(config, fully_qualified_name)) {
      continue;
    }
    // Skip omittable match fields with probability specified in config.
    if (pdpi::IsOmittable(match_field_def) &&
        absl::Bernoulli(gen, config.GetMatchFieldWildcardProbability())) {
      continue;
    }
    ASSIGN_OR_RETURN(bool key_skipped, skip_key(name));
    if (key_skipped) {
      ASSIGN_OR_RETURN(
          *table_entry_without_disabled_fields.add_match(),
          FuzzFieldMatch(&gen, config, switch_state, match_field_def));
    }
  }

  // Fuzz an action.
  // TODO: - Potentially remove when ConcretizeEntry returns an
  // action too.
  ASSIGN_OR_RETURN(
      *table_entry_without_disabled_fields.mutable_action(),
      FuzzAction(&gen, config, switch_state, table),
      _.SetPrepend()
          << "while fuzzing action for a P4-Constraint based table entry: ");

  // Set metadata to ensure the field works correctly.
  table_entry_without_disabled_fields.set_metadata(
      absl::StrCat("some_integer_metadata: ", FuzzUint64(&gen, /*bits=*/64)));

  return table_entry_without_disabled_fields;
}

}  // namespace p4_fuzzer
