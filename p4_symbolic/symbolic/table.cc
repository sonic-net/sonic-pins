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

// Contains functions used to symbolically evaluate P4 tables and their entries.
// A table is turned into a sequence of if-conditions (one per entry),
// each condition corresponds to having that entry matched on, and the
// corresponding then body invokes the appropriate symbolic action expression
// with the parameters specified in the entry.

#include "p4_symbolic/symbolic/table.h"

#include <cstddef>
#include <functional>
#include <string>
#include <utility>
#include <vector>

#include "absl/algorithm/container.h"
#include "absl/container/btree_map.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/types/optional.h"
#include "absl/types/span.h"
#include "google/protobuf/map.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_symbolic/ir/ir.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/symbolic/action.h"
#include "p4_symbolic/symbolic/context.h"
#include "p4_symbolic/symbolic/control.h"
#include "p4_symbolic/symbolic/operators.h"
#include "p4_symbolic/symbolic/solver_state.h"
#include "p4_symbolic/symbolic/symbolic_table_entry.h"
#include "p4_symbolic/symbolic/util.h"
#include "p4_symbolic/symbolic/values.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {
namespace table {

namespace {

absl::Span<const pdpi::IrMatch *const> GetMatches(const ir::TableEntry &entry) {
  switch (entry.entry_case()) {
    case ir::TableEntry::kConcreteEntry: {
      const pdpi::IrEntity &entity = entry.concrete_entry().pdpi_ir_entity();
      switch (entity.entity_case()) {
        case pdpi::IrEntity::kTableEntry:
          return absl::MakeConstSpan(entity.table_entry().matches());
        case pdpi::IrEntity::kPacketReplicationEngineEntry:
          LOG(FATAL)  // Crash OK: test infra.
              << "TODO: Add support for multicast entries";
        case pdpi::IrEntity::ENTITY_NOT_SET:
          break;
      }
      break;
    }
    case ir::TableEntry::kSymbolicEntry:
      return absl::MakeConstSpan(entry.symbolic_entry().sketch().matches());
    case ir::TableEntry::ENTRY_NOT_SET:
      break;
  }
  return {};
}

// Sort the given table entries by priority.
// The priority depends on the match types.
// If the table matches contain at least one ternary or optional match, the
// entries' `priority` fields must be non-zero and determine the matching
// priority.
// If no ternary or optional matches exist, there can be at most one lpm match,
// and the `priority` fields must be zero (unset) and have no effect.
// If no ternary or optional matches exist and there is an lpm match, there may
// be zero or more exact matches, and the priority is determined by the prefix
// length, such that longer prefixes have higher priority.
// Finally, if the matches only contain exact matches, there is no priority.
//
// The function returns a vector of pairs, where the second element is the table
// entry, and the first is its index in the old unsorted array. The pairs are
// sorted by priority, such that the element with highest priority appears
// first. Elements with equal priority retain their relative ordering.
//
// We return the old index so that Symbolic and Concrete TableMatches are
// set up against the indices as they appear in the input table entries array,
// and not the sorted array.
//
// References:
// - P4~16 v1.2.3 section 14.2.1.4
//   https://p4.org/p4-spec/docs/P4-16-v-1.2.3.html#sec-entries
// - P4Runtime v1.3.0 section 9.1
//   https://p4.org/p4-spec/p4runtime/main/P4Runtime-Spec.html#sec-table-entry
// - BMv2 - simple_switch.md
//   https://github.com/p4lang/behavioral-model/blob/main/docs/simple_switch.md#table-match-kinds-supported
//
std::vector<ir::TableEntry> SortedEntries(const ir::Table &table,
                                          std::vector<ir::TableEntry> entries) {
  if (entries.empty()) return {};

  // Find which *definition* of priority we should use by looking at the
  // table's match types.
  bool has_ternary_or_optional = false;
  absl::optional<std::string> lpm_match_name;
  for (const auto &[match_name, match_field_definition] :
       table.table_definition().match_fields_by_name()) {
    switch (match_field_definition.match_field().match_type()) {
      case p4::config::v1::MatchField::TERNARY:
      case p4::config::v1::MatchField::OPTIONAL: {
        has_ternary_or_optional = true;
        break;
      }
      case p4::config::v1::MatchField::LPM: {
        lpm_match_name = match_name;
        break;
      }
      default: {
        // Exact or some other unsupported type, no need to do anything here.
        // An absl error will be returned if the type is unsupported in
        // `EvaluateSingleMatch`.
        break;
      }
    }
  }

  // The sort comparator depends on the match types.
  std::function<bool(const ir::TableEntry &, const ir::TableEntry &)>
      comparator;
  if (has_ternary_or_optional) {
    // Sort by explicit priority.
    // Entries with numerically larger priority precede others.
    comparator = [](const auto &entry1, const auto &entry2) {
      return ir::GetPriority(entry1) > ir::GetPriority(entry2);
    };
  } else if (lpm_match_name.has_value()) {
    auto get_prefix_length = [&](const ir::TableEntry &entry) -> int {
      absl::Span<const pdpi::IrMatch *const> matches = GetMatches(entry);
      auto it = absl::c_find_if(matches, [&](const pdpi::IrMatch *match) {
        return match->name() == *lpm_match_name;
      });
      return it == matches.end() ? 0 : (**it).lpm().prefix_length();
    };
    // Sort by prefix length.
    // Entries with numerically larger prefix length precede others.
    comparator = [=](const auto &entry1, const auto &entry2) {
      return get_prefix_length(entry1) > get_prefix_length(entry2);
    };
  } else {
    return entries;
  }

  // Using stable_sort, we preserve the relative order of entries with the same
  // priority.
  absl::c_stable_sort(entries, comparator);
  return entries;
}

// Analyzes a single symbolic match of a table entry.
// Constructs a symbolic expression that semantically corresponds to the given
// symbolic match.
absl::StatusOr<z3::expr> EvaluateSymbolicMatch(
    const ir::SymbolicTableEntry &entry, absl::string_view match_name,
    const z3::expr &field_value, const ir::Table &table, SolverState &state) {
  ASSIGN_OR_RETURN(SymbolicMatch variables,
                   GetSymbolicMatch(entry, match_name, table, state.program,
                                    *state.context.z3_context));
  ASSIGN_OR_RETURN(z3::expr masked_field,
                   operators::BitAnd(field_value, variables.mask));
  return operators::Eq(masked_field, variables.value);
}

// Analyzes a single concrete match of a table entry.
// Constructs a symbolic expression that semantically corresponds to the given
// concrete match.
absl::StatusOr<z3::expr> EvaluateConcreteMatch(
    const pdpi::IrMatch &ir_match, const p4::config::v1::MatchField &pi_match,
    const std::string &field_name, const z3::expr &field_value,
    SolverState &state) {
  if (!pi_match.has_match_type()) {
    // Architecture-specific match type.
    return gutil::InvalidArgumentErrorBuilder()
           << "Found match with non-standard type";
  }

  // Translates the given `value` read from the match of a table entry into a Z3
  // expression.
  auto GetZ3Value =
      [&field_name, &pi_match,
       &state](const pdpi::IrValue &value) -> absl::StatusOr<z3::expr> {
    return values::FormatP4RTValue(
        value, field_name, pi_match.type_name().name(), pi_match.bitwidth(),
        *state.context.z3_context, state.translator);
  };

  absl::Status mismatch =
      gutil::InvalidArgumentErrorBuilder()
      << "match on field '" << field_name << "' must be of type "
      << p4::config::v1::MatchField::MatchType_Name(pi_match.match_type())
      << " according to the table definition, but got entry with match: "
      << ir_match.ShortDebugString();

  switch (pi_match.match_type()) {
    case p4::config::v1::MatchField::EXACT: {
      if (!ir_match.has_exact()) return mismatch;

      ASSIGN_OR_RETURN(z3::expr exact_value, GetZ3Value(ir_match.exact()));
      return operators::Eq(field_value, exact_value);
    }

    case p4::config::v1::MatchField::LPM: {
      if (!ir_match.has_lpm()) return mismatch;

      ASSIGN_OR_RETURN(z3::expr lpm_value, GetZ3Value(ir_match.lpm().value()));
      return operators::PrefixEq(
          field_value, lpm_value,
          static_cast<unsigned int>(ir_match.lpm().prefix_length()));
    }

    case p4::config::v1::MatchField::TERNARY: {
      if (!ir_match.has_ternary()) return mismatch;

      ASSIGN_OR_RETURN(z3::expr ternary_value,
                       GetZ3Value(ir_match.ternary().value()));
      ASSIGN_OR_RETURN(z3::expr ternary_mask,
                       GetZ3Value(ir_match.ternary().mask()));
      ASSIGN_OR_RETURN(z3::expr masked_field,
                       operators::BitAnd(field_value, ternary_mask));
      return operators::Eq(masked_field, ternary_value);
    }

    case p4::config::v1::MatchField::OPTIONAL: {
      if (!ir_match.has_optional()) return mismatch;

      // According to the P4Runtime spec, "for don't care matches, the P4Runtime
      // client must omit the field's entire FieldMatch entry when building the
      // match repeated field of the TableEntry message". Therefore, if the
      // match value is present for an optional match type, it must be a
      // concrete value.
      ASSIGN_OR_RETURN(z3::expr optional_value,
                       GetZ3Value(ir_match.optional().value()));
      return operators::Eq(field_value, optional_value);
    }

    default: {
      return gutil::UnimplementedErrorBuilder()
             << "Found unsupported match type " << pi_match.DebugString();
    }
  }
}

// Constructs a symbolic expression that is true if and only if this entry
// is matched on.
absl::StatusOr<z3::expr> EvaluateTableEntryCondition(
    const ir::Table &table, const ir::TableEntry &entry, SolverState &state,
    const SymbolicPerPacketState &headers) {
  const std::string &table_name = table.table_definition().preamble().name();
  const google::protobuf::Map<std::string, ::p4_symbolic::ir::FieldValue>
      &match_name_to_header_fields =
          table.table_implementation().match_name_to_field();
  const google::protobuf::Map<std::string, ::pdpi::IrMatchFieldDefinition>
      &match_definition_by_name =
          table.table_definition().match_fields_by_name();

  // Construct the match condition expression.
  z3::expr match_condition = state.context.z3_context->bool_val(true);

  // TODO: Consider sorting the matches before evaluating them to
  // ensure equivalent entries produce the same formulae.
  for (const pdpi::IrMatch *ir_match : GetMatches(entry)) {
    const std::string &match_name = ir_match->name();

    // Check if the match exists in the table definition.
    if (!match_definition_by_name.contains(match_name)) {
      return gutil::InvalidArgumentErrorBuilder()
             << "Match '" << match_name
             << "' not found in the definition of table '" << table_name << "'";
    }

    // We get the match name from pdpi/p4info for simplicity, however that file
    // only contains the match name as a string, which is the same as the match
    // target expression in most cases but not always.
    // For conciseness, we get the corresponding accurate match target from bmv2
    // by looking up the match name there.
    // In certain cases this is important, e.g. a match defined over field
    // "dstAddr" may have aliases of that field as a match name, but will always
    // have the fully qualified name of the field in the bmv2 format.
    if (!match_name_to_header_fields.contains(match_name)) {
      return gutil::InvalidArgumentErrorBuilder()
             << "Match '" << match_name
             << "' not found in the implementation of table '" << table_name
             << "'";
    }

    const p4::config::v1::MatchField &pi_match =
        match_definition_by_name.at(match_name).match_field();
    const ir::FieldValue &matched_field =
        match_name_to_header_fields.at(match_name);
    std::string field_name = absl::StrFormat(
        "%s.%s", matched_field.header_name(), matched_field.field_name());
    ASSIGN_OR_RETURN(z3::expr field_value,
                     action::EvaluateFieldValue(matched_field, headers));

    // Evaluate the condition of the specific match.
    z3::expr match_expression(*state.context.z3_context);
    switch (entry.entry_case()) {
      case ir::TableEntry::kConcreteEntry: {
        ASSIGN_OR_RETURN(match_expression,
                         EvaluateConcreteMatch(*ir_match, pi_match, field_name,
                                               field_value, state));
        break;
      }
      case ir::TableEntry::kSymbolicEntry: {
        ASSIGN_OR_RETURN(
            match_expression,
            EvaluateSymbolicMatch(entry.symbolic_entry(), match_name,
                                  field_value, table, state));
        break;
      }
      case ir::TableEntry::ENTRY_NOT_SET:
        return gutil::InvalidArgumentErrorBuilder()
               << "invalid table entry: " << absl::StrCat(entry);
    }

    ASSIGN_OR_RETURN(match_condition,
                     operators::And(match_condition, match_expression));
  }

  return match_condition;
}

absl::Status EvaluateSingeConcreteAction(const pdpi::IrActionInvocation &action,
                                         SolverState &state,
                                         SymbolicPerPacketState &headers,
                                         const z3::expr &guard) {
  const google::protobuf::Map<std::string, ir::Action> &actions =
      state.program.actions();

  // Check if the action invoked by entry exists.
  if (!actions.contains(action.name())) {
    return gutil::InvalidArgumentErrorBuilder()
           << "unknown action '" << action.name() << "'";
  }
  return action::EvaluateConcreteAction(actions.at(action.name()),
                                        action.params(), state, headers, guard);
}

absl::Status EvaluateSingleSymbolicAction(absl::string_view action_name,
                                          const ir::SymbolicTableEntry &entry,
                                          SolverState &state,
                                          SymbolicPerPacketState &headers,
                                          const z3::expr &guard) {
  const google::protobuf::Map<std::string, ir::Action> &actions =
      state.program.actions();

  // Check if the action from the table definition exists.
  if (!actions.contains(action_name)) {
    return gutil::InternalErrorBuilder()
           << "unknown action '" << action_name << "'";
  }
  return action::EvaluateSymbolicAction(actions.at(action_name), entry, state,
                                        headers, guard);
}

// Constructs a symbolic expressions that represents the action invocation
// corresponding to this entry.
absl::Status EvaluateTableEntryAction(const ir::Table &table,
                                      const ir::ConcreteTableEntry &entry,
                                      SolverState &state,
                                      SymbolicPerPacketState &headers,
                                      const z3::expr &guard) {
  switch (entry.pdpi_ir_entity().entity_case()) {
    case pdpi::IrEntity::kTableEntry: {
      const pdpi::IrTableEntry &ir_entry = entry.pdpi_ir_entity().table_entry();
      switch (ir_entry.type_case()) {
        case pdpi::IrTableEntry::kAction: {
          RETURN_IF_ERROR(EvaluateSingeConcreteAction(ir_entry.action(), state,
                                                      headers, guard))
                  .SetPrepend()
              << "In table entry '" << ir_entry.ShortDebugString() << "':";
          return absl::OkStatus();
        }
        case pdpi::IrTableEntry::kActionSet: {
          auto &action_set = ir_entry.action_set().actions();
          // For action sets, we introduce a new free integer variable
          // "selector" whose value determines which action is executed: to
          // a first approximation, action i is executed iff `selector ==
          // i`.
          std::string selector_name =
              absl::StrFormat("action selector for entry #%d of table '%s'",
                              entry.index(), ir_entry.table_name());
          z3::expr selector =
              state.context.z3_context->int_const(selector_name.c_str());
          z3::expr unselected = state.context.z3_context->bool_val(true);
          for (int i = 0; i < action_set.size(); ++i) {
            auto &action = action_set.at(i).action();
            bool is_last_action = i == action_set.size() - 1;
            z3::expr selected = is_last_action ? unselected : (selector == i);
            unselected = unselected && !selected;
	    // The incoming guard 'guard' is always true and hence the action is
            // evaluated only based on the selected bit.
            RETURN_IF_ERROR(
                EvaluateSingeConcreteAction(action, state, headers, selected))
                    .SetPrepend()
                << "In table entry '" << ir_entry.ShortDebugString() << "':";
          }
          return absl::OkStatus();
        }
        default:
          return gutil::InvalidArgumentErrorBuilder()
                 << "unexpected or missing action in table entry: "
                 << ir_entry.DebugString();
      }
    }
    case pdpi::IrEntity::kPacketReplicationEngineEntry: {
      return gutil::InternalErrorBuilder()
             << "did not expect packet replication engine entry on this "
                "control flow path: "
             << absl::StrCat(entry);
    }
    case pdpi::IrEntity::ENTITY_NOT_SET:
      break;
  }
  return gutil::InvalidArgumentErrorBuilder()
         << "invalid table entry: " << absl::StrCat(entry);
}

// Constructs a symbolic expressions that represents the action invocation
// corresponding to this entry.
absl::Status EvaluateTableEntryAction(
    const ir::Table &table, const ir::SymbolicTableEntry &symbolic_entry,
    SolverState &state, SymbolicPerPacketState &headers,
    const z3::expr &guard) {
  // Entries with symbolic action sets are not supported for now.
  if (table.table_definition().has_action_profile_id()) {
    return gutil::UnimplementedErrorBuilder()
           << "Table entries with symbolic action sets are not supported "
              "at the moment.";
  }

  // Evaluate each symbolic action of a symbolic table entry.
  for (const pdpi::IrActionReference &action_ref :
       table.table_definition().entry_actions()) {
    absl::string_view action_name = action_ref.action().preamble().name();
    ASSIGN_OR_RETURN(
        z3::expr action_is_applied,
        GetSymbolicActionInvocation(symbolic_entry, action_name, table,
                                    *state.context.z3_context));
    RETURN_IF_ERROR(EvaluateSingleSymbolicAction(action_name, symbolic_entry,
                                                 state, headers,
                                                 guard && action_is_applied));
  }

  return absl::OkStatus();
}

// Constructs a symbolic expressions that represents the action invocation
// corresponding to this entry.
absl::Status EvaluateTableEntryAction(const ir::Table &table,
                                      const ir::TableEntry &entry,
                                      SolverState &state,
                                      SymbolicPerPacketState &headers,
                                      const z3::expr &guard) {
  switch (entry.entry_case()) {
    case ir::TableEntry::kConcreteEntry:
      return EvaluateTableEntryAction(table, entry.concrete_entry(), state,
                                      headers, guard);
    case ir::TableEntry::kSymbolicEntry:
      return EvaluateTableEntryAction(table, entry.symbolic_entry(), state,
                                      headers, guard);
    case ir::TableEntry::ENTRY_NOT_SET:
      break;
  }
  return gutil::InvalidArgumentErrorBuilder()
         << "unexpected or missing action in table entry: "
         << absl::StrCat(entry);
}

}  // namespace

TableEntryPriorityType GetTableEntryPriorityType(const ir::Table &table) {
  for (const auto &[match_name, match_definition] :
       table.table_definition().match_fields_by_name()) {
    const auto &pi_match = match_definition.match_field();
    switch (pi_match.match_type()) {
      case p4::config::v1::MatchField::RANGE:
      case p4::config::v1::MatchField::TERNARY:
      case p4::config::v1::MatchField::OPTIONAL: {
        return TableEntryPriorityType::kPositivePriority;
      }
      case p4::config::v1::MatchField::LPM: {
        // Currently the P4 compiler does not allow more than one LPM match in a
        // table, so assuming there is at most one LPM match, it is sufficient
        // to return `kLpmWithZeroOrMoreExacts` here. Otherwise, we will need to
        // count the number of LPM matches.
        // Reference:
        // https://github.com/p4lang/behavioral-model/blob/main/docs/simple_switch.md#table-match-kinds-supported.
        return TableEntryPriorityType::kPriorityZeroWithSingleLpm;
      }

      default: {
        // Exact or some other unsupported type, no need to do anything here.
        // For unsupported types, an absl error will be returned during symbolic
        // evaluation.
        break;
      }
    }
  }
  return TableEntryPriorityType::kPriorityZero;
}

absl::StatusOr<SymbolicTableMatches> EvaluateTable(
    const ir::Table &table, SolverState &state, SymbolicPerPacketState &headers,
    const z3::expr &guard) {
  const std::string &table_name = table.table_definition().preamble().name();

  // Sort entries by priority deduced from match types.
  std::vector<ir::TableEntry> sorted_entries;
  if (auto it = state.context.table_entries.find(table_name);
      it != state.context.table_entries.end()) {
    sorted_entries = SortedEntries(table, it->second);
  }

  // The table semantically is just a bunch of if conditions, one per
  // table entry, we construct this big if-elseif-...-else symbolically.
  //
  // We have to be careful about the nesting order. We should have:
  // <header_field x> =
  //   if <guard && condition[0]>
  //     then <effects of entry[0] on x>
  //     else if <guard && condition[1]>
  //       then <effects of entry[1] on x>
  //       else ...
  //         ...
  //         else <effects of default entry on x>
  //
  //
  // This is important, because condition[1] may be true in cases where
  // condition[0] is also true. But entry[0] has priority over entry[1].
  //
  // We do this by traversing in reverse priority order: from least to highest
  // priority, since we are building the if-then-...-else statement inside out.
  //
  // Another thing to be careful about is making sure that any effects of one
  // entry or its action are not visible when evaluating other actions,
  // regardless of priority. I.e., if the effects of entry[1] refer to the value
  // of field y, that value must be guarded properly so that if entry[0] or
  // entry[2] assign a value to it, that value is unused by this reference.
  // 
  // We do this by introducing a local map of headers for each entry.
  // The local map is a copy of the incoming headers, but the action of each
  // entry can modify the local map without affecting the incoming headers.
  // Then, when we merge the results of each entry, using the entry's match
  // expressions according to their priority order
  // (see go/p4-symbolic-guard-factorization).

  // Find all entries match conditions.
  std::vector<z3::expr> entries_matches;
  for (const auto &entry : sorted_entries) {
    ASSIGN_OR_RETURN(z3::expr entry_match,
                     EvaluateTableEntryCondition(table, entry, state, headers));
    entries_matches.push_back(entry_match);
  }

  // Build a TableEntry object for the default entry.
  ir::TableEntry default_entry;
  default_entry.mutable_concrete_entry()->set_index(kDefaultActionEntryIndex);
  auto &default_action = *default_entry.mutable_concrete_entry()
                              ->mutable_pdpi_ir_entity()
                              ->mutable_table_entry()
                              ->mutable_action();
  default_action.set_name(table.table_implementation().default_action());
  for (const std::string &parameter_value :
       table.table_implementation().default_action_parameters()) {
    ASSIGN_OR_RETURN(*default_action.add_params()->mutable_value(),
                     values::ParseIrValue(parameter_value));
  }

  // Create a SymbolicPerPacketState (local map) for each table entry.
  // Duplicate existing headers (incoming) to individual local headers
  // for each entry.
  std::vector<SymbolicPerPacketState> local_header_per_table_entry(
      sorted_entries.size() + 1, headers);

  // Start with the default entry
  z3::expr match_index =
      state.context.z3_context->int_val(kDefaultActionEntryIndex);
  RETURN_IF_ERROR(EvaluateTableEntryAction(
      table, default_entry, state,
      local_header_per_table_entry[sorted_entries.size()],
      state.context.z3_context->bool_val(true)));

  // Continue evaluating each table entry.
  for (int row = sorted_entries.size() - 1; row >= 0; row--) {
    const ir::TableEntry &entry = sorted_entries.at(row);
    z3::expr row_symbol =
        state.context.z3_context->int_val(ir::GetIndex(entry));

    // The condition used in the big if_else_then construct.
    ASSIGN_OR_RETURN(z3::expr entry_match,
                     operators::And(guard, entries_matches.at(row)));
    ASSIGN_OR_RETURN(match_index,
                     operators::Ite(entry_match, row_symbol, match_index));

    // Evaluate the entry's action and update the local headers map.
    // We pass `true` as the guard expression here (effectively no guard).
    // The proper guard is applied during the merge process (see below).
    RETURN_IF_ERROR(EvaluateTableEntryAction(
        table, entry, state, local_header_per_table_entry[row],
        state.context.z3_context->bool_val(true)));
  }

  // Merge process:
  // Iterate through each field and merge the results of each entry.
  // The iteration is done in reverse order to ensure that the result of the
  // higher priority entry takes precedence over the lower priority entry.
  // The merge is done using the following formula
  // (for every field in the header):
  // resulting_header_field_value =
  //   if entries_matches[0]
  //     then local_header_per_table_entry[0].Get(field)
  //     else if entries_matches[1]
  //       then local_header_per_table_entry[1].Get(field)
  //       else ...
  //         ...
  //         else local_header_per_table_entry[n].Get(field)
  // At the end, the resulting_header_field_value is assigned to the
  // field in the resulting header
  for (const auto &[field, _] : headers) {
    ASSIGN_OR_RETURN(
        z3::expr resulting_header_field_value,
        local_header_per_table_entry[sorted_entries.size()].Get(field));

    for (int row = sorted_entries.size() - 1; row >= 0; row--) {
      ASSIGN_OR_RETURN(z3::expr local_header_field_value,
                       local_header_per_table_entry[row].Get(field));
      ASSIGN_OR_RETURN(
          resulting_header_field_value,
          operators::Ite(entries_matches.at(row), local_header_field_value,
                         resulting_header_field_value));
    }
    RETURN_IF_ERROR(headers.Set(field, resulting_header_field_value, guard));
  }

  const std::string &merge_point = table.table_implementation()
                                       .optimized_symbolic_execution_info()
                                       .merge_point();

  SymbolicTableMatches merged_matches;

  // We use a sorted map to keep the result (i.e. the SMT formula)
  // deterministic.
  absl::btree_map<std::string, std::string> sorted_action_to_next_control(
      table.table_implementation().action_to_next_control().begin(),
      table.table_implementation().action_to_next_control().end());

  // We currently do not support conditionals on which action was executed as
  // a result of table application. We do support conditional on table
  // hit/miss though.
  for (const auto &[action, next_control] : sorted_action_to_next_control) {
    if (next_control != merge_point) {
      if (action == ir::TableHitAction() || action == ir::TableMissAction()) {
        z3::expr branch_condition =
            action == ir::TableHitAction()
                ? (match_index != kDefaultActionEntryIndex)
                : (match_index == kDefaultActionEntryIndex);
        z3::expr next_guard = guard && branch_condition;
        next_guard = next_guard.simplify();
        ASSIGN_OR_RETURN(
            SymbolicTableMatches branch_matches,
            control::EvaluateControl(next_control, state, headers, next_guard));
        ASSIGN_OR_RETURN(merged_matches,
                         util::MergeMatchesOnCondition(
                             branch_condition, branch_matches, merged_matches,
                             *state.context.z3_context));
      } else {
        return absl::UnimplementedError(
            absl::Substitute("Conditional on executed table action is not "
                             "supported (table '$0', action '$1')",
                             table_name, action));
      }
    }
  }

  const std::string continuation = table.table_implementation()
                                           .optimized_symbolic_execution_info()
                                           .continue_to_merge_point()
                                       ? merge_point
                                       : ir::EndOfPipeline();

  // Evaluate the next control.
  ASSIGN_OR_RETURN(
      SymbolicTableMatches result,
      control::EvaluateControl(continuation, state, headers, guard));
  // Merge the result of execution from the merge point with the result of
  // execution from action_to_next_control (up to the merge point).
  ASSIGN_OR_RETURN(result,
                   util::MergeDisjointTableMatches(result, merged_matches));
  // Add the table match for the current table to the result.
  auto [_, inserted] =
      result.insert({table_name, SymbolicTableMatch{
                                     .matched = guard,
                                     .entry_index = match_index,
                                 }});
  // The trace should not contain information for this table, otherwise, it
  // means we visited the table twice in the same execution path!
  if (!inserted) {
    return absl::InternalError(absl::Substitute(
        "Table '$0' was executed twice in the same path.", table_name));
  }

  return result;
}

// Evaluate Table using DFS style symbolic execution
// This is currently being used to generate packets for path coverage
// (go/p4-symbolic-path-coverage).
absl::Status EvaluateTableDfs(
    const ir::Table &table, SolverState &state, SymbolicPerPacketState &headers,
    const std::string &pipeline_name,
    packet_synthesizer::PacketSynthesisResults &results) {
  const std::string &table_name = table.table_definition().preamble().name();

  // Sort entries by priority deduced from match types.
  std::vector<ir::TableEntry> sorted_entries;
  if (auto it = state.context.table_entries.find(table_name);
      it != state.context.table_entries.end()) {
    sorted_entries = SortedEntries(table, it->second);
  }

  // Find all entries match conditions.
  std::vector<z3::expr> entries_matches;
  for (const auto &entry : sorted_entries) {
    ASSIGN_OR_RETURN(z3::expr entry_match,
                     EvaluateTableEntryCondition(table, entry, state, headers));
    entries_matches.push_back(entry_match);
  }

  // Build a TableEntry object for the default entry.
  ir::TableEntry default_entry;
  default_entry.mutable_concrete_entry()->set_index(kDefaultActionEntryIndex);

  auto &default_action = *default_entry.mutable_concrete_entry()
                              ->mutable_pdpi_ir_entity()
                              ->mutable_table_entry()
                              ->mutable_action();
  default_action.set_name(table.table_implementation().default_action());
  for (const std::string &parameter_value :
       table.table_implementation().default_action_parameters()) {
    ASSIGN_OR_RETURN(*default_action.add_params()->mutable_value(),
                     values::ParseIrValue(parameter_value));
  }

  // Evaluate every table entry one-by-one.
  // For every table entry, the match condition is added to the
  // solver state to check if the path (with this entry) is satisfiable.
  // If there is no solution, then the table entry is not evaluated
  // and the path following this table entry is pruned and the execution
  // moves to the next entry.
  // If the path is valid (a solution exists), then the execution moves to the
  // next control point.
  state.solver->push();
  for (int row = 0; row < sorted_entries.size(); row++) {
    // DFS style symbolic execution for every table entry.
    state.solver->push();
    state.solver->add(entries_matches.at(row));
    auto prune = (state.solver->check() == z3::unsat);
    if (!prune) {
      auto local_headers = headers;
      RETURN_IF_ERROR(EvaluateTableEntryAction(
          table, sorted_entries.at(row), state, local_headers,
          state.context.z3_context->bool_val(true)));
      auto next_control = table.table_implementation()
                              .optimized_symbolic_execution_info()
                              .merge_point();
      RETURN_IF_ERROR(control::EvaluateControlDfs(
          next_control, state, local_headers, pipeline_name, results));
    }
    state.solver->pop();
    ASSIGN_OR_RETURN(z3::expr not_match,
                     operators::Not(entries_matches.at(row)));
    state.solver->add(not_match);
  }
  // Finally, the DFS-style symbolic execution
  // is done for the default entry as well.
  auto prune = (state.solver->check() == z3::unsat);
  if (!prune) {
    auto local_headers = headers;
    RETURN_IF_ERROR(
        EvaluateTableEntryAction(table, default_entry, state, local_headers,
                                 state.context.z3_context->bool_val(true)));
    auto next_control = table.table_implementation()
                            .optimized_symbolic_execution_info()
                            .merge_point();
    RETURN_IF_ERROR(control::EvaluateControlDfs(
        next_control, state, local_headers, pipeline_name, results));
  }
  state.solver->pop();

  return absl::OkStatus();
}

}  // namespace table
}  // namespace symbolic
}  // namespace p4_symbolic
