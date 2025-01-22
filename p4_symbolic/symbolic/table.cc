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

#include <algorithm>
#include <cstddef>
#include <functional>
#include <string>
#include <utility>
#include <vector>

#include "absl/container/btree_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/substitute.h"
#include "absl/types/optional.h"
#include "google/protobuf/map.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_pdpi/internal/ordered_map.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_symbolic/ir/ir.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/symbolic/action.h"
#include "p4_symbolic/symbolic/context.h"
#include "p4_symbolic/symbolic/control.h"
#include "p4_symbolic/symbolic/operators.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/symbolic/table_entry.h"
#include "p4_symbolic/symbolic/util.h"
#include "p4_symbolic/symbolic/values.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {
namespace table {

namespace {

// Finds a match field with the given match name in the given table entry.
// Returns the index of that match field inside the matches array in entry, or
// -1 if no such match was found.
int FindMatchWithName(const pdpi::IrTableEntry &entry,
                      const std::string &name) {
  int index = -1;
  for (int i = 0; i < entry.matches_size(); i++) {
    if (entry.matches(i).name() == name) {
      index = i;
      break;
    }
  }
  return index;
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
std::vector<TableEntry> SortEntries(const ir::Table &table,
                                    const std::vector<TableEntry> &entries) {
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

  // The output array.
  std::vector<TableEntry> sorted_entries(entries);

  // The sort comparator depends on the match types.
  std::function<bool(const TableEntry &, const TableEntry &)> comparator;
  if (has_ternary_or_optional) {
    // Sort by explicit priority.
    // Entries with numerically larger priority precede others.
    comparator = [](const TableEntry &entry1, const TableEntry &entry2) {
      return entry1.GetPdpiIrTableEntry().priority() >
             entry2.GetPdpiIrTableEntry().priority();
    };
  } else if (lpm_match_name.has_value()) {
    // Sort by prefix length.
    // Entries with numerically larger prefix length precede others.
    comparator = [&lpm_match_name](const TableEntry &entry1,
                                   const TableEntry &entry2) {
      auto is_lpm_match =
          [&lpm_match_name](const pdpi::IrMatch &match) -> bool {
        return match.name() == *lpm_match_name;
      };

      auto get_prefix_length = [&is_lpm_match](const TableEntry &entry) -> int {
        auto &matches = entry.GetPdpiIrTableEntry().matches();
        auto it = std::find_if(matches.begin(), matches.end(), is_lpm_match);
        return it == matches.end() ? 0 : it->lpm().prefix_length();
      };

      return get_prefix_length(entry1) > get_prefix_length(entry2);
    };
  } else {
    return sorted_entries;
  }

  // Using stable_sort, we preserve the relative order of entries with the same
  // priority.
  std::stable_sort(sorted_entries.begin(), sorted_entries.end(), comparator);
  return sorted_entries;
}

// Analyze a single match that is part of a table entry.
// Constructs a symbolic expression that semantically corresponds to this match.
absl::StatusOr<z3::expr> EvaluateSingleMatch(
    const p4::config::v1::MatchField &match_definition,
    const std::string &field_name, const z3::expr &field_expression,
    const pdpi::IrMatch &match, SolverState &state) {
  if (match_definition.match_case() != p4::config::v1::MatchField::kMatchType) {
    // Arch-specific match type.
    return absl::InvalidArgumentError(
        absl::StrCat("Found match with non-standard type"));
  }

  absl::Status mismatch =
      gutil::InvalidArgumentErrorBuilder()
      << "match on field '" << field_name << "' must be of type "
      << p4::config::v1::MatchField::MatchType_Name(
             match_definition.match_type())
      << " according to the table definition, but got entry with match: "
      << match_definition.ShortDebugString();

  auto GetZ3Value =
      [&](const pdpi::IrValue &value) -> absl::StatusOr<z3::expr> {
    return values::FormatP4RTValue(field_name,
                                   match_definition.type_name().name(), value,
                                   match_definition.bitwidth(),
                                   *state.context.z3_context, state.translator);
  };

  switch (match_definition.match_type()) {
    case p4::config::v1::MatchField::EXACT: {
      if (match.match_value_case() != pdpi::IrMatch::kExact) return mismatch;
      ASSIGN_OR_RETURN(z3::expr value_expression, GetZ3Value(match.exact()));
      return operators::Eq(field_expression, value_expression);
    }

    case p4::config::v1::MatchField::LPM: {
      if (match.match_value_case() != pdpi::IrMatch::kLpm) return mismatch;

      ASSIGN_OR_RETURN(z3::expr value_expression,
                       GetZ3Value(match.lpm().value()));
      return operators::PrefixEq(
          field_expression, value_expression,
          static_cast<unsigned int>(match.lpm().prefix_length()));
    }

    case p4::config::v1::MatchField::TERNARY: {
      if (match.match_value_case() != pdpi::IrMatch::kTernary) return mismatch;

      ASSIGN_OR_RETURN(z3::expr mask_expression,
                       GetZ3Value(match.ternary().mask()));
      ASSIGN_OR_RETURN(z3::expr value_expression,
                       GetZ3Value(match.ternary().value()));
      ASSIGN_OR_RETURN(z3::expr masked_field,
                       operators::BitAnd(field_expression, mask_expression));
      return operators::Eq(masked_field, value_expression);
    }

    case p4::config::v1::MatchField::OPTIONAL: {
      if (match.match_value_case() != pdpi::IrMatch::kOptional) return mismatch;
      // According to the P4Runtime spec, "for don't care matches, the P4Runtime
      // client must omit the field's entire FieldMatch entry when building the
      // match repeated field of the TableEntry message". Therefore, if the
      // match value is present for an optional match type, it must be a
      // concrete value.
      ASSIGN_OR_RETURN(z3::expr value_expression,
                       GetZ3Value(match.optional().value()));
      return operators::Eq(field_expression, value_expression);
    }

    default:
      return absl::UnimplementedError(absl::StrCat(
          "Found unsupported match type ", match_definition.DebugString()));
  }
}

// Constructs a symbolic expression that is true if and only if this entry
// is matched on.
absl::StatusOr<z3::expr> EvaluateTableEntryCondition(
    const ir::Table &table, const pdpi::IrTableEntry &entry, SolverState &state,
    const SymbolicPerPacketState &headers) {
  const std::string &table_name = table.table_definition().preamble().name();

  // Construct the match condition expression.
  z3::expr condition_expression = state.context.z3_context->bool_val(true);
  const google::protobuf::Map<std::string, ir::FieldValue> &match_to_fields =
      table.table_implementation().match_name_to_field();

  // It is desirable for P4Symbolic to produce deterministic outputs. Therefore,
  // all containers need to be traversed in a deterministic order.
  const auto sorted_match_fields_by_name =
      Ordered(table.table_definition().match_fields_by_name());

  for (const auto &[name, match_fields] : sorted_match_fields_by_name) {
    p4::config::v1::MatchField match_definition = match_fields.match_field();

    int match_field_index = FindMatchWithName(entry, name);
    if (match_field_index == -1) {
      // Table entry does not specify a value for this match key, means
      // it is a wildcard, no need to do any symbolic condition for it.
      continue;
    }
    const pdpi::IrMatch &match = entry.matches(match_field_index);

    // We get the match name for pdpi/p4info for simplicity, however that
    // file only contains the match name as a string, which is the same as the
    // match target expression in most cases but not always.
    // For conciseness, we get the corresponding accurate match target from
    // bmv2 by looking up the match name there.
    // In certain cases this is important, e.g. a match defined over field
    // "dstAddr" may have aliases of that field as a match name, but will always
    // have the fully qualified name of the field in the bmv2 format.
    if (match_to_fields.count(match_definition.name()) != 1) {
      return absl::InvalidArgumentError(absl::StrCat(
          "Match key with name \"", match_definition.name(),
          "\" was not found in implementation of table \"", table_name, "\""));
    }

    ir::FieldValue match_field = match_to_fields.at(match_definition.name());
    std::string field_name = absl::StrFormat("%s.%s", match_field.header_name(),
                                             match_field.field_name());
    ASSIGN_OR_RETURN(z3::expr field_expr,
                     action::EvaluateFieldValue(match_field, headers));
    ASSIGN_OR_RETURN(z3::expr match_expression,
                     EvaluateSingleMatch(match_definition, field_name,
                                         field_expr, match, state));
    ASSIGN_OR_RETURN(condition_expression,
                     operators::And(condition_expression, match_expression));
  }

  return condition_expression;
}

absl::Status EvaluateSingeTableEntryAction(
    const pdpi::IrActionInvocation &action,
    const google::protobuf::Map<std::string, ir::Action> &actions,
    SolverState &state, SymbolicPerPacketState *headers,
    const z3::expr &guard) {
  // Check that the action invoked by entry exists.
  if (actions.count(action.name()) != 1) {
    return gutil::InvalidArgumentErrorBuilder()
           << "unknown action '" << action.name() << "'";
  }
  return action::EvaluateAction(actions.at(action.name()), action.params(),
                                state, headers, guard);
}

// Constructs a symbolic expressions that represents the action invocation
// corresponding to this entry.
absl::Status EvaluateTableEntryAction(
    const ir::Table &table, const TableEntry &entry,
    const google::protobuf::Map<std::string, ir::Action> &actions,
    SolverState &state, SymbolicPerPacketState *headers,
    const z3::expr &guard) {
  const pdpi::IrTableEntry &ir_entry = entry.GetPdpiIrTableEntry();

  switch (ir_entry.type_case()) {
    case pdpi::IrTableEntry::kAction:
      RETURN_IF_ERROR(EvaluateSingeTableEntryAction(ir_entry.action(), actions,
                                                    state, headers, guard))
              .SetPrepend()
          << "In table entry '" << ir_entry.ShortDebugString() << "':";
      return absl::OkStatus();
    case pdpi::IrTableEntry::kActionSet: {
      auto &action_set = ir_entry.action_set().actions();
      // For action sets, we introduce a new free integer variable "selector"
      // whose value determines which action is executed: to a first
      // approximation, action i is executed iff `selector == i`.
      std::string selector_name =
          absl::StrFormat("action selector for entry #%d of table '%s'",
                          entry.GetIndex(), ir_entry.table_name());
      z3::expr selector =
          state.context.z3_context->int_const(selector_name.c_str());
      z3::expr unselected = state.context.z3_context->bool_val(true);
      for (int i = 0; i < action_set.size(); ++i) {
        auto &action = action_set.at(i).action();
        bool is_last_action = i == action_set.size() - 1;
        z3::expr selected = is_last_action ? unselected : (selector == i);
        unselected = unselected && !selected;
        RETURN_IF_ERROR(EvaluateSingeTableEntryAction(
                            action, actions, state, headers, guard && selected))
                .SetPrepend()
            << "In table entry '" << ir_entry.ShortDebugString() << "':";
      }
      return absl::OkStatus();
    }
    default:
      break;
  }
  return gutil::InvalidArgumentErrorBuilder()
         << "unexpected or missing action in table entry: "
         << ir_entry.DebugString();
}

}  // namespace

absl::StatusOr<SymbolicTableMatches> EvaluateTable(
    const ir::Table &table, SolverState &state, SymbolicPerPacketState *headers,
    const z3::expr &guard) {
  const std::string &table_name = table.table_definition().preamble().name();
  // Sort entries by priority deduced from match types.
  std::vector<TableEntry> sorted_entries;
  if (auto it = state.context.table_entries.find(table_name);
      it != state.context.table_entries.end()) {
    sorted_entries = SortEntries(table, it->second);
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
  // The simplest way to do this is first evaluate all the match conditions
  // symbolically, then construct complete guard for every entry.
  // Example, For entry i, all assignments/effects made by that entry's action
  // are guarded by:
  // guard && condition[i] && !condition[0] && ... && !condition[i-1]
  //
  // This way, when we evaluate entry i-1 in the next step, and we retrieve the
  // value, we will use it in the context of the then body guarded by
  // guard && condition[i-1], which entails that the assignment guard for
  // effects of entry i (and all following entries) is false.

  // Find all entries match conditions.
  std::vector<z3::expr> entries_matches;
  for (const auto &entry : sorted_entries) {
    if (entry.IsSymbolic()) {
      return gutil::UnimplementedErrorBuilder()
             << "Symbolic entries are not supported at the moment.";
    }

    // We are passing state by const reference here, so we do not need
    // any guard yet.
    ASSIGN_OR_RETURN(z3::expr entry_match,
                     EvaluateTableEntryCondition(
                         table, entry.GetPdpiIrTableEntry(), state, *headers));
    entries_matches.push_back(entry_match);
  }

  // Build each entry's assignment/effect guard by negating
  // higher priority entries.
  z3::expr default_entry_assignment_guard = guard;
  std::vector<z3::expr> assignment_guards;
  if (!entries_matches.empty()) {
    ASSIGN_OR_RETURN(z3::expr current_guard,
                     operators::And(guard, entries_matches.at(0)));
    ASSIGN_OR_RETURN(z3::expr accumulator_guard,
                     operators::Not(entries_matches.at(0)));
    assignment_guards.push_back(current_guard);
    for (size_t i = 1; i < entries_matches.size(); i++) {
      ASSIGN_OR_RETURN(z3::expr tmp, operators::And(guard, accumulator_guard));
      ASSIGN_OR_RETURN(current_guard,
                       operators::And(tmp, entries_matches.at(i)));
      ASSIGN_OR_RETURN(tmp, operators::Not(entries_matches.at(i)));
      ASSIGN_OR_RETURN(accumulator_guard,
                       operators::And(accumulator_guard, tmp));
      assignment_guards.push_back(current_guard);
    }
    ASSIGN_OR_RETURN(
        default_entry_assignment_guard,
        operators::And(default_entry_assignment_guard, accumulator_guard));
  }

  // Build a TableEntry object for the default entry.
  ir::TableEntry ir_default_entry;
  ir_default_entry.mutable_concrete_entry()->mutable_action()->set_name(
      table.table_implementation().default_action());
  for (const std::string &parameter_value :
       table.table_implementation().default_action_parameters()) {
    ASSIGN_OR_RETURN(*(ir_default_entry.mutable_concrete_entry()
                           ->mutable_action()
                           ->add_params()
                           ->mutable_value()),
                     values::ParseIrValue(parameter_value));
  }
  TableEntry default_entry(kDefaultActionEntryIndex,
                           std::move(ir_default_entry));

  // Start with the default entry
  z3::expr match_index =
      state.context.z3_context->int_val(kDefaultActionEntryIndex);
  RETURN_IF_ERROR(
      EvaluateTableEntryAction(table, default_entry, state.program.actions(),
                               state, headers, default_entry_assignment_guard));

  // Continue evaluating each table entry in reverse priority
  for (int row = sorted_entries.size() - 1; row >= 0; row--) {
    const TableEntry &entry = sorted_entries.at(row);
    z3::expr row_symbol = state.context.z3_context->int_val(entry.GetIndex());

    // The condition used in the big if_else_then construct.
    ASSIGN_OR_RETURN(z3::expr entry_match,
                     operators::And(guard, entries_matches.at(row)));
    ASSIGN_OR_RETURN(match_index,
                     operators::Ite(entry_match, row_symbol, match_index));

    // Evaluate the entry's action guarded by its complete assignment guard.
    z3::expr entry_assignment_guard = assignment_guards.at(row);
    RETURN_IF_ERROR(EvaluateTableEntryAction(table, entry,
                                             state.program.actions(), state,
                                             headers, entry_assignment_guard));
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
        ASSIGN_OR_RETURN(SymbolicTableMatches branch_matches,
                         control::EvaluateControl(next_control, state, headers,
                                                  guard && branch_condition));
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

}  // namespace table
}  // namespace symbolic
}  // namespace p4_symbolic
