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
#include <utility>

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/substitute.h"
#include "absl/types/optional.h"
#include "absl/types/span.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_pdpi/internal/ordered_map.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_symbolic/ir/ir.h"
#include "p4_symbolic/symbolic/action.h"
#include "p4_symbolic/symbolic/operators.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/symbolic/values.h"
#include "p4_symbolic/z3_util.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {
namespace table {

namespace {

// Finds a match field with the given id in the given table entry.
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
// Priority depends on the match types.
// If the matches contain one or more ternary matches, priority is the explicit
// numeric priority assigned to the the entry.
// If no ternary matches exist, and there is *exactly* one lpm match, priority
// is determined by the length of the prefix to match, such that longer
// prefixes have higher priority.
// Finally, if the matches only contain exact matches, there is no priority.
//
// The function returns a vector of pairs, where the second element
// is a table entry, and the first is its index in the old unsorted array.
// The pairs are sorted by priority, such that the element with highest priority
// appears first.
// Elements with equal priority maintaing their relative ordering.
//
// We return the old index so that Symbolic and Concrete TableMatches are
// set up against the indices as they appear in the input table entries array,
// and not the sorted array.
std::vector<std::pair<int, pdpi::IrTableEntry>> SortEntries(
    const ir::Table &table, const std::vector<pdpi::IrTableEntry> &entries) {
  if (entries.empty()) return {};
  // Find which *definition* of priority we should use by looking at the
  // table's match types.
  const pdpi::IrTableDefinition &table_definition = table.table_definition();
  bool has_ternary = false;
  absl::optional<std::string> lpm_key;
  for (const auto &[name, match_field_definition] :
       table_definition.match_fields_by_name()) {
    switch (match_field_definition.match_field().match_type()) {
      case p4::config::v1::MatchField::TERNARY: {
        has_ternary = true;
        break;
      }
      case p4::config::v1::MatchField::LPM: {
        lpm_key = name;
        break;
      }
      default: {
        // Exact or some other unsupported type, no need to do anything here.
        // An absl error will be returned if the type is unsupported in
        // "EvaluateSingleMatch".
        break;
      }
    }
  }

  // The output array.
  std::vector<std::pair<int, pdpi::IrTableEntry>> sorted_entries;
  for (int i = 0; i < entries.size(); i++) {
    const pdpi::IrTableEntry &entry = entries.at(i);
    sorted_entries.push_back(std::make_pair(i, entry));
  }

  // The sort comparator depends on the match types.
  std::function<bool(const std::pair<int, pdpi::IrTableEntry> &,
                     const std::pair<int, pdpi::IrTableEntry> &)>
      comparator;
  if (has_ternary) {
    // Sort by explicit priority.
    comparator = [](const std::pair<int, pdpi::IrTableEntry> &entry1,
                    const std::pair<int, pdpi::IrTableEntry> &entry2) {
      return entry1.second.priority() > entry2.second.priority();
    };
  } else if (lpm_key.has_value()) {
    // Sort by prefix length.
    comparator = [lpm_key](const std::pair<int, pdpi::IrTableEntry> &entry1,
                           const std::pair<int, pdpi::IrTableEntry> &entry2) {
      auto is_lpm_match = [=](const pdpi::IrMatch &match) -> bool {
        return match.name() == *lpm_key;
      };
      auto matches1 = entry1.second.matches();
      auto matches2 = entry2.second.matches();
      auto it1 = std::find_if(matches1.begin(), matches1.end(), is_lpm_match);
      auto it2 = std::find_if(matches2.begin(), matches2.end(), is_lpm_match);
      int prefix_length1 =
          it1 == matches1.end() ? 0 : it1->lpm().prefix_length();
      int prefix_length2 =
          it2 == matches2.end() ? 0 : it2->lpm().prefix_length();
      return prefix_length1 > prefix_length2;
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
// Constructs a symbolic expression that semantically corresponds to this
// match.
absl::StatusOr<z3::expr> EvaluateSingleMatch(
    p4::config::v1::MatchField match_definition, const std::string &field_name,
    const z3::expr &field_expression, const pdpi::IrMatch &match,
    values::P4RuntimeTranslator *translator) {
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
                                   match_definition.bitwidth(), translator);
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
    const ir::Table &table, const pdpi::IrTableEntry &entry,
    const SymbolicPerPacketState &state,
    values::P4RuntimeTranslator *translator) {
  const std::string &table_name = table.table_definition().preamble().name();

  // Construct the match condition expression.
  z3::expr condition_expression = Z3Context().bool_val(true);
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
    action::ActionContext fake_context = {table_name, {}};
    ASSIGN_OR_RETURN(
        z3::expr match_field_expr,
        action::EvaluateFieldValue(match_field, state, fake_context));
    ASSIGN_OR_RETURN(z3::expr match_expression,
                     EvaluateSingleMatch(match_definition, field_name,
                                         match_field_expr, match, translator));
    ASSIGN_OR_RETURN(condition_expression,
                     operators::And(condition_expression, match_expression));
  }

  return condition_expression;
}

absl::Status EvaluateSingeTableEntryAction(
    const pdpi::IrActionInvocation &action,
    const google::protobuf::Map<std::string, ir::Action> &actions,
    SymbolicPerPacketState *state, values::P4RuntimeTranslator *translator,
    const z3::expr &guard) {
  // Check that the action invoked by entry exists.
  if (actions.count(action.name()) != 1) {
    return gutil::InvalidArgumentErrorBuilder()
           << "unknown action '" << action.name() << "'";
  }
  return action::EvaluateAction(actions.at(action.name()), action.params(),
                                state, translator, guard);
}

// Constructs a symbolic expressions that represents the action invocation
// corresponding to this entry.
absl::Status EvaluateTableEntryAction(
    const ir::Table &table, const pdpi::IrTableEntry &entry, int entry_index,
    const google::protobuf::Map<std::string, ir::Action> &actions,
    SymbolicPerPacketState *state, values::P4RuntimeTranslator *translator,
    const z3::expr &guard) {
  switch (entry.type_case()) {
    case pdpi::IrTableEntry::kAction:
      RETURN_IF_ERROR(EvaluateSingeTableEntryAction(entry.action(), actions,
                                                    state, translator, guard))
              .SetPrepend()
          << "In table entry '" << entry.ShortDebugString() << "':";
      return absl::OkStatus();
    case pdpi::IrTableEntry::kActionSet: {
      auto &action_set = entry.action_set().actions();
      // For action sets, we introduce a new free integer variable "selector"
      // whose value determines which action is executed: to a first
      // approximation, action i is executed iff `selector == i`.
      std::string selector_name =
          absl::StrFormat("action selector for entry #%d of table '%s'",
                          entry_index, entry.table_name());
      z3::expr selector = Z3Context().int_const(selector_name.c_str());
      z3::expr unselected = Z3Context().bool_val(true);
      for (int i = 0; i < action_set.size(); ++i) {
        auto &action = action_set.at(i).action();
        bool is_last_action = i == action_set.size() - 1;
        z3::expr selected = is_last_action ? unselected : (selector == i);
        unselected = unselected && !selected;
        RETURN_IF_ERROR(EvaluateSingeTableEntryAction(action, actions, state,
                                                      translator,
                                                      guard && selected))
                .SetPrepend()
            << "In table entry '" << entry.ShortDebugString() << "':";
      }
      return absl::OkStatus();
    }
    default:
      break;
  }
  return gutil::InvalidArgumentErrorBuilder()
         << "unexpected or missing action in table entry: "
         << entry.DebugString();
}

}  // namespace

absl::StatusOr<SymbolicTableMatches> EvaluateTable(
    const Dataplane &data_plane, const ir::Table &table,
    const std::vector<pdpi::IrTableEntry> &entries,
    SymbolicPerPacketState *state, values::P4RuntimeTranslator *translator,
    const z3::expr &guard) {
  const std::string &table_name = table.table_definition().preamble().name();
  // Sort entries by priority deduced from match types.
  std::vector<std::pair<int, pdpi::IrTableEntry>> sorted_entries =
      SortEntries(table, entries);
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
  for (const auto &[_, entry] : sorted_entries) {
    // We are passsing state by const reference here, so we do not need
    // any guard yet.
    ASSIGN_OR_RETURN(
        z3::expr entry_match,
        EvaluateTableEntryCondition(table, entry, *state, translator));
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

  // Build an IrTableEntry object for the default entry.
  pdpi::IrTableEntry default_entry;
  default_entry.mutable_action()->set_name(
      table.table_implementation().default_action());
  for (const std::string &parameter_value :
       table.table_implementation().default_action_parameters()) {
    ASSIGN_OR_RETURN(
        *(default_entry.mutable_action()->add_params()->mutable_value()),
        values::ParseIrValue(parameter_value));
  }

  // Start with the default entry
  z3::expr match_index = Z3Context().int_val(kDefaultActionEntryIndex);
  RETURN_IF_ERROR(
      EvaluateTableEntryAction(table, default_entry, kDefaultActionEntryIndex,
                               data_plane.program.actions(), state, translator,
                               default_entry_assignment_guard));

  // Continue evaluating each table entry in reverse priority
  for (int row = sorted_entries.size() - 1; row >= 0; row--) {
    int old_index = sorted_entries.at(row).first;
    const pdpi::IrTableEntry &entry = sorted_entries.at(row).second;
    z3::expr row_symbol = Z3Context().int_val(old_index);

    // The condition used in the big if_else_then construct.
    ASSIGN_OR_RETURN(z3::expr entry_match,
                     operators::And(guard, entries_matches.at(row)));
    ASSIGN_OR_RETURN(match_index,
                     operators::Ite(entry_match, row_symbol, match_index));

    // Evaluate the entry's action guarded by its complete assignment guard.
    z3::expr entry_assignment_guard = assignment_guards.at(row);
    RETURN_IF_ERROR(EvaluateTableEntryAction(
        table, entry, old_index, data_plane.program.actions(), state,
        translator, entry_assignment_guard));
  }

  const std::string &merge_point = table.table_implementation()
                                       .optimized_symbolic_execution_info()
                                       .merge_point();

  // We currenlt only support tables that always have the same next control
  // construct regardless of the table's matches.
  //
  // This can be supported by calling EvaluateControl(...)
  // inside the above for loop for control found at
  //   <action_to_next_control>(<action of entry>)
  // and passing it the complete entry guard.
  //
  // As an optimization, the loop should not call EvaluateControl
  // when all actions have the same next_control, and should instead
  // execute the call once outside the loop as below.
  for (const auto &[_, next_control] :
       table.table_implementation().action_to_next_control()) {
    if (next_control != merge_point) {
      return absl::UnimplementedError(
          absl::Substitute("Table '$0' invokes different control constructs "
                           "based on match results",
                           table_name));
    }
  }

  const std::string continuation = table.table_implementation()
                                           .optimized_symbolic_execution_info()
                                           .continue_to_merge_point()
                                       ? merge_point
                                       : ir::EndOfPipeline();

  // Evaluate the next control.
  ASSIGN_OR_RETURN(SymbolicTableMatches result,
                   control::EvaluateControl(data_plane, continuation, state,
                                            translator, guard));

  // The trace should not contain information for this table, otherwise, it
  // means we visited the table twice in the same execution path!
  if (result.contains(table_name)) {
    return absl::InternalError(absl::Substitute(
        "Table '$0' was executed twice in the same path.", table_name));
  }

  // Add this table's match to the trace, and return it.
  result.insert({table_name, SymbolicTableMatch{
                                 .matched = guard,
                                 .entry_index = match_index,
                             }});
  return result;
}

}  // namespace table
}  // namespace symbolic
}  // namespace p4_symbolic
