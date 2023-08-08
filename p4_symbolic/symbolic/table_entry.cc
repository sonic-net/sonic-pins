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

#include "p4_symbolic/symbolic/table_entry.h"

#include <algorithm>
#include <cstddef>
#include <optional>
#include <string>
#include <utility>

#include "absl/container/flat_hash_map.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_pdpi/internal/ordered_map.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/symbolic/util.h"
#include "z3++.h"

namespace p4_symbolic::symbolic {

using MatchType = p4::config::v1::MatchField::MatchType;

namespace {

// A static mapping between the PI match type to the type string.
const absl::flat_hash_map<MatchType, std::string> match_type_to_str = {
    {MatchType::MatchField_MatchType_EXACT, "exact"},
    {MatchType::MatchField_MatchType_LPM, "lpm"},
    {MatchType::MatchField_MatchType_TERNARY, "ternary"},
    {MatchType::MatchField_MatchType_OPTIONAL, "optional"},
};

}  // namespace

TableEntry::TableEntry(int index, ir::TableEntry ir_entry)
    : index_(index), ir_entry_(std::move(ir_entry)) {}

int TableEntry::GetIndex() const { return index_; }
bool TableEntry::IsConcrete() const { return ir_entry_.has_concrete_entry(); }
bool TableEntry::IsSymbolic() const { return ir_entry_.has_symbolic_entry(); }

const std::string &TableEntry::GetTableName() const {
  return GetPdpiIrTableEntry().table_name();
}

const ir::TableEntry &TableEntry::GetP4SymbolicIrTableEntry() const {
  return ir_entry_;
}

const pdpi::IrTableEntry &TableEntry::GetPdpiIrTableEntry() const {
  if (IsConcrete()) return ir_entry_.concrete_entry();
  return ir_entry_.symbolic_entry().sketch();
}

absl::StatusOr<SymbolicMatchInfo> TableEntry::GetSymbolicMatchInfo(
    absl::string_view match_name, const ir::Table &table,
    const ir::P4Program &program) const {
  // Check if the match exists in the table definition.
  if (!table.table_definition().match_fields_by_name().contains(match_name)) {
    return gutil::NotFoundErrorBuilder()
           << "Match '" << match_name << "' not found in table '"
           << GetTableName() << "'";
  }

  const p4::config::v1::MatchField &pi_match_field = table.table_definition()
                                                         .match_fields_by_name()
                                                         .at(match_name)
                                                         .match_field();

  // Check if the match type is specified and supported.
  if (!pi_match_field.has_match_type() ||
      !match_type_to_str.contains(pi_match_field.match_type())) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Match type must be one of [exact, lpm, ternary, optional]. "
              "Found match: "
           << pi_match_field.DebugString();
  }

  // Return an error if this is a fully concrete entry.
  if (IsConcrete()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Entry " << GetIndex() << " of table '" << GetTableName()
           << "' is not symbolic.";
  }

  // If the specified match of this entry is an explicit wildcard, return an
  // error and no symbolic variable should be created.
  const auto &entry_matches = GetPdpiIrTableEntry().matches();
  auto ir_match_it =
      std::find_if(entry_matches.begin(), entry_matches.end(),
                   [&match_name](const pdpi::IrMatch &match) -> bool {
                     return match.name() == match_name;
                   });
  if (ir_match_it == entry_matches.end()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Match '" << match_name
           << "' is an explicit wildcard. The match is omitted in the IR table"
              " entry. To specify a symbolic match, please set the match name"
              " while leaving other fields unset.";
  }

  // Use the matched header field to get the match bit-width.
  auto it = table.table_implementation().match_name_to_field().find(match_name);
  if (it == table.table_implementation().match_name_to_field().end()) {
    return gutil::NotFoundErrorBuilder()
           << "Match '" << match_name
           << "' not found in implementation of table '" << GetTableName()
           << "'. Found: " << table.DebugString();
  }
  ASSIGN_OR_RETURN(int bitwidth,
                   util::GetFieldBitwidth(it->second.header_name(),
                                          it->second.field_name(), program));

  // If the table definition has the match bit-width, make sure it is consistent
  // with the one in the table implementation.
  if (pi_match_field.bitwidth() != 0 && pi_match_field.bitwidth() != bitwidth) {
    return gutil::InternalErrorBuilder()
           << "Bit-width of match '" << match_name << "' in table '"
           << GetTableName()
           << "' is inconsistent between the definition and implementation.";
  }

  // Construct and return the variable names with the following template:
  // "<table_name>_entry_<index>_<match_name>_<match_type>_(value|mask)"
  const auto &match_type = pi_match_field.match_type();
  std::string name_prefix =
      absl::StrCat(GetTableName(), "_entry_", GetIndex(), "_", match_name, "_",
                   match_type_to_str.at(match_type), "_");
  return SymbolicMatchInfo{
      .match_type = match_type,
      .bitwidth = bitwidth,
      .value_variable_name = absl::StrCat(name_prefix, "value"),
      .mask_variable_name = absl::StrCat(name_prefix, "mask"),
  };
}

absl::StatusOr<std::string> TableEntry::GetActionChoiceSymbolicVariableName(
    absl::string_view action_name, const ir::Table &table) const {
  // Check if the action exists in the table definition based on the given
  // `action_name`.
  auto action_ref_it = std::find_if(
      table.table_definition().entry_actions().begin(),
      table.table_definition().entry_actions().end(),
      [&action_name](const pdpi::IrActionReference &action_ref) -> bool {
        return action_ref.action().preamble().name() == action_name;
      });

  if (action_ref_it == table.table_definition().entry_actions().end()) {
    return gutil::NotFoundErrorBuilder()
           << "Action '" << action_name << "' not found in table '"
           << GetTableName() << "'";
  }

  // Return an error if this is a fully concrete entry.
  if (IsConcrete()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Entry " << GetIndex() << " of table '" << GetTableName()
           << "' is not symbolic.";
  }

  // Construct and return the variable name with the following template:
  // "<table_name>_entry_<index>_<action_name>_$chosen$"
  return absl::StrCat(GetTableName(), "_entry_", GetIndex(), "_", action_name,
                      "_$chosen$");
}

absl::StatusOr<SymbolicActionParameterInfo>
TableEntry::GetSymbolicActionParameterInfo(absl::string_view param_name,
                                           const ir::Action &action,
                                           const ir::Table &table) const {
  const absl::string_view action_name =
      action.action_definition().preamble().name();

  // Check if the action with the given `action_name` exists in the table
  // definition.
  auto action_ref_it = std::find_if(
      table.table_definition().entry_actions().begin(),
      table.table_definition().entry_actions().end(),
      [&action_name](const pdpi::IrActionReference &action_ref) -> bool {
        return action_ref.action().preamble().name() == action_name;
      });

  if (action_ref_it == table.table_definition().entry_actions().end()) {
    return gutil::NotFoundErrorBuilder()
           << "Action '" << action_name << "' not found in table '"
           << GetTableName() << "'";
  }

  // Return an error if this is a fully concrete entry.
  if (IsConcrete()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Entry " << GetIndex() << " of table '" << GetTableName()
           << "' is not symbolic.";
  }

  // Check if the parameter with the given `param_name` exists in the action
  // implementation.
  auto param_bitwidth_it =
      action.action_implementation().parameter_to_bitwidth().find(param_name);
  if (param_bitwidth_it ==
      action.action_implementation().parameter_to_bitwidth().end()) {
    return gutil::NotFoundErrorBuilder()
           << "Action parameter '" << param_name
           << "' not found in implementation of action '" << action_name << "'";
  }
  int bitwidth = param_bitwidth_it->second;

  // Check if the parameter with the given `param_name` exists in the action
  // definition.
  auto param_it = action.action_definition().params_by_name().find(param_name);
  if (param_it == action.action_definition().params_by_name().end()) {
    return gutil::NotFoundErrorBuilder()
           << "Action parameter '" << param_name
           << "' not found in definition of action '" << action_name << "'";
  }

  // If the action definition has the parameter bit-width, make sure it is
  // consistent with the one in the action implementation.
  if (param_it->second.param().bitwidth() != 0 &&
      param_it->second.param().bitwidth() != bitwidth) {
    return gutil::InternalErrorBuilder()
           << "Bit-width of parameter '" << param_name << "' in action '"
           << action_name
           << "' is inconsistent between the definition and implementation.";
  }

  // Construct and return the variable name and its bit-width with the following
  // template:
  // "<table_name>_entry_<index>_<action_name>_<param_name>"
  std::string variable_name = absl::StrCat(
      GetTableName(), "_entry_", GetIndex(), "_", action_name, "_", param_name);
  return SymbolicActionParameterInfo{
      .variable_name = variable_name,
      .bitwidth = bitwidth,
  };
}

absl::StatusOr<SymbolicMatchVariables> TableEntry::GetMatchValues(
    absl::string_view match_name, const ir::Table &table,
    const ir::P4Program &program, z3::context &z3_context) const {
  // Return an error if this is a fully concrete entry.
  if (IsConcrete()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Entry " << GetIndex() << " of table '" << GetTableName()
           << "' is not symbolic.";
  }

  // Get symbolic variable names.
  ASSIGN_OR_RETURN(SymbolicMatchInfo match,
                   GetSymbolicMatchInfo(match_name, table, program));

  // Construct and return the symbolic variables as Z3 expressions.
  return SymbolicMatchVariables{
      .match_type = match.match_type,
      .value = z3_context.bv_const(match.value_variable_name.c_str(),
                                   match.bitwidth),
      .mask =
          z3_context.bv_const(match.mask_variable_name.c_str(), match.bitwidth),
  };
}

absl::StatusOr<z3::expr> TableEntry::GetActionInvocation(
    absl::string_view action_name, const ir::Table &table,
    z3::context &z3_context) const {
  // Return an error if this is a fully concrete entry.
  if (IsConcrete()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Entry " << GetIndex() << " of table '" << GetTableName()
           << "' is not symbolic.";
  }

  // Get symbolic variable names.
  ASSIGN_OR_RETURN(std::string variable_name,
                   GetActionChoiceSymbolicVariableName(action_name, table));

  // Construct and return the symbolic variable as a Z3 expression.
  return z3_context.bool_const(variable_name.c_str());
}

absl::StatusOr<z3::expr> TableEntry::GetActionParameter(
    absl::string_view param_name, const ir::Action &action,
    const ir::Table &table, z3::context &z3_context) const {
  // Return an error if this is a fully concrete entry.
  if (IsConcrete()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Entry " << GetIndex() << " of table '" << GetTableName()
           << "' is not symbolic.";
  }

  // Get symbolic variable names.
  ASSIGN_OR_RETURN(auto action_param,
                   GetSymbolicActionParameterInfo(param_name, action, table));

  // Construct and return the symbolic variable as a Z3 expression.
  return z3_context.bv_const(action_param.variable_name.c_str(),
                             action_param.bitwidth);
}

absl::StatusOr<ir::TableEntry> CreateSymbolicIrTableEntry(
    const ir::Table &table, int priority, std::optional<size_t> prefix_length) {
  // Build a symbolic table entry in P4-Symbolic IR.
  ir::TableEntry ir_entry;
  pdpi::IrTableEntry &sketch =
      *ir_entry.mutable_symbolic_entry()->mutable_sketch();

  // Set table name.
  const std::string &table_name = table.table_definition().preamble().name();
  sketch.set_table_name(table_name);

  bool has_ternary_or_optional = false;
  pdpi::IrMatch *lpm_match = nullptr;

  for (const auto &[match_name, match_definition] :
       Ordered(table.table_definition().match_fields_by_name())) {
    // Set match name.
    pdpi::IrMatch *ir_match = sketch.add_matches();
    ir_match->set_name(match_name);

    const auto &pi_match = match_definition.match_field();
    switch (pi_match.match_type()) {
      case MatchType::MatchField_MatchType_TERNARY:
      case MatchType::MatchField_MatchType_OPTIONAL: {
        has_ternary_or_optional = true;
        break;
      }
      case MatchType::MatchField_MatchType_LPM: {
        lpm_match = ir_match;
        break;
      }
      default: {
        // Exact or some other unsupported type, no need to do anything here.
        // An absl error will be returned during symbolic evaluation.
        break;
      }
    }
  }

  // Set prefix length for single-LPM tables.
  if (!has_ternary_or_optional && lpm_match) {
    if (!prefix_length.has_value()) {
      return gutil::InvalidArgumentErrorBuilder()
             << "Prefix length must be provided for tables with a single LPM "
                "match.";
    }
    lpm_match->mutable_lpm()->set_prefix_length(*prefix_length);
  }

  // Set priority.
  if (has_ternary_or_optional && priority <= 0) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Priority must be greater than 0 for tables with ternary or "
              "optional matches. Found: "
           << priority;
  }
  sketch.set_priority(has_ternary_or_optional ? priority : 0);

  return ir_entry;
}

}  // namespace p4_symbolic::symbolic
