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

#include "absl/container/btree_map.h"
#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "gutil/collections.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_pdpi/internal/ordered_map.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/symbolic/operators.h"
#include "p4_symbolic/symbolic/util.h"
#include "p4_symbolic/symbolic/values.h"
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

// Translates the given `value` read from the `match` of an entry in the given
// `table` into a Z3 expression.
absl::StatusOr<z3::expr> GetZ3Value(const pdpi::IrValue &value,
                                    const p4::config::v1::MatchField &match,
                                    const ir::Table &table,
                                    z3::context &z3_context,
                                    values::P4RuntimeTranslator &translator) {
  const google::protobuf::Map<std::string, ir::FieldValue>
      &match_name_to_field = table.table_implementation().match_name_to_field();
  const auto it = match_name_to_field.find(match.name());
  if (it == match_name_to_field.end()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Match key with name '" << match.name()
           << "' was not found in implementation of table '"
           << table.table_definition().preamble().name() << "'";
  }
  const ir::FieldValue &matched_field = it->second;
  std::string field_name = absl::StrFormat("%s.%s", matched_field.header_name(),
                                           matched_field.field_name());
  return values::FormatP4RTValue(value, field_name, match.type_name().name(),
                                 match.bitwidth(), z3_context, translator);
}

// Adds constraints for the specific match types for encoding them as ternary
// values and masks.
absl::Status AddMatchTypeConstraintsForSymbolicMatch(
    const SymbolicMatchVariables &variables, z3::context &z3_context,
    z3::solver &solver) {
  // Add type constraints on the symbolic match variables.
  switch (variables.match_type) {
    case p4::config::v1::MatchField::EXACT: {
      // For exact matches, the mask bit-vector must be all-1s.
      int bitwidth = variables.mask.get_sort().bv_size();
      z3::expr all_ones = z3_context.bv_val((1UL << bitwidth) - 1, bitwidth);
      ASSIGN_OR_RETURN(z3::expr mask_constraint,
                       operators::Eq(variables.mask, all_ones));
      solver.add(mask_constraint);
      break;
    }
    case p4::config::v1::MatchField::LPM: {
      // For LPM matches, the mask bit-vector must comply with the LPM format.
      // I.e. (~lpm_mask) & (~lpm_mask + 1) == 0
      int bitwidth = variables.mask.get_sort().bv_size();
      ASSIGN_OR_RETURN(z3::expr negated_mask,
                       operators::BitNeg(variables.mask));
      ASSIGN_OR_RETURN(
          z3::expr negated_mask_plus_one,
          operators::Plus(negated_mask, z3_context.bv_val(1, bitwidth)));
      ASSIGN_OR_RETURN(z3::expr result,
                       operators::BitAnd(negated_mask, negated_mask_plus_one));
      ASSIGN_OR_RETURN(z3::expr mask_constraint,
                       operators::Eq(result, z3_context.bv_val(0, bitwidth)));
      solver.add(mask_constraint);
      break;
    }
    case p4::config::v1::MatchField::OPTIONAL: {
      // For optional matches, the mask bit-vector must be either all-1s
      // (present) or all-0s (don't-care).
      int bitwidth = variables.mask.get_sort().bv_size();
      z3::expr all_ones = z3_context.bv_val((1UL << bitwidth) - 1, bitwidth);
      z3::expr all_zeroes = z3_context.bv_val(0, bitwidth);
      ASSIGN_OR_RETURN(z3::expr mask_is_all_ones,
                       operators::Eq(variables.mask, all_ones));
      ASSIGN_OR_RETURN(z3::expr mask_is_all_zeroes,
                       operators::Eq(variables.mask, all_zeroes));
      ASSIGN_OR_RETURN(z3::expr mask_constraint,
                       operators::Or(mask_is_all_ones, mask_is_all_zeroes));
      solver.add(mask_constraint);
      break;
    }
    case p4::config::v1::MatchField::TERNARY: {
      // No type constraint is required for ternary matches.
      break;
    }
    default: {
      return gutil::InvalidArgumentErrorBuilder()
             << "Unsupported match type: " << variables.match_type
             << ". Expected: EXACT, LPM, TERNARY, or OPTIONAL";
    }
  }

  return absl::OkStatus();
}

// Adds canonicity constraints for P4Runtime updates.
// Since the P4Runtime API rejects entry updates where the non-masked bits are
// not zero, here we add the constraint to avoid synthesizing such entries.
// Namely, "(value & mask == value)".
absl::Status AddCanonicityConstraintForSymbolicMatch(
    const SymbolicMatchVariables &variables, z3::solver &solver) {
  ASSIGN_OR_RETURN(z3::expr masked_value,
                   operators::BitAnd(variables.value, variables.mask));
  ASSIGN_OR_RETURN(z3::expr constraint,
                   operators::Eq(masked_value, variables.value));
  solver.add(constraint);
  return absl::OkStatus();
}

// Adds equality constraints on the given `variables` corresponding to the
// concrete parts of the given symbolic `ir_match` of a table entry in the given
// `table`.
absl::Status AddConstraintsForConcretePartsOfSymbolicMatch(
    const SymbolicMatchVariables &variables, const pdpi::IrMatch &ir_match,
    const ir::Table &table, z3::context &z3_context, z3::solver &solver,
    values::P4RuntimeTranslator &translator) {
  // If the symbolic variables are created successfully, it means that a
  // match with the match name exists in the table definition, so no
  // exception will be thrown here.
  const p4::config::v1::MatchField &pi_match = table.table_definition()
                                                   .match_fields_by_name()
                                                   .at(ir_match.name())
                                                   .match_field();

  // Add equality constraints if a match value is set.
  // If no concrete value is specified, no equality constraint is asserted.
  if (ir_match.has_exact()) {
    ASSIGN_OR_RETURN(
        z3::expr concrete_exact_value,
        GetZ3Value(ir_match.exact(), pi_match, table, z3_context, translator));
    ASSIGN_OR_RETURN(z3::expr constraint,
                     operators::Eq(variables.value, concrete_exact_value));
    solver.add(constraint);
  } else if (ir_match.has_lpm()) {
    if (ir_match.lpm().has_value()) {
      ASSIGN_OR_RETURN(z3::expr concrete_lpm_value,
                       GetZ3Value(ir_match.lpm().value(), pi_match, table,
                                  z3_context, translator));
      ASSIGN_OR_RETURN(z3::expr value_constraint,
                       operators::Eq(variables.value, concrete_lpm_value));
      solver.add(value_constraint);
    }
    if (ir_match.lpm().prefix_length() >= 0) {
      int bitwidth = variables.value.get_sort().bv_size();
      int prefix_length = ir_match.lpm().prefix_length();
      if (prefix_length < 0 || prefix_length > bitwidth) {
        return gutil::InvalidArgumentErrorBuilder()
               << "Prefix length of match '" << ir_match.name()
               << "' must fall in the range [0, " << bitwidth
               << "]. Found: " << ir_match.DebugString();
      }
      z3::expr ones =
          z3_context.bv_val((1UL << prefix_length) - 1, prefix_length);
      z3::expr zeroes = z3_context.bv_val(0, bitwidth - prefix_length);
      z3::expr concrete_lpm_mask = z3::concat(ones, zeroes);

      // Constrain the symbolic variables of the LPM match to be equal to
      // the specified concrete values.
      ASSIGN_OR_RETURN(z3::expr mask_constraint,
                       operators::Eq(variables.mask, concrete_lpm_mask));
      solver.add(mask_constraint);
    }
  } else if (ir_match.has_ternary()) {
    if (ir_match.ternary().has_value()) {
      ASSIGN_OR_RETURN(z3::expr concrete_ternary_value,
                       GetZ3Value(ir_match.ternary().value(), pi_match, table,
                                  z3_context, translator));
      ASSIGN_OR_RETURN(z3::expr value_constraint,
                       operators::Eq(variables.value, concrete_ternary_value));
      solver.add(value_constraint);
    }
    if (ir_match.ternary().has_mask()) {
      ASSIGN_OR_RETURN(z3::expr concrete_ternary_mask,
                       GetZ3Value(ir_match.ternary().mask(), pi_match, table,
                                  z3_context, translator));
      ASSIGN_OR_RETURN(z3::expr mask_constraint,
                       operators::Eq(variables.mask, concrete_ternary_mask));
      solver.add(mask_constraint);
    }
  } else if (ir_match.has_optional() && ir_match.optional().has_value()) {
    ASSIGN_OR_RETURN(z3::expr concrete_optional_value,
                     GetZ3Value(ir_match.optional().value(), pi_match, table,
                                z3_context, translator));
    ASSIGN_OR_RETURN(z3::expr value_constraint,
                     operators::Eq(variables.value, concrete_optional_value));
    solver.add(value_constraint);
  }

  return absl::OkStatus();
}

// Add constraints enforcing exactly one action to be chosen for a symbolic
// action, for entries in a direct match table.
void AddSingleActionChoiceConstraintForSymbolicAction(
    const absl::btree_map<std::string, z3::expr> &action_choices_by_name,
    z3::context &z3_context, z3::solver &solver) {
  z3::expr overall_constraint = z3_context.bool_val(false);

  for (const auto &[applied_action_name, applied_action] :
       action_choices_by_name) {
    z3::expr assignment_constraint =
        (applied_action == z3_context.bool_val(true));

    for (const auto &[action_name, action] : action_choices_by_name) {
      if (action_name != applied_action_name) {
        assignment_constraint =
            (assignment_constraint && (action == z3_context.bool_val(false)));
      }
    }

    overall_constraint = overall_constraint || assignment_constraint;
  }

  solver.add(overall_constraint);
}

// Adds equality constraints to the solver according to the given `ir_action`.
absl::Status AddConstraintsForConcretePartsOfSymbolicAction(
    const pdpi::IrActionInvocation &ir_action,
    const absl::btree_map<std::string, z3::expr> &action_invocations_by_name,
    const absl::flat_hash_map<std::string,
                              absl::flat_hash_map<std::string, z3::expr>>
        &action_params_by_name,
    const ir::P4Program &program, z3::context &z3_context, z3::solver &solver,
    values::P4RuntimeTranslator &translator) {
  // If the action name of the invocation is empty, it is treated as an
  // unconstrained symbolic action. No constraint is asserted and no concrete
  // parameters should be specified.
  if (ir_action.name().empty()) {
    if (!ir_action.params().empty()) {
      return gutil::InvalidArgumentErrorBuilder()
             << "Action parameters must not be specified in a fully "
                "symbolic action. Found: "
             << ir_action.DebugString();
    }
    return absl::OkStatus();
  }

  // Check if the specified action name is valid.
  if (!action_invocations_by_name.contains(ir_action.name()) ||
      !action_params_by_name.contains(ir_action.name())) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Invalid action name: '" << ir_action.name() << "'";
  }

  // Check if the specified action parameter names are valid.
  for (const auto &param : ir_action.params()) {
    if (!action_params_by_name.at(ir_action.name()).contains(param.name())) {
      return gutil::InvalidArgumentErrorBuilder()
             << "Invalid action parameter name: '" << param.name() << "'";
    }
  }

  // Constrain the symbolic action invocation with the specified action name to
  // true and all other action invocations to false.
  solver.add(action_invocations_by_name.at(ir_action.name()) ==
             z3_context.bool_val(true));

  for (const auto &[action_name, action] : action_invocations_by_name) {
    if (action_name != ir_action.name()) {
      solver.add(action == z3_context.bool_val(false));
    }
  }

  // Add equality constraints on the symbolic action parameters with the
  // specified concrete parameter values.
  for (const auto &param : ir_action.params()) {
    z3::expr action_param =
        action_params_by_name.at(ir_action.name()).at(param.name());
    ASSIGN_OR_RETURN(const pdpi::IrActionDefinition::IrActionParamDefinition
                         *param_definition,
                     gutil::FindPtrOrStatus(program.actions()
                                                .at(ir_action.name())
                                                .action_definition()
                                                .params_by_name(),
                                            param.name()));
    ASSIGN_OR_RETURN(
        z3::expr concrete_param_value,
        values::FormatP4RTValue(param.value(), /*field_name=*/std::nullopt,
                                param_definition->param().type_name().name(),
                                param_definition->param().bitwidth(),
                                z3_context, translator));
    ASSIGN_OR_RETURN(z3::expr param_constraint,
                     operators::Eq(action_param, concrete_param_value));
    solver.add(param_constraint);
  }

  return absl::OkStatus();
}

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

absl::Status InitializeSymbolicMatches(
    const TableEntry &entry, const ir::Table &table,
    const ir::P4Program &program, z3::context &z3_context, z3::solver &solver,
    values::P4RuntimeTranslator &translator) {
  for (const pdpi::IrMatch &match : entry.GetPdpiIrTableEntry().matches()) {
    if (match.name().empty()) {
      return gutil::InvalidArgumentErrorBuilder()
             << "The match name must not be empty. Found: "
             << match.DebugString();
    }

    // Create symbolic variables for the symbolic match.
    ASSIGN_OR_RETURN(
        SymbolicMatchVariables variables,
        entry.GetMatchValues(match.name(), table, program, z3_context));
    // Add various constraints for the symbolic match.
    RETURN_IF_ERROR(
        AddMatchTypeConstraintsForSymbolicMatch(variables, z3_context, solver));
    RETURN_IF_ERROR(AddCanonicityConstraintForSymbolicMatch(variables, solver));
    RETURN_IF_ERROR(AddConstraintsForConcretePartsOfSymbolicMatch(
        variables, match, table, z3_context, solver, translator));
  }
  return absl::OkStatus();
}

absl::Status InitializeSymbolicActions(
    const TableEntry &entry, const ir::Table &table,
    const ir::P4Program &program, z3::context &z3_context, z3::solver &solver,
    values::P4RuntimeTranslator &translator) {
  absl::btree_map<std::string, z3::expr> action_choices_by_name;
  absl::flat_hash_map<std::string, absl::flat_hash_map<std::string, z3::expr>>
      action_params_by_name;

  // Create symbolic variables for each valid action of the table.
  for (const pdpi::IrActionReference &action_ref :
       table.table_definition().entry_actions()) {
    const std::string &action_name = action_ref.action().preamble().name();

    // Check if the action referred by the table definition exists.
    auto it = program.actions().find(action_name);
    if (it == program.actions().end()) {
      return gutil::NotFoundErrorBuilder()
             << "Action not found: '" << action_name << "'";
    }
    const ir::Action &action = it->second;

    // Create a symbolic variable for the action invocation.
    ASSIGN_OR_RETURN(z3::expr action_invocation,
                     entry.GetActionInvocation(action_name, table, z3_context));
    action_choices_by_name.insert_or_assign(action_name, action_invocation);

    // Create a symbolic variable for each action parameter.
    for (const auto &[param_name, param_definition] :
         Ordered(action.action_definition().params_by_name())) {
      ASSIGN_OR_RETURN(
          z3::expr action_param,
          entry.GetActionParameter(param_name, action, table, z3_context));
      action_params_by_name[action_name].insert_or_assign(param_name,
                                                          action_param);
    }
  }

  // Add well-formedness constraints for the symbolic actions of this entry.
  AddSingleActionChoiceConstraintForSymbolicAction(action_choices_by_name,
                                                   z3_context, solver);

  // Add equality constraints for the symbolic actions if concrete values are
  // specified.
  const pdpi::IrTableEntry &ir_entry = entry.GetPdpiIrTableEntry();
  if (ir_entry.has_action()) {
    RETURN_IF_ERROR(AddConstraintsForConcretePartsOfSymbolicAction(
        ir_entry.action(), action_choices_by_name, action_params_by_name,
        program, z3_context, solver, translator));
  } else if (ir_entry.has_action_set()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Action set should not be specified in a direct match table. "
              "Found: "
           << ir_entry.DebugString();
  }

  return absl::OkStatus();
}

}  // namespace p4_symbolic::symbolic
