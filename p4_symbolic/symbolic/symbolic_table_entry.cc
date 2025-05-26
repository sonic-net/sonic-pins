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

#include "p4_symbolic/symbolic/symbolic_table_entry.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <utility>

#include "absl/algorithm/container.h"
#include "absl/container/btree_map.h"
#include "absl/container/flat_hash_map.h"
#include "absl/log/log.h"
#include "absl/numeric/bits.h"
#include "absl/numeric/int128.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "gutil/collections.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/internal/ordered_map.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_symbolic/ir/ir.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/symbolic/operators.h"
#include "p4_symbolic/symbolic/util.h"
#include "p4_symbolic/symbolic/values.h"
#include "p4_symbolic/z3_util.h"
#include "z3++.h"

namespace p4_symbolic::symbolic {

using MatchType = p4::config::v1::MatchField::MatchType;

namespace {

// Contains the symbolic variable names and bit-width of the symbolic match of a
// table entry.
struct SymbolicMatchInfo {
  p4::config::v1::MatchField::MatchType match_type;
  int bitwidth;
  // Value variable name of the symbolic match. It looks like
  // "<table_name>_entry_<index>_<match_name>_<match_type>_value".
  std::string value_variable_name;
  // Value variable name of the symbolic match. It looks like
  // "<table_name>_entry_<index>_<match_name>_<match_type>_mask".
  std::string mask_variable_name;
};

// Contains the symbolic variable name and bit-width of the symbolic action
// parameter of a table entry.
struct SymbolicActionParameterInfo {
  // Variable name of the symbolic action parameter. It looks like
  // "<table_name>_entry_<index>_<action_name>_<param_name>".
  std::string variable_name;
  int bitwidth;
};

// Evaluates and returns the PDPI IR value for the `bv_expr` of a match field.
absl::StatusOr<pdpi::IrValue> EvalZ3BitvectorToIrValue(
    const z3::expr &bv_expr, const z3::model &model,
    const std::optional<std::string> &field_name, const std::string &type_name,
    const pdpi::Format &format, const values::P4RuntimeTranslator &translator) {
  int bitwidth = bv_expr.get_sort().bv_size();
  const std::string value =
      model.eval(bv_expr, /*model_completion=*/true).to_string();
  return values::TranslateZ3ValueStringToIrValue(value, bitwidth, field_name,
                                                 type_name, translator, format);
}

// Evaluates the given bit-vector and converts it to prefix length. Returns an
// error if the evaluated value is not a valid prefix-length mask.
absl::StatusOr<unsigned int> EvalZ3BitvectorToPrefixLength(
    const z3::expr &bv_expr, const z3::model &model) {
  // Check if the size of the bit-vector is within 128 bits.
  size_t bitwidth = bv_expr.get_sort().bv_size();
  if (bitwidth > 128) {
    return gutil::UnimplementedErrorBuilder()
           << "Only values representable with 128-bit unsigned integers are "
              "currently supported for prefix lengths. Found bit-width: "
           << bitwidth;
  }

  ASSIGN_OR_RETURN(absl::uint128 int_value,
                   EvalZ3BitvectorToUInt128(bv_expr, model));

  // Note that (uint128(1) << 128) != 0. Here we handle the corner case
  // separately.
  absl::uint128 mask;
  if (bitwidth == 128) {
    mask = absl::Uint128Max();
  } else {
    mask = (absl::uint128(1) << bitwidth) - 1;
  }

  // Check if `int_value` is of the form 1*0*.
  if (((~int_value) & (~int_value + 1) & mask) != 0) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Bit-vector value '" << int_value
           << "' is not a valid prefix length.";
  }

  absl::uint128 suffix = ~int_value & mask;
  uint64_t low64 = absl::Uint128Low64(suffix);
  uint64_t high64 = absl::Uint128High64(suffix);
  int suffix_length = absl::bit_width(low64) + absl::bit_width(high64);
  return bitwidth - suffix_length;
}

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
    const SymbolicMatch &variables, z3::context &z3_context,
    z3::solver &solver) {
  // Add type constraints on the symbolic match variables.
  switch (variables.match_type) {
    case p4::config::v1::MatchField::EXACT: {
      // For exact matches, the mask bit-vector must be all-1s.
      unsigned int bitwidth = variables.mask.get_sort().bv_size();
      z3::expr all_ones = z3_context.bv_val(1, 1).repeat(bitwidth);
      ASSIGN_OR_RETURN(z3::expr mask_constraint,
                       operators::Eq(variables.mask, all_ones));
      solver.add(mask_constraint);
      break;
    }
    case p4::config::v1::MatchField::LPM: {
      // For LPM matches, the mask bit-vector must comply with the LPM format.
      // I.e. (~lpm_mask) & (~lpm_mask + 1) == 0
      unsigned int bitwidth = variables.mask.get_sort().bv_size();
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
      unsigned int bitwidth = variables.mask.get_sort().bv_size();
      z3::expr all_ones = z3_context.bv_val(1, 1).repeat(bitwidth);
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
    const SymbolicMatch &variables, z3::solver &solver) {
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
    const SymbolicMatch &variables, const pdpi::IrMatch &ir_match,
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

absl::StatusOr<SymbolicMatchInfo> GetSymbolicMatchInfo(
    const ir::SymbolicTableEntry &symbolic_entry, absl::string_view match_name,
    const ir::Table &table, const ir::P4Program &program) {
  // A static mapping between the PI match type to the type string.
  static const absl::flat_hash_map<MatchType, std::string> match_type_to_str = {
      {MatchType::MatchField_MatchType_EXACT, "exact"},
      {MatchType::MatchField_MatchType_LPM, "lpm"},
      {MatchType::MatchField_MatchType_TERNARY, "ternary"},
      {MatchType::MatchField_MatchType_OPTIONAL, "optional"},
  };

  // Check if the match exists in the table definition.
  if (!table.table_definition().match_fields_by_name().contains(match_name)) {
    return gutil::NotFoundErrorBuilder()
           << "Match '" << match_name << "' not found in table '"
           << ir::GetTableName(symbolic_entry) << "'";
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

  // If the specified match of this entry is an explicit wildcard, return an
  // error and no symbolic variable should be created.
  const auto &matches = symbolic_entry.sketch().matches();
  auto ir_match_it = absl::c_find_if(matches, [&](const pdpi::IrMatch &match) {
    return match.name() == match_name;
  });
  if (ir_match_it == matches.end()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Match '" << match_name
           << "' is an explicit wildcard. The match is omitted in the IR table "
              "entry.To specify a symbolic match, please set the match name "
              " while leaving other fields unset.";
  }

  // Use the matched header field to get the match bit-width.
  auto it = table.table_implementation().match_name_to_field().find(match_name);
  if (it == table.table_implementation().match_name_to_field().end()) {
    return gutil::NotFoundErrorBuilder()
           << "Match '" << match_name
           << "' not found in implementation of table '"
           << ir::GetTableName(symbolic_entry)
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
           << ir::GetTableName(symbolic_entry)
           << "' is inconsistent between the definition and implementation.";
  }

  // Construct and return the variable names with the following template:
  // "<table_name>_entry_<index>_<match_name>_<match_type>_(value|mask)"
  const auto &match_type = pi_match_field.match_type();
  std::string name_prefix = absl::StrCat(
      ir::GetTableName(symbolic_entry), "_entry_", symbolic_entry.index(), "_",
      match_name, "_", match_type_to_str.at(match_type), "_");
  return SymbolicMatchInfo{
      .match_type = match_type,
      .bitwidth = bitwidth,
      .value_variable_name = absl::StrCat(name_prefix, "value"),
      .mask_variable_name = absl::StrCat(name_prefix, "mask"),
  };
}

// Returns the symbolic variable name of the action invocation with the given
// `action_name`. Returns an error if the given `action_name` is not found in
// the table definition.
absl::StatusOr<std::string> GetActionChoiceSymbolicVariableName(
    const ir::SymbolicTableEntry &symbolic_entry, absl::string_view action_name,
    const ir::Table &table) {
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
           << ir::GetTableName(symbolic_entry) << "'";
  }

  // Construct and return the variable name with the following template:
  // "<table_name>_entry_<index>_<action_name>_$chosen$"
  return absl::StrCat(ir::GetTableName(symbolic_entry), "_entry_",
                      symbolic_entry.index(), "_", action_name, "_$chosen$");
}

// Returns the symbolic variable name and the bit-width of the action
// parameter with the given `action_name` and `param_name`. Returns an error if
// the given `action_name` and `param_name` are not found in the table and
// action definition.
absl::StatusOr<SymbolicActionParameterInfo> GetSymbolicActionParameterInfo(
    const ir::SymbolicTableEntry &symbolic_entry, absl::string_view param_name,
    const ir::Action &action, const ir::Table &table) {
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
           << ir::GetTableName(symbolic_entry) << "'";
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
  return SymbolicActionParameterInfo{
      .variable_name = absl::StrCat(ir::GetTableName(symbolic_entry), "_entry_",
                                    symbolic_entry.index(), "_", action_name,
                                    "_", param_name),
      .bitwidth = bitwidth,
  };
}

}  // namespace

absl::StatusOr<SymbolicMatch> GetSymbolicMatch(
    const ir::SymbolicTableEntry &symbolic_entry, absl::string_view match_name,
    const ir::Table &table, const ir::P4Program &program,
    z3::context &z3_context) {
  // Get symbolic variable names.
  ASSIGN_OR_RETURN(
      SymbolicMatchInfo match,
      GetSymbolicMatchInfo(symbolic_entry, match_name, table, program));

  // Construct and return the symbolic variables as Z3 expressions.
  return SymbolicMatch{
      .match_type = match.match_type,
      .value = z3_context.bv_const(match.value_variable_name.c_str(),
                                   match.bitwidth),
      .mask =
          z3_context.bv_const(match.mask_variable_name.c_str(), match.bitwidth),
  };
}

absl::StatusOr<z3::expr> GetSymbolicActionInvocation(
    const ir::SymbolicTableEntry &symbolic_entry, absl::string_view action_name,
    const ir::Table &table, z3::context &z3_context) {
  // Get symbolic variable names.
  ASSIGN_OR_RETURN(
      std::string variable_name,
      GetActionChoiceSymbolicVariableName(symbolic_entry, action_name, table));

  // Construct and return the symbolic variable as a Z3 expression.
  return z3_context.bool_const(variable_name.c_str());
}

absl::StatusOr<z3::expr> GetSymbolicActionParameter(
    const ir::SymbolicTableEntry &symbolic_entry, absl::string_view param_name,
    const ir::Action &action, const ir::Table &table, z3::context &z3_context) {
  // Get symbolic variable names.
  ASSIGN_OR_RETURN(SymbolicActionParameterInfo action_param,
                   GetSymbolicActionParameterInfo(symbolic_entry, param_name,
                                                  action, table));

  // Construct and return the symbolic variable as a Z3 expression.
  return z3_context.bv_const(action_param.variable_name.c_str(),
                             action_param.bitwidth);
}

absl::Status InitializeSymbolicMatches(
    const ir::SymbolicTableEntry &symbolic_entry, const ir::Table &table,
    const ir::P4Program &program, z3::context &z3_context, z3::solver &solver,
    values::P4RuntimeTranslator &translator) {
  for (const pdpi::IrMatch &match : symbolic_entry.sketch().matches()) {
    if (match.name().empty()) {
      return gutil::InvalidArgumentErrorBuilder()
             << "The match name must not be empty. Found: "
             << match.DebugString();
    }

    // Create symbolic variables for the symbolic match.
    ASSIGN_OR_RETURN(SymbolicMatch variables,
                     GetSymbolicMatch(symbolic_entry, match.name(), table,
                                      program, z3_context));
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
    const ir::SymbolicTableEntry &symbolic_entry, const ir::Table &table,
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
                     GetSymbolicActionInvocation(symbolic_entry, action_name,
                                                 table, z3_context));
    action_choices_by_name.insert_or_assign(action_name, action_invocation);

    // Create a symbolic variable for each action parameter.
    for (const auto &[param_name, param_definition] :
         Ordered(action.action_definition().params_by_name())) {
      ASSIGN_OR_RETURN(z3::expr action_param,
                       GetSymbolicActionParameter(symbolic_entry, param_name,
                                                  action, table, z3_context));
      action_params_by_name[action_name].insert_or_assign(param_name,
                                                          action_param);
    }
  }

  // Add well-formedness constraints for the symbolic actions of this entry.
  AddSingleActionChoiceConstraintForSymbolicAction(action_choices_by_name,
                                                   z3_context, solver);

  // Add equality constraints for the symbolic actions if concrete values are
  // specified.
  switch (symbolic_entry.sketch().type_case()) {
    case pdpi::IrTableEntry::kAction: {
      RETURN_IF_ERROR(AddConstraintsForConcretePartsOfSymbolicAction(
          symbolic_entry.sketch().action(), action_choices_by_name,
          action_params_by_name, program, z3_context, solver, translator));
      break;
    }
    case pdpi::IrTableEntry::kActionSet: {
      return gutil::InvalidArgumentErrorBuilder()
             << "Action set should not be specified in a direct match table. "
                "Found: "
             << symbolic_entry.DebugString();
    }
    case pdpi::IrTableEntry::TYPE_NOT_SET:
      break;
  }

  return absl::OkStatus();
}

// Returns a concrete table entry extracted from the given `symbolic_entry`
// based on the given `model` and `translator`.
absl::StatusOr<ir::ConcreteTableEntry> ExtractConcreteEntryFromModel(
    const ir::SymbolicTableEntry &entry, const z3::model &model,
    const ir::P4Program &program, const values::P4RuntimeTranslator &translator,
    z3::context &z3_context) {
  ir::ConcreteTableEntry result;
  result.set_index(entry.index());

  // Check if the table specified by the symbolic entry exists.
  const std::string &table_name = ir::GetTableName(entry);
  ASSIGN_OR_RETURN(const ir::Table *table,
                   util::GetIrTable(program, table_name));

  // Construct the concrete PDPI IR entry.
  // By assigning the symbolic sketch to the concrete IR entry, we keep things
  // that are not under the control of P4-Symbolic intact (e.g., table_name,
  // priority, meter_config, counter_data, meter_counter_data,
  // controller_metadata).
  pdpi::IrTableEntry &result_entry =
      *result.mutable_pdpi_ir_entity()->mutable_table_entry();
  result_entry = entry.sketch();
  result_entry.clear_matches();
  result_entry.clear_action();
  result_entry.clear_action_set();

  // Set matches.
  for (const pdpi::IrMatch &symbolic_match : entry.sketch().matches()) {
    bool wildcard = false;
    pdpi::IrMatch concrete_match;

    // Set match name.
    const std::string &match_name = symbolic_match.name();
    concrete_match.set_name(match_name);

    // Evaluate and set match values.
    ASSIGN_OR_RETURN(
        SymbolicMatch match_variables,
        GetSymbolicMatch(entry, match_name, *table, program, z3_context));
    ASSIGN_OR_RETURN(std::string field_name,
                     util::GetFieldNameFromMatch(match_name, *table));
    ASSIGN_OR_RETURN(pdpi::IrMatchFieldDefinition match_definition,
                     util::GetMatchDefinition(match_name, *table));
    const std::string &type_name =
        match_definition.match_field().type_name().name();
    ASSIGN_OR_RETURN(pdpi::IrValue value,
                     EvalZ3BitvectorToIrValue(
                         match_variables.value, model, field_name, type_name,
                         match_definition.format(), translator));

    switch (match_variables.match_type) {
      case MatchType::MatchField_MatchType_EXACT: {
        *concrete_match.mutable_exact() = std::move(value);
        break;
      }
      case MatchType::MatchField_MatchType_LPM: {
        *concrete_match.mutable_lpm()->mutable_value() = std::move(value);
        ASSIGN_OR_RETURN(int prefix_length, EvalZ3BitvectorToPrefixLength(
                                                match_variables.mask, model));
        concrete_match.mutable_lpm()->set_prefix_length(prefix_length);
        if (prefix_length == 0) wildcard = true;
        break;
      }
      case MatchType::MatchField_MatchType_TERNARY: {
        ASSIGN_OR_RETURN(pdpi::IrValue mask,
                         EvalZ3BitvectorToIrValue(
                             match_variables.mask, model, field_name, type_name,
                             match_definition.format(), translator));
        *concrete_match.mutable_ternary()->mutable_value() = std::move(value);
        *concrete_match.mutable_ternary()->mutable_mask() = std::move(mask);
        ASSIGN_OR_RETURN(absl::uint128 mask_value,
                         EvalZ3BitvectorToUInt128(match_variables.mask, model));
        if (mask_value == 0) wildcard = true;
        break;
      }
      case MatchType::MatchField_MatchType_OPTIONAL: {
        *concrete_match.mutable_optional()->mutable_value() = std::move(value);
        ASSIGN_OR_RETURN(int prefix_length, EvalZ3BitvectorToPrefixLength(
                                                match_variables.mask, model));
        const size_t bitwidth = match_variables.value.get_sort().bv_size();
        if (prefix_length != 0 && prefix_length != bitwidth) {
          return gutil::InternalErrorBuilder()
                 << "The mask must be either all-1s or all-0s for optional "
                    "matches. Found prefix length "
                 << prefix_length;
        }
        if (prefix_length == 0) wildcard = true;
        break;
      }
      default: {
        return gutil::InvalidArgumentErrorBuilder()
               << "Invalid match type, must be one of [exact, lpm, ternary, "
                  "optional]. Found: "
               << match_variables.match_type;
      }
    }

    if (!wildcard) {
      *result_entry.add_matches() = std::move(concrete_match);
    }
  }

  // Check if the table is a WCMP table.
  if (table->table_definition().has_action_profile_id()) {
    return gutil::UnimplementedErrorBuilder()
           << "Table entries with symbolic action sets are not supported "
              "at the moment.";
  }

  // Set the invoked action of the entry.
  std::optional<std::string> previous_action_applied;

  for (const auto &action_ref : table->table_definition().entry_actions()) {
    const std::string &action_name = action_ref.action().preamble().name();
    ASSIGN_OR_RETURN(
        z3::expr action_invocation,
        GetSymbolicActionInvocation(entry, action_name, *table, z3_context));
    ASSIGN_OR_RETURN(bool action_applied, EvalZ3Bool(action_invocation, model));
    if (!action_applied) continue;

    // Make sure only one action is applied for each entry.
    if (previous_action_applied) {
      return gutil::InternalErrorBuilder()
             << "More than one action is applied for an entry in a non-WCMP "
                "table: '"
             << *previous_action_applied << "' and '" << action_name << "'";
    }
    previous_action_applied = action_name;

    // Check and get the action in P4-Symbolic IR.
    auto it = program.actions().find(action_name);
    if (it == program.actions().end()) {
      return gutil::NotFoundErrorBuilder()
             << "Action '" << action_name << "' not found.";
    }
    const ir::Action &action = it->second;

    // Set action name.
    result_entry.mutable_action()->set_name(action_name);

    // Set action parameters.
    for (const auto &[param_name, param_definition] :
         Ordered(action.action_definition().params_by_name())) {
      // Set action parameter name.
      pdpi::IrActionInvocation::IrActionParam &ir_param =
          *result_entry.mutable_action()->add_params();
      ir_param.set_name(param_name);
      // Set action parameter value.
      ASSIGN_OR_RETURN(z3::expr param,
                       GetSymbolicActionParameter(entry, param_name, action,
                                                  *table, z3_context));
      ASSIGN_OR_RETURN(
          pdpi::IrValue value,
          EvalZ3BitvectorToIrValue(param, model, /*field_name=*/std::nullopt,
                                   param_definition.param().type_name().name(),
                                   param_definition.format(), translator));
      *ir_param.mutable_value() = std::move(value);
    }
  }

  // Build and return the concrete table entry.
  return result;
}

}  // namespace p4_symbolic::symbolic
