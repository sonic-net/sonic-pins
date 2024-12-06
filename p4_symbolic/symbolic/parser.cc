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

#include "p4_symbolic/symbolic/parser.h"

#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/str_format.h"
#include "gutil/status.h"
#include "p4_pdpi/internal/ordered_map.h"
#include "p4_symbolic/ir/ir.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/symbolic/action.h"
#include "p4_symbolic/symbolic/operators.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/symbolic/util.h"
#include "p4_symbolic/z3_util.h"
#include "z3++.h"

namespace p4_symbolic::symbolic::parser {

namespace {

// Evaluates the given "extract" parser operation.
// We assume that the input packet has enough bits for the extract operation,
// and so the operation never fails. The symbolic evaluation is implemented by
// setting the `$valid$` and `$extracted$` fields to `guard` and then verifying
// that all fields within the extracted header are free bit-vector variables.
// Reference: go/p4-symbolic-parser-support.
absl::Status EvaluateExtractParserOperation(
    const ir::P4Program &program,
    const ir::ParserOperation::Extract &extract_op,
    SymbolicPerPacketState &state, const z3::expr &guard) {
  // The extracted header must exists.
  const std::string &header_name = extract_op.header().header_name();
  auto it = program.headers().find(header_name);
  if (it == program.headers().end()) {
    return gutil::NotFoundErrorBuilder() << "Header not found: " << header_name;
  }

  // Set the "valid" and "extracted" fields of the header to `guard`.
  RETURN_IF_ERROR(state.Set(header_name, kValidPseudoField,
                            Z3Context().bool_val(true), guard));
  RETURN_IF_ERROR(state.Set(header_name, kExtractedPseudoField,
                            Z3Context().bool_val(true), guard));

  // Verify if all fields of the header are single, free bit-vector variables.
  for (const auto &[field_name, ir_field] : Ordered(it->second.fields())) {
    std::string field_full_name =
        absl::StrFormat("%s.%s", header_name, field_name);
    ASSIGN_OR_RETURN(const z3::expr &field, state.Get(field_full_name));
    if (field.to_string() != field_full_name || !field.is_bv() ||
        field.get_sort().bv_size() !=
            static_cast<unsigned int>(ir_field.bitwidth())) {
      return gutil::InvalidArgumentErrorBuilder()
             << "Field '" << field_full_name
             << "' should be a free bit-vector. Found: " << field;
    }
  }

  return absl::OkStatus();
}

// Constructs a symbolic expression corresponding to the given R-value of the
// set operation.
absl::StatusOr<z3::expr> EvaluateSetOperationRValue(
    const ir::ParserOperation::Set &set_op, const SymbolicPerPacketState &state,
    const action::ActionContext &context) {
  switch (set_op.rvalue_case()) {
    case ir::ParserOperation::Set::RvalueCase::kFieldRvalue: {
      return action::EvaluateFieldValue(set_op.field_rvalue(), state, context);
    }
    case ir::ParserOperation::Set::RvalueCase::kHexstrRvalue: {
      return action::EvaluateHexStr(set_op.hexstr_rvalue());
    }
    case ir::ParserOperation::Set::RvalueCase::kLookaheadRvalue: {
      return gutil::UnimplementedErrorBuilder()
             << "Lookahead R-values for set operations are not supported.";
    }
    case ir::ParserOperation::Set::RvalueCase::kExpressionRvalue: {
      return action::EvaluateRExpression(set_op.expression_rvalue(), state,
                                         context);
    }
    default: {
      return gutil::InvalidArgumentErrorBuilder()
             << "Invalid R-value type of a set operation: "
             << set_op.DebugString();
    }
  }
}

// Evaluates the given "set" parser operation.
absl::Status EvaluateSetParserOperation(const ir::ParserOperation::Set &set_op,
                                        SymbolicPerPacketState &state,
                                        const action::ActionContext &context,
                                        const z3::expr &guard) {
  // Get the field name of the L-value and the expression of the R-value.
  const ir::FieldValue &field_value = set_op.lvalue();
  ASSIGN_OR_RETURN(z3::expr rvalue,
                   EvaluateSetOperationRValue(set_op, state, context));
  // Set the header field to the symbolic expression.
  RETURN_IF_ERROR(state.Set(field_value.header_name(), field_value.field_name(),
                            rvalue, guard));
  return absl::OkStatus();
}

// Evaluates the given "primitive" parser operation.
absl::Status EvaluatePrimitiveParserOperation(
    const ir::ParserOperation::Primitive &primitive,
    SymbolicPerPacketState &state, action::ActionContext &context,
    const z3::expr &guard) {
  switch (primitive.statement_case()) {
    case ir::ParserOperation::Primitive::StatementCase::kAssignment: {
      return action::EvaluateAssignmentStatement(primitive.assignment(), &state,
                                                 &context, guard);
    }
    default: {
      return gutil::UnimplementedErrorBuilder()
             << "Parse state '" << context.action_name
             << "' contains unsupported primitive parser operation: "
             << primitive.DebugString();
    }
  }

  return absl::OkStatus();
}

// Evaluates the given parser operation.
absl::Status EvaluateParserOperation(const ir::P4Program &program,
                                     const ir::ParserOperation &op,
                                     SymbolicPerPacketState &state,
                                     action::ActionContext &context,
                                     const z3::expr &guard) {
  switch (op.operation_case()) {
    case ir::ParserOperation::OperationCase::kExtract: {
      return EvaluateExtractParserOperation(program, op.extract(), state,
                                            guard);
    }
    case ir::ParserOperation::OperationCase::kSet: {
      return EvaluateSetParserOperation(op.set(), state, context, guard);
    }
    case ir::ParserOperation::OperationCase::kPrimitive: {
      return EvaluatePrimitiveParserOperation(op.primitive(), state, context,
                                              guard);
    }
    default: {
      return gutil::InvalidArgumentErrorBuilder()
             << "Parser operation must be set as one of [extract, set, "
                "primitive]. Found: "
             << op.DebugString();
    }
  }

  return absl::OkStatus();
}

// Constructs the expression that encodes the match condition for the given
// `ir_value` and `ir_mask`. Note that this builds the match condition for one
// transition only regardless of whether the key matches other transitions or
// not.
absl::StatusOr<z3::expr> ConstructHexStringMatchCondition(
    const ir::HexstrValue &ir_value, const ir::HexstrValue &ir_mask,
    const z3::expr &transition_key) {
  ASSIGN_OR_RETURN(z3::expr value, action::EvaluateHexStr(ir_value));

  if (ir_mask.value().empty()) {
    // The mask is not set. The key is matched against a single value.
    // Reference:
    // https://p4.org/p4-spec/docs/P4-16-v-1.2.3.html#sec-singleton-set
    return operators::Eq(value, transition_key);
  } else {
    // The mask is set. A key is said to be matched if and only if (key & mask
    // == value & mask).  Reference:
    // https://p4.org/p4-spec/docs/P4-16-v-1.2.3.html#sec-cubes
    ASSIGN_OR_RETURN(z3::expr mask, action::EvaluateHexStr(ir_mask));
    ASSIGN_OR_RETURN(z3::expr masked_value, operators::BitAnd(value, mask));
    ASSIGN_OR_RETURN(z3::expr masked_key,
                     operators::BitAnd(transition_key, mask));
    return operators::Eq(masked_value, masked_key);
  }
}

// Constructs the match conditions for each transition in the given
// `parse_state`. Note that it builds the match condition of each transition
// independently regardless of whether the transition key in the given
// `parse_state` matches another transition or not.
absl::StatusOr<std::vector<z3::expr>> ConstructMatchConditions(
    const ir::ParseState &parse_state, const SymbolicPerPacketState &state,
    const z3::expr &guard) {
  // Collect all transition key fields to construct the transition key.
  z3::expr_vector key_fields(Z3Context());

  for (const ir::ParserTransitionKeyField &key_field :
       parse_state.transition_key_fields()) {
    if (key_field.key_field_case() !=
        ir::ParserTransitionKeyField::KeyFieldCase::kField) {
      return gutil::UnimplementedErrorBuilder()
             << "Transition key field must be a header field. Found: "
             << key_field.DebugString();
    }

    const ir::FieldValue &field_value = key_field.field();
    ASSIGN_OR_RETURN(
        z3::expr key_field_expr,
        state.Get(field_value.header_name(), field_value.field_name()));
    key_fields.push_back(std::move(key_field_expr));
  }

  // Construct the transition key by concatenating all the key fields.
  absl::optional<z3::expr> transition_key;
  if (!key_fields.empty()) {
    // This is necessary because if `key_fields` is empty, which can be the case
    // for parse states that have only one default transition, `z3::concat` will
    // trigger an assertion failure.
    transition_key = z3::concat(key_fields);
  }

  // Build the match condition for each transition.
  std::vector<z3::expr> match_conditions;
  match_conditions.reserve(parse_state.transitions_size());

  for (int i = 0; i < parse_state.transitions_size(); ++i) {
    const ir::ParserTransition &transition = parse_state.transitions(i);

    switch (transition.transition_case()) {
      case ir::ParserTransition::TransitionCase::kDefaultTransition: {
        // The P4 compiler should have removed the transitions specified after a
        // default transition. Therefore, if there is a default transition in
        // the IR, it must be the last transition of the current parse state.
        if (i != parse_state.transitions_size() - 1) {
          return gutil::InvalidArgumentErrorBuilder()
                 << "A default transition is not the last transition in a "
                    "parse state. Found: "
                 << parse_state.DebugString();
        }

        // The key set of a default transition specified by the keywords
        // "default" or "_" is referred to as the "universal set" that contains
        // any transition key, which means the match condition is always true.
        // Ref: https://p4.org/p4-spec/docs/P4-16-v-1.2.3.html#sec-universal-set
        match_conditions.push_back(Z3Context().bool_val(true));
        break;
      }
      case ir::ParserTransition::TransitionCase::kHexStringTransition: {
        // Make sure there is the transition key to be matched against.
        if (!transition_key.has_value()) {
          return gutil::NotFoundErrorBuilder()
                 << "No transition key specified but hex string transitions "
                    "exist.";
        }

        ASSIGN_OR_RETURN(
            z3::expr match_condition,
            ConstructHexStringMatchCondition(
                transition.hex_string_transition().value(),
                transition.hex_string_transition().mask(), *transition_key));
        match_conditions.push_back(std::move(match_condition));
        break;
      }
      default: {
        return gutil::InvalidArgumentErrorBuilder()
               << "Transition type must default or hex string. Found: "
               << transition.DebugString();
      }
    }
  }

  return match_conditions;
}

// Constructs the transition guard for each transition given their
// `match_conditions`. The transition guard of a given transition `i` is defined
// as: `guard` && match_conditions[i] && (!match_conditions[j] for all j < i).
// Namely, the match condition of the given transition `i` is true, while the
// match conditions of all previous (higher-priority) transitions are false.
// This ensures that the transition guards of all transitions from the same
// parse state are mutual exclusive.
std::vector<z3::expr> ConstructTransitionGuards(
    const std::vector<z3::expr> &match_conditions, const z3::expr &guard) {
  std::vector<z3::expr> transition_guards;
  transition_guards.reserve(match_conditions.size());
  z3::expr cumulative_reachability_condition = guard;

  for (const auto &match_condition : match_conditions) {
    transition_guards.push_back(cumulative_reachability_condition &&
                                match_condition);
    cumulative_reachability_condition =
        cumulative_reachability_condition && (!match_condition);
  }

  return transition_guards;
}

// Constructs the fall-through guard. The fall-through guard encodes the path
// condition where all previous transitions in a "select" expression did not get
// matched with the transition key, which may happen, for example, in the
// following P4 program, if the `ether_type` of the input packet does not match
// any of the specified match conditions.
//
// ```p4
//   state parse_ethernet {
//     packet.extract(header.ethernet);
//     transition select(header.ethernet.ether_type) {
//       ETHERTYPE_IPV4: parse_ipv4;
//       ETHERTYPE_IPV6: parse_ipv6;
//     }
//   }
// ```
z3::expr ConstructFallThroughGuard(
    const std::vector<z3::expr> &match_conditions, const z3::expr &guard) {
  z3::expr fall_through_guard = guard;

  for (const auto &match_condition : match_conditions) {
    fall_through_guard = fall_through_guard && (!match_condition);
  }

  return fall_through_guard;
}

}  // namespace p4_symbolic::symbolic::parser
