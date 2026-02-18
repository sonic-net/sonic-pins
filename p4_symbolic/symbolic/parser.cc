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

#include <cstddef>
#include <string>
#include <utility>
#include <vector>

#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_format.h"
#include "absl/types/optional.h"
#include "gutil/gutil/status.h"
#include "p4_infra/p4_pdpi/internal/ordered_map.h"
#include "p4_symbolic/ir/ir.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesizer.pb.h"
#include "p4_symbolic/symbolic/action.h"
#include "p4_symbolic/symbolic/context.h"
#include "p4_symbolic/symbolic/control.h"
#include "p4_symbolic/symbolic/operators.h"
#include "p4_symbolic/symbolic/solver_state.h"
#include "p4_symbolic/symbolic/util.h"
#include "p4_symbolic/symbolic/v1model.h"
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
    SymbolicPerPacketState &headers, z3::context &z3_context,
    const z3::expr &guard) {
  // The extracted header must exists.
  const std::string &header_name = extract_op.header().header_name();
  auto it = program.headers().find(header_name);
  if (it == program.headers().end()) {
    return gutil::NotFoundErrorBuilder() << "Header not found: " << header_name;
  }

  // Set the "valid" and "extracted" fields of the header to `guard`.
  RETURN_IF_ERROR(headers.Set(header_name, kValidPseudoField,
                              z3_context.bool_val(true), guard));
  RETURN_IF_ERROR(headers.Set(header_name, kExtractedPseudoField,
                              z3_context.bool_val(true), guard));

  // Verify if all fields of the header are single, free bit-vector variables.
  for (const auto &[field_name, ir_field] : Ordered(it->second.fields())) {
    std::string field_full_name =
        absl::StrFormat("%s.%s", header_name, field_name);
    ASSIGN_OR_RETURN(const z3::expr &field, headers.Get(field_full_name));
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
    const ir::ParserOperation::Set &set_op,
    const SymbolicPerPacketState &headers, const action::ActionContext &context,
    z3::context &z3_context) {
  switch (set_op.rvalue_case()) {
    case ir::ParserOperation::Set::RvalueCase::kFieldRvalue: {
      return action::EvaluateFieldValue(set_op.field_rvalue(), headers);
    }
    case ir::ParserOperation::Set::RvalueCase::kHexstrRvalue: {
      return action::EvaluateHexStr(set_op.hexstr_rvalue(), z3_context);
    }
    case ir::ParserOperation::Set::RvalueCase::kLookaheadRvalue: {
      return gutil::UnimplementedErrorBuilder()
             << "Lookahead R-values for set operations are not supported.";
    }
    case ir::ParserOperation::Set::RvalueCase::kExpressionRvalue: {
      return action::EvaluateRExpression(set_op.expression_rvalue(), headers,
                                         context, z3_context);
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
                                        SymbolicPerPacketState &headers,
                                        const action::ActionContext &context,
                                        z3::context &z3_context,
                                        const z3::expr &guard) {
  // Get the field name of the L-value and the expression of the R-value.
  const ir::FieldValue &field_value = set_op.lvalue();
  ASSIGN_OR_RETURN(z3::expr rvalue, EvaluateSetOperationRValue(
                                        set_op, headers, context, z3_context));
  // Set the header field to the symbolic expression.
  RETURN_IF_ERROR(headers.Set(field_value.header_name(),
                              field_value.field_name(), rvalue, guard));
  return absl::OkStatus();
}

// Evaluates the given "primitive" parser operation.
absl::Status EvaluatePrimitiveParserOperation(
    const ir::ParserOperation::Primitive &primitive,
    SymbolicPerPacketState &headers, action::ActionContext &context,
    z3::context &z3_context, const z3::expr &guard) {
  switch (primitive.statement_case()) {
    case ir::ParserOperation::Primitive::StatementCase::kAssignment: {
      return action::EvaluateAssignmentStatement(
          primitive.assignment(), headers, &context, z3_context, guard);
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
                                     SymbolicPerPacketState &headers,
                                     action::ActionContext &context,
                                     z3::context &z3_context,
                                     const z3::expr &guard) {
  switch (op.operation_case()) {
    case ir::ParserOperation::OperationCase::kExtract: {
      return EvaluateExtractParserOperation(program, op.extract(), headers,
                                            z3_context, guard);
    }
    case ir::ParserOperation::OperationCase::kSet: {
      return EvaluateSetParserOperation(op.set(), headers, context, z3_context,
                                        guard);
    }
    case ir::ParserOperation::OperationCase::kPrimitive: {
      return EvaluatePrimitiveParserOperation(op.primitive(), headers, context,
                                              z3_context, guard);
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
  z3::context &z3_context = transition_key.ctx();
  ASSIGN_OR_RETURN(z3::expr value,
                   action::EvaluateHexStr(ir_value, z3_context));

  if (ir_mask.value().empty()) {
    // The mask is not set. The key is matched against a single value.
    // Reference:
    // https://p4.org/p4-spec/docs/P4-16-v-1.2.3.html#sec-singleton-set
    return operators::Eq(value, transition_key);
  } else {
    // The mask is set. A key is said to be matched if and only if (key & mask
    // == value & mask).  Reference:
    // https://p4.org/p4-spec/docs/P4-16-v-1.2.3.html#sec-cubes
    ASSIGN_OR_RETURN(z3::expr mask,
                     action::EvaluateHexStr(ir_mask, z3_context));
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
    const ir::ParseState &parse_state, const SymbolicPerPacketState &headers,
    z3::context &z3_context, const z3::expr &guard) {
  // Collect all transition key fields to construct the transition key.
  z3::expr_vector key_fields(z3_context);

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
        headers.Get(field_value.header_name(), field_value.field_name()));
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
        match_conditions.push_back(z3_context.bool_val(true));
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

// Obtains the next state name of the given `transition`.
absl::StatusOr<std::string> GetNextState(
    const ir::ParserTransition &transition) {
  switch (transition.transition_case()) {
    case ir::ParserTransition::TransitionCase::kDefaultTransition: {
      return transition.default_transition().next_state();
    }
    case ir::ParserTransition::TransitionCase::kHexStringTransition: {
      return transition.hex_string_transition().next_state();
    }
    default: {
      return gutil::InvalidArgumentErrorBuilder()
             << "Transition type must default or hex string. Found: "
             << transition.DebugString();
    }
  }
}

absl::Status SetParserError(const ir::P4Program &program,
                            z3::context &z3_context,
                            SymbolicPerPacketState &headers,
                            const std::string &error_name,
                            const z3::expr &guard) {
  ASSIGN_OR_RETURN(z3::expr error_code,
                   GetErrorCodeExpression(program, error_name, z3_context));
  return headers.Set(v1model::kParserErrorField, std::move(error_code), guard);
}

// Evaluates the parse state with the given `state_name` in the given parser.
absl::Status EvaluateParseState(const ir::P4Program &program,
                                const ir::Parser &parser,
                                const std::string &state_name,
                                SymbolicPerPacketState &headers,
                                z3::context &z3_context,
                                const z3::expr &guard) {
  // Base case. We got to the end of the parser execution path.
  if (state_name == ir::EndOfParser()) {
    return absl::OkStatus();
  }

  // Get the parse state with the given state name.
  auto it = parser.parse_states().find(state_name);
  if (it == parser.parse_states().end()) {
    return gutil::NotFoundErrorBuilder()
           << "Parse state not found: " << state_name;
  }

  const ir::ParseState &parse_state = it->second;

  // We evaluate a parse state by first evaluating all the parser operations
  // defined in this state, and then evaluating each transition conditionally,
  // where it transitions into the next parse state recursively. For optimized
  // symbolic execution (go/optimized-symbolic-execution), we evaluate each
  // transition conditionally only when the next state of the transition is not
  // the merge point. Once all such transitions are evaluated, the execution
  // continues at the merge point. The condition of each transition is
  // constructed according to the P4 semantics. The match conditions of
  // different transitions may overlap, meaning that more than one transition
  // may be valid for the same transition key, in which case, the priority of
  // the transitions is defined by the order in which they are specified in the
  // original P4 program.
  // See go/p4-symbolic-parser-support.
  // b/285404691: Note that in the current implementation, a parse state may
  // still be evaluated more than once.

  // Evaluate the parser operations in this parse state.
  action::ActionContext fake_context = {state_name, {}};
  for (const ir::ParserOperation &op : parse_state.parser_ops()) {
    RETURN_IF_ERROR(EvaluateParserOperation(program, op, headers, fake_context,
                                            z3_context, guard));
  }

  // Construct the match condition of each transition.
  ASSIGN_OR_RETURN(
      std::vector<z3::expr> match_conditions,
      ConstructMatchConditions(parse_state, headers, z3_context, guard));

  const std::string &merge_point =
      parse_state.optimized_symbolic_execution_info().merge_point();

  // Create a SymbolicPerPacketState (local map) for each transition choice.
  // Duplicate existing headers (incoming) to individual local headers
  // for each transition choice.
  std::vector<SymbolicPerPacketState> local_headers_per_transition(
      match_conditions.size(), headers);

  // Evaluate each next state that is not the merge point.
  for (size_t i = 0; i < match_conditions.size(); ++i) {
    ASSIGN_OR_RETURN(std::string next_state,
                     GetNextState(parse_state.transitions(i)));
    if (next_state != merge_point) {
      // We pass `true` as the guard expression here (effectively no guard).
      // The proper guard is applied during the merge process (see below).
      RETURN_IF_ERROR(EvaluateParseState(
          program, parser, next_state, local_headers_per_transition[i],
          z3_context, z3_context.bool_val(true)));
    }
  }

  // Merge process:
  // Iterate through each field and merge the results of each transition.
  // The merge is done using the following formula
  // (for every field in the header):
  // resulting_header_field_value =
  //   if match_conditions[0]
  //     then local_header_per_transition[0].Get(field)
  //     else if match_conditions[1]
  //       then local_header_per_transition[1].Get(field)
  //       else ...
  //         ...
  //         else local_header_per_transition[n].Get(field)
  // At the end, the resulting_header_field_value is assigned to the
  // field in the resulting header.
  for (const auto &[field, _] : headers) {
    ASSIGN_OR_RETURN(z3::expr resulting_header_field_value, headers.Get(field));

    for (int row = match_conditions.size() - 1; row >= 0; row--) {
      ASSIGN_OR_RETURN(z3::expr local_header_field_value,
                       local_headers_per_transition[row].Get(field));
      ASSIGN_OR_RETURN(
          resulting_header_field_value,
          operators::Ite(match_conditions.at(row), local_header_field_value,
                         resulting_header_field_value));
    }
    RETURN_IF_ERROR(headers.Set(field, resulting_header_field_value, guard));
  }

  z3::expr merge_point_guard = guard;

  // If the last transition is not a default transition, i.e., the last match
  // condition is not TRUE, it is possible that a packet does not match any
  // valid transition of the parse state. In that case, the P4 program will mark
  // the `standard_metadata.parser_error` as `error.NoMatch`, skip the rest of
  // the parser, and then continue to the ingress pipeline directly.
  // Reference: https://p4.org/p4-spec/docs/P4-16-v-1.2.3.html#sec-select.
  //
  // We construct the fall-through guard and then evaluate the fall-through
  // scenario. Technically we can always evaluate the fall-through scenario and
  // encode it in the symbolic state, but if there is a default transition, the
  // fall-through guard will always be evaluated to FALSE, so we evaluate this
  // conditionally to save Z3 some effort.
  if (!match_conditions.empty() &&
      match_conditions.back() != z3_context.bool_val(true)) {
    z3::expr fall_through_guard =
        ConstructFallThroughGuard(match_conditions, guard);

    // Here we apply the side effect for the fall-through scenario. The "next
    // state" in this case will be the end of parser, so there is no need to do
    // anything else. The fall-through guard should be sufficient to ensure that
    // if the fall-through guard is true, no other transitions will happen.
    RETURN_IF_ERROR(SetParserError(program, z3_context, headers, "NoMatch",
                                   fall_through_guard));

    // If a fall-through is possible, the `merge_point_guard` should be the
    // negation of the `fall_through_guard` under the current `guard`.
    merge_point_guard = guard && !fall_through_guard;
  }

  // Continue the evaluation at the merge point or terminate this execution
  // path, where the merge point is guaranteed to be evaluated through a
  // different path.
  if (parse_state.optimized_symbolic_execution_info()
          .continue_to_merge_point()) {
    return EvaluateParseState(program, parser, merge_point, headers, z3_context,
                              merge_point_guard);
  } else {
    return absl::OkStatus();
  }
}

absl::Status EvaluateParseStateDfs(
    const ir::P4Program &program, const ir::Parser &parser,
    const std::string &state_name, SymbolicPerPacketState &headers,
    z3::context &z3_context, SolverState &state,
    packet_synthesizer::PacketSynthesisResults &results) {
  // Base case. We got to the end of the parser execution path.
  if (state_name == ir::EndOfParser()) {
    // At the end of the parser pipeline for a particular path in the parser,
    // the execution moves to the "ingress" pipeline.
    // The "ingress" pipeline is the evaluated with the current parser path
    // and the current headers packet state.
    RETURN_IF_ERROR(
        control::EvaluatePipelineDfs("ingress", state, headers, results));
    return absl::OkStatus();
  }

  // Get the parse state with the given state name.
  auto it = parser.parse_states().find(state_name);
  if (it == parser.parse_states().end()) {
    return gutil::NotFoundErrorBuilder()
           << "Parse state not found: " << state_name;
  }

  const ir::ParseState &parse_state = it->second;

  // We evaluate a parse state by first evaluating all the parser operations
  // defined in this state.

  // Evaluate the parser operations in this parse state.
  action::ActionContext fake_context = {state_name, {}};
  for (const ir::ParserOperation &op : parse_state.parser_ops()) {
    RETURN_IF_ERROR(EvaluateParserOperation(program, op, headers, fake_context,
                                            z3_context,
                                            z3_context.bool_val(true)));
  }

  // Construct the match condition of each transition.
  ASSIGN_OR_RETURN(std::vector<z3::expr> match_conditions,
                   ConstructMatchConditions(parse_state, headers, z3_context,
                                            z3_context.bool_val(true)));

  // Evaluate every parser transition one-by-one.
  // For every transition, the match condition is added to the
  // solver state to check if the path (with this transition) is satisfiable.
  // If there is no solution, then the transition is not evaluated
  // and the path following this transition is pruned and the execution
  // moves to the next transition.
  // If the path is valid (a solution exists), then the execution moves to the
  // next transition.
  state.solver->push();
  for (size_t i = 0; i < match_conditions.size(); ++i) {
    ASSIGN_OR_RETURN(std::string next_state,
                     GetNextState(parse_state.transitions(i)));
    state.solver->push();
    state.solver->add(match_conditions[i]);
    auto prune = (state.solver->check() == z3::unsat);
    if (!prune) {
      RETURN_IF_ERROR(EvaluateParseStateDfs(
          program, parser, next_state, headers, z3_context, state, results));
    }
    state.solver->pop();
  }
  state.solver->pop();

  return absl::OkStatus();
}

}  // namespace

absl::StatusOr<z3::expr> GetErrorCodeExpression(const ir::P4Program &program,
                                                const std::string &error_name,
                                                z3::context &z3_context) {
  // Obtain the error code from the given `error_name`.
  auto err_it = program.errors().find(error_name);
  if (err_it == program.errors().end()) {
    return gutil::NotFoundErrorBuilder() << "Error not found: " << error_name;
  }
  unsigned int error_code = err_it->second.value();

  // Obtain the bitwidth of the `parser_error` field
  ASSIGN_OR_RETURN(unsigned int bitwidth,
                   util::GetFieldBitwidth(v1model::kParserErrorField, program));

  return z3_context.bv_val(error_code, bitwidth);
}

absl::StatusOr<SymbolicPerPacketState> EvaluateParsers(
    const ir::P4Program &program, const SymbolicPerPacketState &ingress_headers,
    z3::context &z3_context) {
  // Make sure there is exactly one parser in the P4-Symbolic IR.
  if (program.parsers_size() != 1) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Invalid number of parsers: " << program.parsers_size();
  }

  // Duplicate the symbolic headers for evaluating the parsers. This is to
  // preserve the symbolic state of the ingress packet before entering the
  // parsers.
  SymbolicPerPacketState parsed_headers = ingress_headers;
  const ir::Parser &parser = program.parsers().begin()->second;
  RETURN_IF_ERROR(EvaluateParseState(program, parser, parser.initial_state(),
                                     parsed_headers, z3_context,
                                     z3_context.bool_val(true)));
  return parsed_headers;
}

absl::Status EvaluateParsersDfs(
    const ir::P4Program &program, const SymbolicPerPacketState &headers,
    z3::context &z3_context, SolverState &state,
    packet_synthesizer::PacketSynthesisResults &results) {
  // Make sure there is exactly one parser in the P4-Symbolic IR.
  if (program.parsers_size() != 1) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Invalid number of parsers: " << program.parsers_size();
  }

  // Duplicate the symbolic headers for evaluating the parsers. This is to
  // preserve the symbolic state of the ingress packet before entering the
  // parsers.
  SymbolicPerPacketState parsed_headers = headers;
  const ir::Parser &parser = program.parsers().begin()->second;
  RETURN_IF_ERROR(EvaluateParseStateDfs(program, parser, parser.initial_state(),
                                        parsed_headers, z3_context, state,
                                        results));
  return absl::OkStatus();
}

}  // namespace p4_symbolic::symbolic::parser
