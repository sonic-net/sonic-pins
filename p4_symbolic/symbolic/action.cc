// Copyright 2020 Google LLC
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

#include "p4_symbolic/symbolic/action.h"

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "p4_symbolic/symbolic/operators.h"

namespace p4_symbolic {
namespace symbolic {
namespace action {

absl::Status EvaluateStatement(const ir::Statement &statement,
                               SymbolicPerPacketState *state,
                               ActionContext *context, const z3::expr &guard) {
  switch (statement.statement_case()) {
    case ir::Statement::kAssignment: {
      return EvaluateAssignmentStatement(statement.assignment(), state, context,
                                         guard);
    }
    case ir::Statement::kDrop: {
      // https://github.com/p4lang/p4c/blob/7ee76d16da63883c5092ab0c28321f04c2646759/p4include/v1model.p4#L435
      const std::string &header_name = statement.drop().header().header_name();
      z3::expr dropped_value = Z3Context().bv_val(DROPPED_EGRESS_SPEC_VALUE,
                                                  DROPPED_EGRESS_SPEC_LENGTH);
      RETURN_IF_ERROR(state->Set(absl::StrFormat("%s.egress_spec", header_name),
                                 dropped_value, guard));
      RETURN_IF_ERROR(state->Set(absl::StrFormat("%s.mcast_grp", header_name),
                                 Z3Context().bv_val(0, 1), guard));
      return absl::OkStatus();
    }
    case ir::Statement::kClone: {
      // No-op.
      return absl::OkStatus();
    }
    case ir::Statement::kHash: {
      const ir::FieldValue &field = statement.hash().field();
      std::string field_name =
          absl::StrFormat("%s.%s", field.header_name(), field.field_name());
      if (!state->ContainsKey(field_name)) {
        return absl::UnimplementedError(absl::StrCat(
            "Action ", context->action_name, " hashes to unknown header field ",
            field.DebugString()));
      }
      ASSIGN_OR_RETURN(z3::expr old_value, state->Get(field_name));
      ASSIGN_OR_RETURN(
          z3::expr free_variable,
          operators::FreeVariable(field_name, old_value.get_sort()));
      RETURN_IF_ERROR(state->Set(field_name, free_variable, guard));
      return absl::OkStatus();
    }
    default:
      return absl::UnimplementedError(absl::StrCat(
          "Action ", context->action_name, " contains unsupported statement ",
          statement.DebugString()));
  }
}

// Constructs a symbolic expression for the assignment value, and either
// constrains it in an enclosing assignment expression, or stores it in
// the action scope.
absl::Status EvaluateAssignmentStatement(
    const ir::AssignmentStatement &assignment, SymbolicPerPacketState *state,
    ActionContext *context, const z3::expr &guard) {
  // Evaluate RValue recursively, evaluate LValue in this function, then
  // assign RValue to the scope at LValue.
  ASSIGN_OR_RETURN(z3::expr right,
                   EvaluateRValue(assignment.right(), *state, *context));

  switch (assignment.left().lvalue_case()) {
    case ir::LValue::kFieldValue: {
      const ir::FieldValue &field_value = assignment.left().field_value();
      std::string field_name = absl::StrFormat(
          "%s.%s", field_value.header_name(), field_value.field_name());
      if (!state->ContainsKey(field_name)) {
        return absl::UnimplementedError(absl::StrCat(
            "Action ", context->action_name, " refers to unknown header field ",
            field_value.DebugString()));
      }
      RETURN_IF_ERROR(state->Set(field_name, right, guard));
      return absl::OkStatus();
    }

    case ir::LValue::kVariableValue: {
      const std::string &variable = assignment.left().variable_value().name();
      context->scope.insert_or_assign(variable, right);
      return absl::OkStatus();
    }

    default:
      return absl::UnimplementedError(absl::StrCat(
          "Action ", context->action_name, " contains unsupported LValue ",
          assignment.left().DebugString()));
  }
}

// Constructs a symbolic expression corresponding to this value, according
// to its type.
absl::StatusOr<z3::expr> EvaluateRValue(const ir::RValue &rvalue,
                                        const SymbolicPerPacketState &state,
                                        const ActionContext &context) {
  switch (rvalue.rvalue_case()) {
    case ir::RValue::kFieldValue:
      return EvaluateFieldValue(rvalue.field_value(), state, context);

    case ir::RValue::kHexstrValue:
      return EvaluateHexStr(rvalue.hexstr_value());

    case ir::RValue::kBoolValue:
      return EvaluateBool(rvalue.bool_value());

    case ir::RValue::kStringValue:
      return EvaluateString(rvalue.string_value());

    case ir::RValue::kVariableValue:
      return EvaluateVariable(rvalue.variable_value(), context);

    case ir::RValue::kExpressionValue:
      return EvaluateRExpression(rvalue.expression_value(), state, context);

    default:
      return absl::UnimplementedError(
          absl::StrCat("Action ", context.action_name,
                       " contains unsupported RValue ", rvalue.DebugString()));
  }
}

// Extract the field symbolic value from the symbolic state.
absl::StatusOr<z3::expr> EvaluateFieldValue(const ir::FieldValue &field_value,
                                            const SymbolicPerPacketState &state,
                                            const ActionContext &context) {
  std::string field_name = absl::StrFormat("%s.%s", field_value.header_name(),
                                           field_value.field_name());
  if (!state.ContainsKey(field_name)) {
    return absl::UnimplementedError(absl::StrCat(
        "Action ", context.action_name, " refers to unknown header field ",
        field_value.DebugString()));
  }

  return state.Get(field_name);
}

// Turns bmv2 values to Symbolic Expressions.
absl::StatusOr<z3::expr> EvaluateHexStr(const ir::HexstrValue &hexstr) {
  if (hexstr.negative()) {
    return absl::UnimplementedError(
        "Negative hex string values are not supported!");
  }

  ASSIGN_OR_RETURN(pdpi::IrValue parsed_value,
                   values::ParseIrValue(hexstr.value()));
  return values::FormatBmv2Value(parsed_value);
}

absl::StatusOr<z3::expr> EvaluateBool(const ir::BoolValue &bool_value) {
  return Z3Context().bool_val(bool_value.value());
}

absl::StatusOr<z3::expr> EvaluateString(const ir::StringValue &string_value) {
  return Z3Context().string_val(string_value.value().c_str());
}

// Looks up the symbolic value of the variable in the action scope.
absl::StatusOr<z3::expr> EvaluateVariable(const ir::Variable &variable,
                                          const ActionContext &context) {
  std::string variable_name = variable.name();
  if (context.scope.count(variable_name) != 1) {
    return absl::InvalidArgumentError(
        absl::StrCat("Action ", context.action_name,
                     " refers to undefined variable ", variable_name));
  }

  return context.scope.at(variable_name);
}

// Recursively evaluate expressions.
absl::StatusOr<z3::expr> EvaluateRExpression(
    const ir::RExpression &expr, const SymbolicPerPacketState &state,
    const ActionContext &context) {
  switch (expr.expression_case()) {
    case ir::RExpression::kBinaryExpression: {
      ir::BinaryExpression bin_expr = expr.binary_expression();
      ASSIGN_OR_RETURN(z3::expr left,
                       EvaluateRValue(bin_expr.left(), state, context));
      ASSIGN_OR_RETURN(z3::expr right,
                       EvaluateRValue(bin_expr.right(), state, context));
      switch (bin_expr.operation()) {
        case ir::BinaryExpression::PLUS:
          return operators::Plus(left, right);
        case ir::BinaryExpression::MINUS:
          return operators::Minus(left, right);
        case ir::BinaryExpression::TIMES:
          return operators::Times(left, right);
        case ir::BinaryExpression::LEFT_SHIT:
          return operators::LShift(left, right);
        case ir::BinaryExpression::RIGHT_SHIFT:
          return operators::RShift(left, right);
        case ir::BinaryExpression::EQUALS:
          return operators::Eq(left, right);
        case ir::BinaryExpression::NOT_EQUALS:
          return operators::Neq(left, right);
        case ir::BinaryExpression::GREATER:
          return operators::Gt(left, right);
        case ir::BinaryExpression::GREATER_EQUALS:
          return operators::Gte(left, right);
        case ir::BinaryExpression::LESS:
          return operators::Lt(left, right);
        case ir::BinaryExpression::LESS_EQUALS:
          return operators::Lte(left, right);
        case ir::BinaryExpression::AND:
          return operators::And(left, right);
        case ir::BinaryExpression::OR:
          return operators::Or(left, right);
        case ir::BinaryExpression::BIT_AND:
          return operators::BitAnd(left, right);
        case ir::BinaryExpression::BIT_OR:
          return operators::BitOr(left, right);
        case ir::BinaryExpression::BIT_XOR:
          return operators::BitXor(left, right);
        default:
          return absl::UnimplementedError(
              absl::StrCat("Action ", context.action_name,
                           " contains unsupported BinaryExpression ",
                           bin_expr.DebugString()));
      }
      break;
    }

    case ir::RExpression::kUnaryExpression: {
      ir::UnaryExpression un_expr = expr.unary_expression();
      ASSIGN_OR_RETURN(z3::expr operand,
                       EvaluateRValue(un_expr.operand(), state, context));
      switch (un_expr.operation()) {
        case ir::UnaryExpression::NOT:
          return operators::Not(operand);
        case ir::UnaryExpression::BIT_NEGATION:
          return operators::BitNeg(operand);
        default:
          return absl::UnimplementedError(absl::StrCat(
              "Action ", context.action_name,
              " contains unsupported UnaryExpression ", un_expr.DebugString()));
      }
      break;
    }

    case ir::RExpression::kTernaryExpression: {
      ir::TernaryExpression tern_expr = expr.ternary_expression();
      ASSIGN_OR_RETURN(z3::expr condition,
                       EvaluateRValue(tern_expr.condition(), state, context));
      ASSIGN_OR_RETURN(z3::expr left,
                       EvaluateRValue(tern_expr.left(), state, context));
      ASSIGN_OR_RETURN(z3::expr right,
                       EvaluateRValue(tern_expr.right(), state, context));
      return operators::Ite(condition, left, right);
    }

    case ir::RExpression::kBuiltinExpression: {
      ir::BuiltinExpression builtin_expr = expr.builtin_expression();
      // Evaluate arguments.
      std::vector<z3::expr> args;
      for (const auto &arg_value : builtin_expr.arguments()) {
        ASSIGN_OR_RETURN(z3::expr arg,
                         EvaluateRValue(arg_value, state, context));
        args.push_back(arg);
      }

      switch (builtin_expr.function()) {
        case ir::BuiltinExpression::DATA_TO_BOOL:
          return operators::ToBoolSort(args.at(0));
        case ir::BuiltinExpression::BOOL_TO_DATA:
          return operators::ToBitVectorSort(args.at(0), 1);
        default:
          return absl::UnimplementedError(
              absl::StrCat("Action ", context.action_name,
                           " contains unsupported BuiltinExpression ",
                           builtin_expr.DebugString()));
      }
    }

    default:
      return absl::UnimplementedError(absl::StrCat(
          "Action ", context.action_name, " contains unsupported RExpression ",
          expr.DebugString()));
  }
}

// Symbolically evaluates the given action on the given symbolic parameters.
// This produces a symbolic expression on the symbolic parameters that is
// semantically equivalent to the behavior of the action on its concrete
// parameters.
absl::Status EvaluateAction(const ir::Action &action,
                            const google::protobuf::RepeatedPtrField<
                                pdpi::IrActionInvocation::IrActionParam> &args,
                            SymbolicPerPacketState *state,
                            values::P4RuntimeTranslator *translator,
                            const z3::expr &guard) {
  // Construct this action's context.
  ActionContext context;
  context.action_name = action.action_definition().preamble().name();

  // Add action parameters to scope.
  const auto &parameters = action.action_definition().params_by_id();
  if (static_cast<int>(parameters.size()) != args.size()) {
    return absl::InvalidArgumentError(
        absl::StrCat("Action ", action.action_definition().preamble().name(),
                     " called with incompatible number of parameters"));
  }

  // Find each parameter value in argument by parameter's name.
  for (size_t i = 1; i <= parameters.size(); i++) {
    // parameter id is the same as its index + 1.
    const pdpi::IrActionDefinition::IrActionParamDefinition &parameter =
        parameters.at(i);
    const std::string &parameter_name = parameter.param().name();
    const std::string &parameter_type_name =
        parameter.param().type_name().name();
    ASSIGN_OR_RETURN(
        z3::expr parameter_value,
        values::FormatP4RTValue("", parameter_type_name, args.at(i - 1).value(),
                                translator));
    context.scope.insert({parameter_name, parameter_value});
  }

  // Iterate over the body in order, and evaluate each statement.
  for (const auto &statement : action.action_implementation().action_body()) {
    RETURN_IF_ERROR(EvaluateStatement(statement, state, &context, guard));
  }

  return absl::OkStatus();
}

}  // namespace action
}  // namespace symbolic
}  // namespace p4_symbolic
