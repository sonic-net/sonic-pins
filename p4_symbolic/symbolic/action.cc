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

#include "p4_symbolic/symbolic/action.h"

#include <optional>
#include <string>
#include <vector>

#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "google/protobuf/repeated_ptr_field.h"
#include "gutil/collections.h"
#include "gutil/status.h"
#include "p4_pdpi/internal/ordered_map.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_symbolic/ir/ir.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/symbolic/context.h"
#include "p4_symbolic/symbolic/operators.h"
#include "p4_symbolic/symbolic/solver_state.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/symbolic/symbolic_table_entry.h"
#include "p4_symbolic/symbolic/util.h"
#include "p4_symbolic/symbolic/v1model.h"
#include "p4_symbolic/symbolic/values.h"
#include "p4_symbolic/z3_util.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {
namespace action {

absl::Status EvaluateStatement(const ir::Statement &statement,
                               SymbolicPerPacketState &headers,
                               SolverState &state, ActionContext *context,
                               const z3::expr &guard) {
  switch (statement.statement_case()) {
    case ir::Statement::kAssignment: {
      return EvaluateAssignmentStatement(statement.assignment(), headers,
                                         context, *state.context.z3_context,
                                         guard);
    }
    case ir::Statement::kClone: {
      // TODO: Add support for cloning.
      return headers.Set(std::string(kGotClonedPseudoField),
                         state.context.z3_context->bool_val(true), guard);
    }
    case ir::Statement::kRecirculate: {
      return headers.Set(std::string(kGotRecirculatedPseudoField),
                         state.context.z3_context->bool_val(true), guard);
    }
    case ir::Statement::kDrop: {
      z3::context &z3_context = *state.context.z3_context;
      absl::string_view standard_metadata =
          statement.drop().header().header_name();
      RETURN_IF_ERROR(headers.Set(standard_metadata, "egress_spec",
                                  v1model::EgressSpecDroppedValue(z3_context),
                                  guard));
      ASSIGN_OR_RETURN(int mcast_grp_width,
                       util::GetFieldBitwidth(standard_metadata, "mcast_grp",
                                              state.program));
      RETURN_IF_ERROR(headers.Set(standard_metadata, "mcast_grp",
                                  z3_context.bv_val(0, mcast_grp_width),
                                  guard));
      return absl::OkStatus();
    }
    case ir::Statement::kHash: {
      const ir::FieldValue &field = statement.hash().field();
      std::string field_name =
          absl::StrFormat("%s.%s", field.header_name(), field.field_name());
      if (!headers.ContainsKey(field_name)) {
        return absl::NotFoundError(absl::StrCat(
            "Action ", context->action_name, " hashes to unknown header field ",
            field.DebugString()));
      }
      ASSIGN_OR_RETURN(z3::expr old_value, headers.Get(field_name));
      ASSIGN_OR_RETURN(
          z3::expr free_variable,
          operators::FreeVariable(field_name, old_value.get_sort()));
      RETURN_IF_ERROR(headers.Set(field_name, free_variable, guard));
      return absl::OkStatus();
    }
    case ir::Statement::kExit: {
      // TODO: Implement. For now, just a no-op.
      LOG(ERROR) << "exit statement ignored since it is unsupported";
      return absl::OkStatus();
    }
    case ir::Statement::kHeaderAssignment: {
      return EvaluateHeaderAssignmentStatement(statement.header_assignment(),
                                               headers, state, guard);
    }
    case ir::Statement::STATEMENT_NOT_SET:
      break;
  }
  return absl::UnimplementedError(absl::StrCat(
      "Action ", context->action_name, " contains unsupported statement ",
      statement.DebugString()));
}

absl::Status EvaluateHeaderAssignmentStatement(
    const ir::HeaderAssignmentStatement &statement,
    SymbolicPerPacketState &headers, SolverState &state,
    const z3::expr &guard) {
  const std::string &left_header_name = statement.left().header_name();
  const std::string &right_header_name = statement.right().header_name();
  auto left_it = state.program.headers().find(left_header_name);
  auto right_it = state.program.headers().find(right_header_name);
  if (left_it == state.program.headers().end()) {
    return gutil::NotFoundErrorBuilder()
           << "Header '" << left_header_name << "' not found";
  }
  if (right_it == state.program.headers().end()) {
    return gutil::NotFoundErrorBuilder()
           << "Header '" << right_header_name << "' not found";
  }
  const ir::HeaderType &left_header = left_it->second;
  const ir::HeaderType &right_header = right_it->second;

  // Check the two headers have the same header type.
  if (left_header.id() != right_header.id()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Headers '" << left_header_name << "' and '" << right_header_name
           << "' have different header types. Header assignments expect the "
              "same header type.";
  }

  // Assign the value of each header field from right to left.
  for (const std::string &field_name : right_header.ordered_fields_list()) {
    // Check if the `field_name` also exists in the left header.
    if (!left_header.fields().contains(field_name)) {
      return gutil::InvalidArgumentErrorBuilder()
             << "Field '" << field_name << "' not found in header '"
             << left_header_name << "' during header assignment.";
    }

    ASSIGN_OR_RETURN(z3::expr right_value,
                     headers.Get(right_header_name, field_name));
    RETURN_IF_ERROR(
        headers.Set(left_header_name, field_name, right_value, guard));
  }

  // Assign the header validity from right to left.
  ASSIGN_OR_RETURN(z3::expr right_valid,
                   headers.Get(right_header_name, kValidPseudoField));
  RETURN_IF_ERROR(
      headers.Set(left_header_name, kValidPseudoField, right_valid, guard));

  return absl::OkStatus();
}

// Constructs a symbolic expression for the assignment value, and either
// constrains it in an enclosing assignment expression, or stores it in
// the action scope.
absl::Status EvaluateAssignmentStatement(
    const ir::AssignmentStatement &assignment, SymbolicPerPacketState &headers,
    ActionContext *context, z3::context &z3_context, const z3::expr &guard) {
  // Evaluate RValue recursively, evaluate LValue in this function, then
  // assign RValue to the scope at LValue.
  ASSIGN_OR_RETURN(z3::expr right, EvaluateRValue(assignment.right(), headers,
                                                  *context, z3_context));

  switch (assignment.left().lvalue_case()) {
    case ir::LValue::kFieldValue: {
      const ir::FieldValue &field_value = assignment.left().field_value();
      RETURN_IF_ERROR(headers.Set(field_value.header_name(),
                                  field_value.field_name(), right, guard));
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
                                        const SymbolicPerPacketState &headers,
                                        const ActionContext &context,
                                        z3::context &z3_context) {
  switch (rvalue.rvalue_case()) {
    case ir::RValue::kFieldValue:
      return EvaluateFieldValue(rvalue.field_value(), headers);

    case ir::RValue::kHexstrValue:
      return EvaluateHexStr(rvalue.hexstr_value(), z3_context);

    case ir::RValue::kBoolValue:
      return EvaluateBool(rvalue.bool_value(), z3_context);

    case ir::RValue::kStringValue:
      return EvaluateString(rvalue.string_value(), z3_context);

    case ir::RValue::kVariableValue:
      return EvaluateVariable(rvalue.variable_value(), context);

    case ir::RValue::kExpressionValue:
      return EvaluateRExpression(rvalue.expression_value(), headers, context,
                                 z3_context);

    default:
      return absl::UnimplementedError(
          absl::StrCat("Action ", context.action_name,
                       " contains unsupported RValue ", rvalue.DebugString()));
  }
}

// Extract the field symbolic value from the symbolic state.
absl::StatusOr<z3::expr> EvaluateFieldValue(
    const ir::FieldValue &field_value, const SymbolicPerPacketState &headers) {
  return headers.Get(field_value.header_name(), field_value.field_name());
}

// Turns bmv2 values to Symbolic Expressions.
absl::StatusOr<z3::expr> EvaluateHexStr(const ir::HexstrValue &hexstr,
                                        z3::context &z3_context) {
  if (hexstr.negative()) {
    return absl::UnimplementedError(
        "Negative hex string values are not supported!");
  }

  ASSIGN_OR_RETURN(pdpi::IrValue parsed_value,
                   values::ParseIrValue(hexstr.value()));
  return HexStringToZ3Bitvector(z3_context, hexstr.value());
}

absl::StatusOr<z3::expr> EvaluateBool(const ir::BoolValue &bool_value,
                                      z3::context &z3_context) {
  return z3_context.bool_val(bool_value.value());
}

absl::StatusOr<z3::expr> EvaluateString(const ir::StringValue &string_value,
                                        z3::context &z3_context) {
  return z3_context.string_val(string_value.value().c_str());
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
    const ir::RExpression &expr, const SymbolicPerPacketState &headers,
    const ActionContext &context, z3::context &z3_context) {
  switch (expr.expression_case()) {
    case ir::RExpression::kBinaryExpression: {
      ir::BinaryExpression bin_expr = expr.binary_expression();
      ASSIGN_OR_RETURN(z3::expr left, EvaluateRValue(bin_expr.left(), headers,
                                                     context, z3_context));
      ASSIGN_OR_RETURN(z3::expr right, EvaluateRValue(bin_expr.right(), headers,
                                                      context, z3_context));
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
      ASSIGN_OR_RETURN(
          z3::expr operand,
          EvaluateRValue(un_expr.operand(), headers, context, z3_context));
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
      ASSIGN_OR_RETURN(
          z3::expr condition,
          EvaluateRValue(tern_expr.condition(), headers, context, z3_context));
      ASSIGN_OR_RETURN(z3::expr left, EvaluateRValue(tern_expr.left(), headers,
                                                     context, z3_context));
      ASSIGN_OR_RETURN(
          z3::expr right,
          EvaluateRValue(tern_expr.right(), headers, context, z3_context));
      return operators::Ite(condition, left, right);
    }

    case ir::RExpression::kBuiltinExpression: {
      ir::BuiltinExpression builtin_expr = expr.builtin_expression();
      // Evaluate arguments.
      std::vector<z3::expr> args;
      for (const auto &arg_value : builtin_expr.arguments()) {
        ASSIGN_OR_RETURN(z3::expr arg, EvaluateRValue(arg_value, headers,
                                                      context, z3_context));
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

absl::Status EvaluateConcreteAction(
    const ir::Action &action,
    const google::protobuf::RepeatedPtrField<
        pdpi::IrActionInvocation::IrActionParam> &args,
    SolverState &state, SymbolicPerPacketState &headers,
    const z3::expr &guard) {
  // Construct this action's context.
  ActionContext context;
  context.action_name = action.action_definition().preamble().name();

  VLOG(1) << "evaluating action '" << context.action_name << "'";

  // Add action parameters to scope.
  const auto &parameters = action.action_definition().params_by_name();
  if (static_cast<int>(parameters.size()) != args.size()) {
    return absl::InvalidArgumentError(
        absl::StrCat("Action ", action.action_definition().preamble().name(),
                     " called with incompatible number of parameters"));
  }

  // Find each parameter value in arguments by argument name. We should not
  // rely on argument order matching param definition order, because the P4
  // runtime spec does not enforce this assumption in implementations, and
  // furthermore the spec explicitly states that read entries do not have to
  // preserve the order of repeated fields in written entries.
  for (const auto &arg : args) {
    absl::string_view arg_name = arg.name();
    ASSIGN_OR_RETURN(const pdpi::IrActionDefinition::IrActionParamDefinition
                         *param_definition,
                     gutil::FindPtrOrStatus(parameters, arg_name));
    ASSIGN_OR_RETURN(
        z3::expr parameter_value,
        values::FormatP4RTValue(arg.value(), /*field_name=*/std::nullopt,
                                param_definition->param().type_name().name(),
                                param_definition->param().bitwidth(),
                                *state.context.z3_context, state.translator));
    context.scope.insert({param_definition->param().name(), parameter_value});
  }

  // Iterate over the body in order, and evaluate each statement.
  for (const auto &statement : action.action_implementation().action_body()) {
    RETURN_IF_ERROR(
        EvaluateStatement(statement, headers, state, &context, guard));
  }

  return absl::OkStatus();
}

absl::Status EvaluateSymbolicAction(const ir::Action &action,
                                    const ir::SymbolicTableEntry &entry,
                                    SolverState &state,
                                    SymbolicPerPacketState &headers,
                                    const z3::expr &guard) {
  // At this point the table must exists because otherwise an absl error would
  // have been returned upon initializing the table entries, so no exception
  // will be thrown.
  const ir::Table &table = state.program.tables().at(ir::GetTableName(entry));

  // Construct the action's context.
  ActionContext context;
  context.action_name = action.action_definition().preamble().name();

  // Add the symbolic action parameters to scope.
  for (const auto &[param_name, _] :
       Ordered(action.action_definition().params_by_name())) {
    ASSIGN_OR_RETURN(z3::expr param_value, GetSymbolicActionParameter(
                                               entry, param_name, action, table,
                                               *state.context.z3_context));
    context.scope.insert({param_name, param_value});
  }

  // Iterate over the body in order, and evaluate each statement.
  for (const auto &statement : action.action_implementation().action_body()) {
    RETURN_IF_ERROR(
        EvaluateStatement(statement, headers, state, &context, guard));
  }

  return absl::OkStatus();
}

}  // namespace action
}  // namespace symbolic
}  // namespace p4_symbolic
