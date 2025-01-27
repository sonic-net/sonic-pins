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

#include "p4_symbolic/ir/ir.h"

#include <memory>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "absl/strings/strip.h"
#include "google/protobuf/repeated_ptr_field.h"
#include "google/protobuf/struct.pb.h"
#include "gutil/gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/internal/ordered_map.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/names.h"
#include "p4_symbolic/bmv2/bmv2.pb.h"
#include "p4_symbolic/ir/cfg.h"
#include "p4_symbolic/ir/ir.pb.h"

namespace p4_symbolic::ir {

namespace {

// Turns BMv2-style names of control nodes to P4-Symbolic's IR-style names.
std::string Bmv2ToIrControlName(const std::string &control_name) {
  return control_name.empty() ? EndOfPipeline() : control_name;
}

// Turns BMv2-style names of parse states to P4-Symbolic's IR-style names.
std::string Bmv2ToIrParseStateName(const std::string &state_name) {
  return state_name.empty() ? EndOfParser() : state_name;
}

// Forward declaration to enable mutual recursion with (sub) expression parsing
// functions, e.g. ExtractBinaryExpression, ExtractUnaryExpression, etc.
absl::StatusOr<RValue> ExtractRValue(const google::protobuf::Value &bmv2_value,
                                     const std::vector<std::string> &variables);

// Translate a string statement op to its respective enum value.
absl::StatusOr<bmv2::StatementOp> StatementOpToEnum(const std::string &op) {
  static const std::unordered_map<std::string, bmv2::StatementOp> op_table = {
      {"assign", bmv2::StatementOp::assign},
      {"mark_to_drop", bmv2::StatementOp::mark_to_drop},
      {"clone_ingress_pkt_to_egress",  // clone3(...)
       bmv2::StatementOp::clone_ingress_pkt_to_egress},
      {"modify_field_with_hash_based_offset",  // hash(...)
       bmv2::StatementOp::modify_field_with_hash_based_offset},
      {"add_header",  // hdr.SetValid()
       bmv2::StatementOp::add_header},
      {"remove_header",  // hdr.SetInvalid()
       bmv2::StatementOp::remove_header},
      {"assign_header", bmv2::StatementOp::assign_header},
      {"exit", bmv2::StatementOp::exit},
      {"recirculate", bmv2::StatementOp::recirculate},
  };

  if (op_table.count(op) != 1) {
    return absl::UnimplementedError(
        absl::StrCat("Unsupported statement op ", op));
  }
  return op_table.at(op);
}

// Translate a string expression type to its respective enum value.
absl::StatusOr<bmv2::ExpressionType> ExpressionTypeToEnum(
    const std::string &type) {
  static const std::unordered_map<std::string, bmv2::ExpressionType>
      type_table = {{"header", bmv2::ExpressionType::header},
                    {"field", bmv2::ExpressionType::field},
                    {"runtime_data", bmv2::ExpressionType::runtime_data},
                    // "local" is the same as "runtime_data", but while
                    // runtime_data is used in parameters, local is used
                    // in expressions.
                    {"local", bmv2::ExpressionType::runtime_data},
                    {"hexstr", bmv2::ExpressionType::hexstr_},
                    {"bool", bmv2::ExpressionType::bool_},
                    {"string", bmv2::ExpressionType::string_},
                    {"expression", bmv2::ExpressionType::expression}};

  if (type_table.count(type) != 1) {
    return absl::UnimplementedError(
        absl::StrCat("Unsupported expression type ", type));
  }
  return type_table.at(type);
}

// Translate a string expression operation ("op") to its respective enum value.
absl::StatusOr<RExpression::ExpressionCase> ExpressionOpToCase(
    const std::string &op) {
  static const std::unordered_map<std::string, RExpression::ExpressionCase>
      table = {// Binary expressions.
               {"+", RExpression::ExpressionCase::kBinaryExpression},
               {"-", RExpression::ExpressionCase::kBinaryExpression},
               {"*", RExpression::ExpressionCase::kBinaryExpression},
               {"<<", RExpression::ExpressionCase::kBinaryExpression},
               {">>", RExpression::ExpressionCase::kBinaryExpression},
               {"==", RExpression::ExpressionCase::kBinaryExpression},
               {"!=", RExpression::ExpressionCase::kBinaryExpression},
               {">", RExpression::ExpressionCase::kBinaryExpression},
               {">=", RExpression::ExpressionCase::kBinaryExpression},
               {"<", RExpression::ExpressionCase::kBinaryExpression},
               {"<=", RExpression::ExpressionCase::kBinaryExpression},
               {"and", RExpression::ExpressionCase::kBinaryExpression},
               {"or", RExpression::ExpressionCase::kBinaryExpression},
               {"&", RExpression::ExpressionCase::kBinaryExpression},
               {"|", RExpression::ExpressionCase::kBinaryExpression},
               {"^", RExpression::ExpressionCase::kBinaryExpression},
               // Unary.
               {"~", RExpression::ExpressionCase::kUnaryExpression},
               {"not", RExpression::ExpressionCase::kUnaryExpression},
               // Ternary.
               {"?", RExpression::ExpressionCase::kTernaryExpression},
               // Builtin functions.
               {"b2d", RExpression::ExpressionCase::kBuiltinExpression},
               {"d2b", RExpression::ExpressionCase::kBuiltinExpression}};

  if (table.count(op) != 1) {
    return absl::UnimplementedError(
        absl::StrCat("Unsupported expression op ", op));
  }

  return table.at(op);
}

// Extracting source code information.
absl::StatusOr<bmv2::SourceLocation> ExtractSourceLocation(
    google::protobuf::Value unparsed_source_location) {
  if (unparsed_source_location.kind_case() !=
      google::protobuf::Value::kStructValue) {
    return absl::InvalidArgumentError(
        absl::StrCat("Source Location is expected to be a struct, found ",
                     unparsed_source_location.DebugString()));
  }

  const auto &fields = unparsed_source_location.struct_value().fields();
  if (fields.count("filename") != 1 || fields.count("line") != 1 ||
      fields.count("column") != 1 || fields.count("source_fragment") != 1) {
    return absl::InvalidArgumentError(
        absl::StrCat("Source Location is expected to contain 'filename', "
                     "'line', 'colmn', and 'source_fragment, found ",
                     unparsed_source_location.DebugString()));
  }

  bmv2::SourceLocation output;
  output.set_filename(fields.at("filename").string_value());
  output.set_line(fields.at("line").number_value());
  output.set_column(fields.at("column").number_value());
  output.set_source_fragment(fields.at("source_fragment").string_value());
  return output;
}

// Parsing and validating Headers.
absl::Status ValidateHeaderTypeFields(const google::protobuf::ListValue &list) {
  // Size must be 3.
  int size = list.values_size();
  if (size != 3) {
    return absl::InvalidArgumentError(absl::StrCat(
        "Header field should contain 3 elements, found ", list.DebugString()));
  }

  // Array must contain [string, int, bool] in that order.
  if (list.values(0).kind_case() != google::protobuf::Value::kStringValue ||
      list.values(1).kind_case() != google::protobuf::Value::kNumberValue ||
      list.values(2).kind_case() != google::protobuf::Value::kBoolValue) {
    return absl::InvalidArgumentError(
        absl::StrCat("Header field should be [string, int, bool], found ",
                     list.DebugString()));
  }

  return absl::OkStatus();
}

absl::StatusOr<HeaderType> ExtractHeaderType(const bmv2::HeaderType &header) {
  HeaderType output;
  output.set_name(header.name());
  output.set_id(header.id());
  for (const google::protobuf::ListValue &unparsed_field : header.fields()) {
    RETURN_IF_ERROR(ValidateHeaderTypeFields(unparsed_field));

    HeaderField &field =
        (*output.mutable_fields())[unparsed_field.values(0).string_value()];
    field.set_name(unparsed_field.values(0).string_value());
    field.set_bitwidth(unparsed_field.values(1).number_value());
    field.set_signed_(unparsed_field.values(2).bool_value());
    output.add_ordered_fields_list(unparsed_field.values(0).string_value());
  }

  // TODO: We should remove this if-clause when GPINS' last tested
  // version is updated with the complete ICMP definition.
  if (header.name() == "icmp_t" && header.fields_size() < 4) {
    constexpr absl::string_view kIcmpRestOfHeaderFieldName = "rest_of_header";
    constexpr int kIcmpRestOfHeaderBitwidth = 32;
    constexpr bool kIcmpRestOfHeaderSigned = false;
    RET_CHECK(!output.fields().contains(kIcmpRestOfHeaderFieldName));
    LOG(WARNING) << "Fixing incomplete definition of the ICMP header, missing '"
                 << kIcmpRestOfHeaderFieldName << "'";
    HeaderField &field = (*output.mutable_fields())[kIcmpRestOfHeaderFieldName];
    field.set_name(kIcmpRestOfHeaderFieldName);
    field.set_bitwidth(kIcmpRestOfHeaderBitwidth);
    field.set_signed_(kIcmpRestOfHeaderSigned);
    output.add_ordered_fields_list(kIcmpRestOfHeaderFieldName);
  }

  return output;
}

// Functions for translating RExpressions (arithmetic, relational, etc).
absl::StatusOr<UnaryExpression> ExtractUnaryExpression(
    const google::protobuf::Struct &bmv2_expression,
    const std::vector<std::string> &variables) {
  static const std::unordered_map<std::string, UnaryExpression::Operation>
      unary_op_table = {{"~", UnaryExpression::BIT_NEGATION},
                        {"not", UnaryExpression::NOT}};

  const google::protobuf::Value &right = bmv2_expression.fields().at("right");
  const std::string &operation =
      bmv2_expression.fields().at("op").string_value();

  UnaryExpression output;
  // No need for error checking, operation must be legal since we got here.
  output.set_operation(unary_op_table.at(operation));
  ASSIGN_OR_RETURN(*output.mutable_operand(), ExtractRValue(right, variables));
  return output;
}

absl::StatusOr<BinaryExpression> ExtractBinaryExpression(
    const google::protobuf::Struct &bmv2_expression,
    const std::vector<std::string> &variables) {
  static const std::unordered_map<std::string, BinaryExpression::Operation>
      binary_op_table = {{"+", BinaryExpression::PLUS},
                         {"-", BinaryExpression::MINUS},
                         {"*", BinaryExpression::TIMES},
                         {"<<", BinaryExpression::LEFT_SHIT},
                         {">>", BinaryExpression::RIGHT_SHIFT},
                         {"==", BinaryExpression::EQUALS},
                         {"!=", BinaryExpression::NOT_EQUALS},
                         {">", BinaryExpression::GREATER},
                         {">=", BinaryExpression::GREATER_EQUALS},
                         {"<", BinaryExpression::LESS},
                         {"<=", BinaryExpression::LESS_EQUALS},
                         {"and", BinaryExpression::AND},
                         {"or", BinaryExpression::OR},
                         {"&", BinaryExpression::BIT_AND},
                         {"|", BinaryExpression::BIT_OR},
                         {"^", BinaryExpression::BIT_XOR}};

  if (bmv2_expression.fields().count("left") != 1) {
    return absl::InvalidArgumentError(
        absl::StrCat("BinaryExpression must contain 'left', found ",
                     bmv2_expression.DebugString()));
  }

  const google::protobuf::Value &left = bmv2_expression.fields().at("left");
  const google::protobuf::Value &right = bmv2_expression.fields().at("right");
  const std::string &operation =
      bmv2_expression.fields().at("op").string_value();

  BinaryExpression output;
  // No need for error checking, operation must be legal since we got here.
  output.set_operation(binary_op_table.at(operation));
  ASSIGN_OR_RETURN(*output.mutable_left(), ExtractRValue(left, variables));
  ASSIGN_OR_RETURN(*output.mutable_right(), ExtractRValue(right, variables));
  return output;
}

absl::StatusOr<TernaryExpression> ExtractTernaryExpression(
    const google::protobuf::Struct &bmv2_expression,
    const std::vector<std::string> &variables) {
  if (bmv2_expression.fields().count("left") != 1 ||
      (bmv2_expression.fields().count("cond") != 1 &&
       bmv2_expression.fields().count("condition") != 1)) {
    return absl::InvalidArgumentError(absl::StrCat(
        "TernaryExpression must contain 'left', and 'condition'/'cond' ",
        bmv2_expression.DebugString()));
  }

  const google::protobuf::Value &condition =
      bmv2_expression.fields().contains("condition")
          ? bmv2_expression.fields().at("condition")
          : bmv2_expression.fields().at("cond");
  const google::protobuf::Value &left = bmv2_expression.fields().at("left");
  const google::protobuf::Value &right = bmv2_expression.fields().at("right");

  TernaryExpression output;
  ASSIGN_OR_RETURN(*output.mutable_condition(),
                   ExtractRValue(condition, variables));
  ASSIGN_OR_RETURN(*output.mutable_left(), ExtractRValue(left, variables));
  ASSIGN_OR_RETURN(*output.mutable_right(), ExtractRValue(right, variables));
  return output;
}

absl::StatusOr<BuiltinExpression> ExtractBuiltinExpression(
    const google::protobuf::Struct &bmv2_expression,
    const std::vector<std::string> &variables) {
  static const std::unordered_map<std::string, BuiltinExpression::Function>
      builtin_table = {{"b2d", BuiltinExpression::BOOL_TO_DATA},
                       {"d2b", BuiltinExpression::DATA_TO_BOOL}};

  BuiltinExpression output;
  output.set_function(
      builtin_table.at(bmv2_expression.fields().at("op").string_value()));

  // Left argument comes first if it exists.
  if (bmv2_expression.fields().count("left") == 1 &&
      bmv2_expression.fields().at("left").kind_case() !=
          google::protobuf::Value::kNullValue) {
    const google::protobuf::Value &left = bmv2_expression.fields().at("left");
    ASSIGN_OR_RETURN(*output.add_arguments(), ExtractRValue(left, variables));
  }

  // There is always at least one argument.
  const google::protobuf::Value &right = bmv2_expression.fields().at("right");
  ASSIGN_OR_RETURN(*output.add_arguments(), ExtractRValue(right, variables));
  return output;
}

absl::StatusOr<RExpression> ExtractRExpression(
    const google::protobuf::Struct &bmv2_expression,
    const std::vector<std::string> &variables) {
  // An expression in the BMv2 format may have its value be a single other
  // expression, whose value may also be another single expression, etc., until
  // the actual value of the expression is reached. This is analogous to having
  // an expression wrapped in multiple layers of parentheses. This conditional
  // recursively navigates to the inner most expression.
  if (!bmv2_expression.fields().contains("op") &&
      bmv2_expression.fields().contains("type") &&
      bmv2_expression.fields().at("type").has_string_value() &&
      bmv2_expression.fields().at("type").string_value() == "expression" &&
      bmv2_expression.fields().contains("value") &&
      bmv2_expression.fields().at("value").has_struct_value()) {
    return ExtractRExpression(
        bmv2_expression.fields().at("value").struct_value(), variables);
  }

  // Integrity check.
  if (!bmv2_expression.fields().contains("op") ||
      !bmv2_expression.fields().contains("right")) {
    return absl::InvalidArgumentError(
        absl::StrCat("RExpression must contain 'op' and 'right', found ",
                     bmv2_expression.DebugString()));
  }

  RExpression output;
  const std::string &operation =
      bmv2_expression.fields().at("op").string_value();
  ASSIGN_OR_RETURN(RExpression::ExpressionCase expression_case,
                   ExpressionOpToCase(operation));

  // Parse expression by case.
  switch (expression_case) {
    case RExpression::ExpressionCase::kUnaryExpression: {
      ASSIGN_OR_RETURN(*output.mutable_unary_expression(),
                       ExtractUnaryExpression(bmv2_expression, variables));
      return output;
    }
    case RExpression::ExpressionCase::kBinaryExpression: {
      ASSIGN_OR_RETURN(*output.mutable_binary_expression(),
                       ExtractBinaryExpression(bmv2_expression, variables));
      return output;
    }
    case RExpression::ExpressionCase::kTernaryExpression: {
      ASSIGN_OR_RETURN(*output.mutable_ternary_expression(),
                       ExtractTernaryExpression(bmv2_expression, variables));
      return output;
    }
    case RExpression::ExpressionCase::kBuiltinExpression: {
      ASSIGN_OR_RETURN(*output.mutable_builtin_expression(),
                       ExtractBuiltinExpression(bmv2_expression, variables));
      return output;
    }
    default:
      return absl::UnimplementedError(absl::StrCat(
          "Unsupported expression op ", bmv2_expression.DebugString()));
  }
}

// Extracts field value from BMv2 protobuf fields.
absl::StatusOr<FieldValue> ExtractFieldValue(
    const google::protobuf::ListValue &bmv2_field_value) {
  FieldValue output;

  if (bmv2_field_value.values_size() != 2 ||
      !bmv2_field_value.values(0).has_string_value() ||
      !bmv2_field_value.values(1).has_string_value()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Field value must contain 2 strings. Found: "
           << bmv2_field_value.DebugString();
  }

  output.set_header_name(bmv2_field_value.values(0).string_value());
  output.set_field_name(bmv2_field_value.values(1).string_value());
  return output;
}

// Extracts hex string value from BMv2 protobuf fields.
HexstrValue ExtractHexstrValue(const std::string &bmv2_hexstr) {
  HexstrValue output;
  if (absl::StartsWith(bmv2_hexstr, "-")) {
    output.set_value(std::string(absl::StripPrefix(bmv2_hexstr, "-")));
    output.set_negative(true);
  } else {
    output.set_value(bmv2_hexstr);
    output.set_negative(false);
  }
  return output;
}

// Extracts lookahead value from BMv2 protobuf fields.
absl::StatusOr<LookaheadValue> ExtractLookaheadValue(
    const google::protobuf::ListValue &bmv2_lookahead) {
  LookaheadValue output;

  if (bmv2_lookahead.values_size() != 2 ||
      !bmv2_lookahead.values(0).has_number_value() ||
      !bmv2_lookahead.values(1).has_number_value()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Lookahead value must contain 2 numbers. Found: "
           << bmv2_lookahead.DebugString();
  }

  output.set_offset(bmv2_lookahead.values(0).number_value());
  output.set_bitwidth(bmv2_lookahead.values(1).number_value());
  return output;
}

// Functions for translating values.
absl::StatusOr<LValue> ExtractLValue(
    const google::protobuf::Value &bmv2_value,
    const std::vector<std::string> &variables) {
  LValue output;
  // Either a field value or a variable.
  if (bmv2_value.kind_case() != google::protobuf::Value::kStructValue ||
      bmv2_value.struct_value().fields().count("type") != 1 ||
      bmv2_value.struct_value().fields().count("value") != 1) {
    return absl::InvalidArgumentError(
        absl::StrCat("Lvalue must contain 'type' and 'value', found ",
                     bmv2_value.DebugString()));
  }

  const google::protobuf::Struct &struct_value = bmv2_value.struct_value();
  const std::string &type = struct_value.fields().at("type").string_value();
  const google::protobuf::Value &value = struct_value.fields().at("value");

  ASSIGN_OR_RETURN(bmv2::ExpressionType type_case, ExpressionTypeToEnum(type));
  switch (type_case) {
    case bmv2::ExpressionType::field: {
      ASSIGN_OR_RETURN(*output.mutable_field_value(),
                       ExtractFieldValue(value.list_value()));
      return output;
    }
    case bmv2::ExpressionType::runtime_data: {
      int variable_index = value.number_value();
      Variable *variable = output.mutable_variable_value();
      variable->set_name(variables[variable_index]);
      return output;
    }
    default:
      return absl::UnimplementedError(
          absl::StrCat("Unsupported lvalue ", bmv2_value.DebugString()));
  }
}

absl::StatusOr<RValue> ExtractRValue(
    const google::protobuf::Value &bmv2_value,
    const std::vector<std::string> &variables) {
  RValue output;
  if (bmv2_value.kind_case() != google::protobuf::Value::kStructValue ||
      bmv2_value.struct_value().fields().count("type") != 1 ||
      bmv2_value.struct_value().fields().count("value") != 1) {
    return absl::InvalidArgumentError(
        absl::StrCat("Rvalue must contain 'type' and 'value', found ",
                     bmv2_value.DebugString()));
  }

  const google::protobuf::Struct &struct_value = bmv2_value.struct_value();
  const std::string &type = struct_value.fields().at("type").string_value();
  const google::protobuf::Value &value = struct_value.fields().at("value");

  ASSIGN_OR_RETURN(bmv2::ExpressionType type_case, ExpressionTypeToEnum(type));
  switch (type_case) {
    case bmv2::ExpressionType::header: {
      const std::string &header_name = value.string_value();
      HeaderValue *header_value = output.mutable_header_value();
      header_value->set_header_name(header_name);
      return output;
    }
    case bmv2::ExpressionType::field: {
      ASSIGN_OR_RETURN(*output.mutable_field_value(),
                       ExtractFieldValue(value.list_value()));
      return output;
    }
    case bmv2::ExpressionType::runtime_data: {
      int variable_index = value.number_value();

      Variable *variable = output.mutable_variable_value();
      variable->set_name(variables[variable_index]);
      return output;
    }
    case bmv2::ExpressionType::hexstr_: {
      *output.mutable_hexstr_value() = ExtractHexstrValue(value.string_value());
      return output;
    }
    case bmv2::ExpressionType::bool_: {
      output.mutable_bool_value()->set_value(value.bool_value());
      return output;
    }
    case bmv2::ExpressionType::string_: {
      output.mutable_string_value()->set_value(value.string_value());
      return output;
    }
    case bmv2::ExpressionType::expression: {
      const google::protobuf::Struct &expression = value.struct_value();
      ASSIGN_OR_RETURN(*(output.mutable_expression_value()),
                       ExtractRExpression(expression, variables));
      return output;
    }
    default:
      return absl::UnimplementedError(
          absl::StrCat("Unsupported rvalue ", bmv2_value.DebugString()));
  }
}

absl::StatusOr<Statement> ExtractStatement(
    const google::protobuf::Struct &action_primitive,
    const std::vector<std::string> &parameter_map) {

  if (action_primitive.fields().count("op") != 1 ||
      action_primitive.fields().count("parameters") != 1) {
    return absl::InvalidArgumentError(
        absl::StrCat("Primitive statement should contain 'op', 'parameters', "
                     "and optionally 'source_info', found ",
                     action_primitive.DebugString()));
  }

  Statement statement;
  {
    auto it = action_primitive.fields().find("source_info");
    if (it != action_primitive.fields().end()) {
      ASSIGN_OR_RETURN(*statement.mutable_source_info(),
                       ExtractSourceLocation(it->second));
    }
  }
  ASSIGN_OR_RETURN(
      bmv2::StatementOp op_case,
      StatementOpToEnum(action_primitive.fields().at("op").string_value()));

  switch (op_case) {
    case bmv2::StatementOp::assign: {
      AssignmentStatement *assignment = statement.mutable_assignment();
      const google::protobuf::Value &params =
          action_primitive.fields().at("parameters");
      if (params.kind_case() != google::protobuf::Value::kListValue ||
          params.list_value().values_size() != 2) {
        return absl::InvalidArgumentError(absl::StrCat(
            "Assignment statement must contain 2 parameters, found ",
            action_primitive.DebugString()));
      }

      ASSIGN_OR_RETURN(
          *assignment->mutable_left(),
          ExtractLValue(params.list_value().values(0), parameter_map));
      ASSIGN_OR_RETURN(
          *assignment->mutable_right(),
          ExtractRValue(params.list_value().values(1), parameter_map));
      return statement;
    }
    case bmv2::StatementOp::mark_to_drop: {
      DropStatement *drop = statement.mutable_drop();
      const google::protobuf::Value &params =
          action_primitive.fields().at("parameters");
      if (params.kind_case() != google::protobuf::Value::kListValue ||
          params.list_value().values_size() != 1) {
        return absl::InvalidArgumentError(absl::StrCat(
            "Mark to drop statement must contain 1 parameter, found ",
            action_primitive.DebugString()));
      }

      ASSIGN_OR_RETURN(
          RValue drop_rvalue,
          ExtractRValue(params.list_value().values(0), parameter_map));
      if (drop_rvalue.rvalue_case() != RValue::kHeaderValue) {
        return absl::InvalidArgumentError(absl::StrCat(
            "Mark to drop statement must be passed a header, found ",
            action_primitive.DebugString()));
      }
      drop->set_allocated_header(drop_rvalue.release_header_value());
      return statement;
    }
    case bmv2::StatementOp::modify_field_with_hash_based_offset: {
      HashStatement *hash = statement.mutable_hash();

      const google::protobuf::Value &params =
          action_primitive.fields().at("parameters");
      if (params.kind_case() != google::protobuf::Value::kListValue ||
          params.list_value().values_size() < 1) {
        return absl::InvalidArgumentError(absl::StrCat(
            "hash statement must at least specify target field, found ",
            action_primitive.DebugString()));
      }

      ASSIGN_OR_RETURN(
          LValue hash_lvalue,
          ExtractLValue(params.list_value().values(0), parameter_map));
      if (hash_lvalue.lvalue_case() != LValue::kFieldValue) {
        return absl::InvalidArgumentError(
            absl::StrCat("Hash statement in action must target a field, found ",
                         action_primitive.DebugString()));
      }
      hash->set_allocated_field(hash_lvalue.release_field_value());
      return statement;
    }
    case bmv2::StatementOp::clone_ingress_pkt_to_egress: {
      statement.mutable_clone();
      return statement;
    }
    case bmv2::StatementOp::recirculate: {
      statement.mutable_recirculate();
      return statement;
    }
    case bmv2::StatementOp::add_header:
    case bmv2::StatementOp::remove_header: {
      const google::protobuf::Value &params =
          action_primitive.fields().at("parameters");
      if (params.kind_case() != google::protobuf::Value::kListValue ||
          params.list_value().values_size() != 1) {
        return absl::InvalidArgumentError(absl::StrCat(
            "<header>.setValid() statement must contain 1 parameter, found ",
            action_primitive.DebugString()));
      }
      ASSIGN_OR_RETURN(
          RValue header,
          ExtractRValue(params.list_value().values(0), parameter_map));
      if (header.rvalue_case() != RValue::kHeaderValue) {
        return absl::InvalidArgumentError(
            absl::StrCat("<header>.setValid() statement must contain header as "
                         "parameter, found ",
                         action_primitive.DebugString()));
      }
      const std::string &header_name = header.header_value().header_name();

      AssignmentStatement &assignment = *statement.mutable_assignment();
      // LValue: The validity bit of the header.
      FieldValue &valid_bit = *assignment.mutable_left()->mutable_field_value();
      valid_bit.set_header_name(header_name);
      valid_bit.set_field_name("$valid$");
      // RValue: The boolean constant true for add_header and false for
      // remove_header.
      assignment.mutable_right()->mutable_bool_value()->set_value(
          op_case == bmv2::StatementOp::add_header);
      return statement;
    }

    case bmv2::StatementOp::assign_header: {
      HeaderAssignmentStatement &header_assignment =
          *statement.mutable_header_assignment();
      const google::protobuf::Value &params =
          action_primitive.fields().at("parameters");
      if (!params.has_list_value() || params.list_value().values_size() != 2) {
        return gutil::InvalidArgumentErrorBuilder()
               << "Header assignment must contain 2 parameters, found "
               << action_primitive.DebugString();
      }

      ASSIGN_OR_RETURN(RValue left, ExtractRValue(params.list_value().values(0),
                                                  parameter_map));
      ASSIGN_OR_RETURN(
          RValue right,
          ExtractRValue(params.list_value().values(1), parameter_map));
      if (!left.has_header_value() || !right.has_header_value()) {
        return gutil::InvalidArgumentErrorBuilder()
               << "Header assignment must be passed header instances, found "
               << action_primitive.DebugString();
      }
      header_assignment.set_allocated_left(left.release_header_value());
      header_assignment.set_allocated_right(right.release_header_value());
      return statement;
    }

    case bmv2::StatementOp::exit: {
      statement.mutable_exit();
      return statement;
    }

    default:
      return absl::UnimplementedError(absl::StrCat(
          "Unsupported statement: ", action_primitive.DebugString()));
  }
}

// Parsing and validating actions.
absl::StatusOr<Action> ExtractAction(
    const bmv2::Action &bmv2_action,
    const pdpi::IrActionDefinition &pdpi_action) {
  Action output;
  // Definition is copied form pdpi.
  *output.mutable_action_definition() = pdpi_action;

  // Implementation is extracted from bmv2.
  ActionImplementation *action_impl = output.mutable_action_implementation();

  // BMV2 format uses ints as ids for parameters.
  // We will replace the ids with the actual parameter name.
  std::vector<std::string> parameter_map(bmv2_action.runtime_data_size());
  for (int i = 0; i < bmv2_action.runtime_data_size(); i++) {
    const bmv2::VariableDefinition parameter = bmv2_action.runtime_data(i);
    (*action_impl->mutable_parameter_to_bitwidth())[parameter.name()] =
        parameter.bitwidth();
    parameter_map[i] = parameter.name();
  }

  // Parse every statement in body.
  // When encountering a parameter, look it up in the parameter map.
  for (const google::protobuf::Struct &primitive : bmv2_action.primitives()) {
    ASSIGN_OR_RETURN(*action_impl->add_action_body(),
                     ExtractStatement(primitive, parameter_map),
                     _.SetPrepend() << "In action "
                                    << pdpi_action.preamble().name() << ": ");
  }

  return output;
}

// Parsing and validating tables.
absl::StatusOr<Table> ExtractTable(
    const bmv2::Table &bmv2_table, const pdpi::IrTableDefinition &pdpi_table,
    const std::unordered_map<int, const Action &> &actions) {
  Table output;
  // Table definition is copied from pdpi.
  *output.mutable_table_definition() = pdpi_table;

  // Table implementation is extracted from bmv2.
  TableImplementation *table_impl = output.mutable_table_implementation();
  switch (bmv2_table.type()) {
    case bmv2::ActionSelectorType::simple:
      table_impl->set_action_selector_type(TableImplementation::SIMPLE);
      break;
    case bmv2::ActionSelectorType::indirect:
      table_impl->set_action_selector_type(TableImplementation::INDIRECT);
      break;
    case bmv2::ActionSelectorType::indirect_ws:
      table_impl->set_action_selector_type(TableImplementation::INDIRECT_WS);
      break;
    default:
      return absl::UnimplementedError(absl::StrCat(
          "Unsupported action selector type in ", bmv2_table.DebugString()));
  }

  // Look up the default action by its bmv2 json id.
  int default_action_id = bmv2_table.default_entry().action_id();
  if (actions.count(default_action_id) != 1) {
    return absl::InvalidArgumentError(
        absl::StrCat("Table ", pdpi_table.preamble().name(),
                     " has unknown default action id ",
                     bmv2_table.default_entry().action_id()));
  }
  const Action &default_action = actions.at(default_action_id);

  // Make sure default action arguments are consistent with its defined
  // parameters count.
  if (default_action.action_implementation().parameter_to_bitwidth_size() !=
      bmv2_table.default_entry().action_data_size()) {
    return absl::InvalidArgumentError(absl::StrCat(
        "Table ", pdpi_table.preamble().name(),
        " passes the wrong number of arguments to its default action"));
  }

  // Extract default entry from bmv2 json.
  table_impl->set_default_action(
      default_action.action_definition().preamble().name());
  table_impl->mutable_default_action_parameters()->CopyFrom(
      bmv2_table.default_entry().action_data());

  // Set which controls are next for each possible action match in this table.
  for (const auto &[action_name, next_control] : bmv2_table.next_tables()) {
    table_impl->mutable_action_to_next_control()->insert(
        {action_name, Bmv2ToIrControlName(next_control)});
  }

  // Build a mapping from match names to match target field.
  for (const bmv2::TableKey &match_key : bmv2_table.key()) {
    if (match_key.target_size() != 2) {
      return absl::InvalidArgumentError(
          absl::StrCat("Table \"", bmv2_table.name(),
                       "\" has a match key with a non field target ",
                       match_key.DebugString()));
    }

    FieldValue &field =
        (*table_impl->mutable_match_name_to_field())[match_key.name()];
    field.set_header_name(match_key.target(0));
    field.set_field_name(match_key.target(1));
  }

  return output;
}

// Translates the "extract" parser operation from the BMv2 protobuf message.
absl::StatusOr<ParserOperation::Extract> ExtractExtractParserOp(
    const bmv2::ParserOperation &bmv2_op) {
  ParserOperation::Extract result;

  // The "extract" parser operation must have exactly 1 parameter.
  if (bmv2_op.parameters_size() != 1) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Parser extract op must have 1 parameter, found "
           << bmv2_op.DebugString();
  }

  const ::google::protobuf::Struct &bmv2_param = bmv2_op.parameters(0);

  // Make sure the parameter struct contains the correct fields.
  if (!bmv2_param.fields().contains("type") ||
      !bmv2_param.fields().at("type").has_string_value() ||
      !bmv2_param.fields().contains("value") ||
      !bmv2_param.fields().at("value").has_string_value()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Extract operation has an invalid parameter: "
           << bmv2_param.DebugString();
  }

  const std::string &bmv2_type = bmv2_param.fields().at("type").string_value();
  const std::string &bmv2_value =
      bmv2_param.fields().at("value").string_value();

  if (bmv2_type == "regular") {
    // `bmv2_value` is the name of the header to be extracted.
    result.mutable_header()->set_header_name(bmv2_value);
  } else if (bmv2_type == "stack" || bmv2_type == "union_stack") {
    // Stacks and union stacks are not supported at the moment.
    return absl::UnimplementedError(
        absl::StrFormat("Unsupported parameter type '%s'", bmv2_type));
  } else {
    return absl::InvalidArgumentError(
        absl::StrFormat("Parameter type must be one of [regular, stack, "
                        "union_stack]. Found '%s'",
                        bmv2_type));
  }

  return result;
}

// Translates the "set" parser operation from the BMv2 protobuf message.
absl::StatusOr<ParserOperation::Set> ExtractSetParserOp(
    const bmv2::ParserOperation &bmv2_op) {
  ParserOperation::Set result;

  // The "set" parser operation must have exactly 2 parameters.
  if (bmv2_op.parameters_size() != 2) {
    return absl::InvalidArgumentError(absl::StrCat(
        "Parser set op must have 2 parameters, found ", bmv2_op.DebugString()));
  }

  const ::google::protobuf::Struct &bmv2_lparam = bmv2_op.parameters(0);
  const ::google::protobuf::Struct &bmv2_rparam = bmv2_op.parameters(1);

  // Make sure the L-parameter struct contains the correct fields.
  if (!bmv2_lparam.fields().contains("type") ||
      !bmv2_lparam.fields().at("type").has_string_value() ||
      !bmv2_lparam.fields().contains("value") ||
      !bmv2_lparam.fields().at("value").has_list_value()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Set operation has invalid parameters: "
           << bmv2_lparam.DebugString();
  }

  // Translate the L-parameter of the "set" parser operation.
  const std::string &bmv2_ltype =
      bmv2_lparam.fields().at("type").string_value();
  if (bmv2_ltype != "field") {
    return absl::InvalidArgumentError(absl::StrFormat(
        "Parameter type must be 'field'. Found '%s'", bmv2_ltype));
  }

  const google::protobuf::ListValue &bmv2_lvalue =
      bmv2_lparam.fields().at("value").list_value();
  ASSIGN_OR_RETURN(*result.mutable_lvalue(), ExtractFieldValue(bmv2_lvalue));

  // Make sure the R-parameter struct contains the correct fields.
  if (!bmv2_rparam.fields().contains("type") ||
      !bmv2_rparam.fields().at("type").has_string_value() ||
      !bmv2_rparam.fields().contains("value")) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Set operation has invalid parameters: "
           << bmv2_rparam.DebugString();
  }

  // Translate the R-parameter of "set" parser operation.
  const std::string &bmv2_rtype =
      bmv2_rparam.fields().at("type").string_value();
  const google::protobuf::Value &bmv2_rvalue = bmv2_rparam.fields().at("value");

  if (bmv2_rtype == "field") {
    ASSIGN_OR_RETURN(*result.mutable_field_rvalue(),
                     ExtractFieldValue(bmv2_rvalue.list_value()));
  } else if (bmv2_rtype == "hexstr") {
    const std::string &bmv2_hexstr =
        bmv2_rparam.fields().at("value").string_value();
    *result.mutable_hexstr_rvalue() = ExtractHexstrValue(bmv2_hexstr);
  } else if (bmv2_rtype == "lookahead") {
    const ::google::protobuf::ListValue &bmv2_lookahead =
        bmv2_rparam.fields().at("value").list_value();
    ASSIGN_OR_RETURN(*result.mutable_lookahead_rvalue(),
                     ExtractLookaheadValue(bmv2_lookahead));
  } else if (bmv2_rtype == "expression") {
    RExpression &rvalue = *result.mutable_expression_rvalue();
    const google::protobuf::Struct &bmv2_expression =
        bmv2_rparam.fields().at("value").struct_value();
    ASSIGN_OR_RETURN(rvalue, ExtractRExpression(bmv2_expression, {}));
  } else {
    return absl::InvalidArgumentError(
        absl::StrFormat("Invalid parameter type '%s'", bmv2_rtype));
  }

  return result;
}

// Translates the "primitive" parser operation from the BMv2 protobuf message.
// Currently only "add_header" and "remove_header" primitives are supported,
// which correspond to "setValid" and "setInvalid" methods respectively.
absl::StatusOr<ParserOperation::Primitive> ExtractPrimitiveParserOp(
    const bmv2::ParserOperation &bmv2_op) {
  ParserOperation::Primitive result;

  // The "primitive" parser operation must have exactly 1 parameter.
  if (bmv2_op.parameters_size() != 1) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Parser primitive op must have 1 parameter, found "
           << bmv2_op.DebugString();
  }

  const ::google::protobuf::Struct &bmv2_param = bmv2_op.parameters(0);

  // Make sure the parameter struct contains the correct fields.
  if (!bmv2_param.fields().contains("op") ||
      !bmv2_param.fields().at("op").has_string_value() ||
      !bmv2_param.fields().contains("parameters") ||
      !bmv2_param.fields().at("parameters").has_list_value()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Primitive operation has an invalid parameter: "
           << bmv2_param.DebugString();
  }

  const std::string &bmv2_primitive_op =
      bmv2_param.fields().at("op").string_value();
  const ::google::protobuf::ListValue &bmv2_primitive_parameters =
      bmv2_param.fields().at("parameters").list_value();
  ASSIGN_OR_RETURN(bmv2::StatementOp op_case,
                   StatementOpToEnum(bmv2_primitive_op));

  switch (op_case) {
    case bmv2::StatementOp::add_header:
    case bmv2::StatementOp::remove_header: {
      // "add_header" or "remove_header" primitives must have exactly 1
      // parameter.
      if (bmv2_primitive_parameters.values_size() != 1) {
        return gutil::InvalidArgumentErrorBuilder()
               << "setValid/setInvalid statements must contain 1 parameter, "
                  "found: "
               << bmv2_primitive_parameters.DebugString();
      }

      ASSIGN_OR_RETURN(RValue header,
                       ExtractRValue(bmv2_primitive_parameters.values(0), {}));

      // "add_header" or "remove_header" primitives must have a header name as
      // the parameter.
      if (header.rvalue_case() != RValue::kHeaderValue) {
        return gutil::InvalidArgumentErrorBuilder()
               << "setValid/setInvalid statements must have header as the "
                  "parameter, found: "
               << bmv2_primitive_parameters.DebugString();
      }

      const std::string &header_name = header.header_value().header_name();

      // Set the field `<header>.$valid$` to true or false based on whether the
      // primitive is `add_header` or `remove_header` respectively.
      AssignmentStatement &assignment = *result.mutable_assignment();
      FieldValue &valid_field =
          *assignment.mutable_left()->mutable_field_value();
      valid_field.set_header_name(header_name);
      valid_field.set_field_name("$valid$");
      assignment.mutable_right()->mutable_bool_value()->set_value(
          op_case == bmv2::StatementOp::add_header);
      break;
    }
    default: {
      return gutil::UnimplementedErrorBuilder()
             << "Unsupported primitive op: " << bmv2_param.DebugString();
    }
  }

  return result;
}

// Translates parser operations.
// Currently only "extract", "set", and "primitive" parser operations are
// supported since others are not required at the moment.
absl::StatusOr<ParserOperation> ExtractParserOperation(
    const bmv2::ParserOperation &bmv2_op) {
  ParserOperation result;

  switch (bmv2_op.op()) {
    case bmv2::ParserOperation::extract: {
      ASSIGN_OR_RETURN(*result.mutable_extract(),
                       ExtractExtractParserOp(bmv2_op));
      break;
    }
    case bmv2::ParserOperation::set: {
      ASSIGN_OR_RETURN(*result.mutable_set(), ExtractSetParserOp(bmv2_op));
      break;
    }
    case bmv2::ParserOperation::primitive: {
      ASSIGN_OR_RETURN(*result.mutable_primitive(),
                       ExtractPrimitiveParserOp(bmv2_op));
      break;
    }
    default: {
      return absl::UnimplementedError(
          absl::StrCat("Unsupported parser op: ", bmv2_op.DebugString()));
    }
  }

  return result;
}

// Translates parser transition key fields.
absl::StatusOr<ParserTransitionKeyField> ExtractParserTransitionKeyField(
    const bmv2::ParserTransitionKeyField &bmv2_key_field) {
  ParserTransitionKeyField result;

  switch (bmv2_key_field.type()) {
    case bmv2::ParserTransitionKeyField::field: {
      ASSIGN_OR_RETURN(*result.mutable_field(),
                       ExtractFieldValue(bmv2_key_field.value()));
      break;
    }
    case bmv2::ParserTransitionKeyField::lookahead:
    case bmv2::ParserTransitionKeyField::stack_field:
    case bmv2::ParserTransitionKeyField::union_stack_field: {
      return absl::UnimplementedError(
          absl::StrCat("Unsupported parser transition key field type: ",
                       bmv2_key_field.type()));
    }
    default: {
      return absl::InvalidArgumentError(
          absl::StrCat("Invalid parser transition key field: ",
                       bmv2_key_field.DebugString()));
    }
  }

  return result;
}

// Translates a parser's state transition from the BMv2 protobuf message.
absl::StatusOr<ParserTransition> ExtractParserTransition(
    const bmv2::ParserTransition &bmv2_transition) {
  ParserTransition result;
  const std::string &bmv2_value = bmv2_transition.value();
  const std::string &bmv2_mask = bmv2_transition.mask();
  const std::string &bmv2_next_state = bmv2_transition.next_state();

  switch (bmv2_transition.type()) {
    case bmv2::ParserTransitionType::default_: {
      DefaultTransition &default_transition =
          *result.mutable_default_transition();
      default_transition.set_next_state(
          Bmv2ToIrParseStateName(bmv2_next_state));
      break;
    }

    case bmv2::ParserTransitionType::hexstr: {
      HexStringTransition &hexstr_transition =
          *result.mutable_hex_string_transition();

      if (bmv2_value.empty()) {
        return absl::InvalidArgumentError(absl::StrCat(
            "Empty hex string value: ", bmv2_transition.DebugString()));
      }

      *hexstr_transition.mutable_value() = ExtractHexstrValue(bmv2_value);
      *hexstr_transition.mutable_mask() = ExtractHexstrValue(bmv2_mask);
      hexstr_transition.set_next_state(Bmv2ToIrParseStateName(bmv2_next_state));
      break;
    }

    case bmv2::ParserTransitionType::parse_vset: {
      return absl::UnimplementedError(
          absl::StrCat("Unsupported parser transition type: ",
                       bmv2_transition.DebugString()));
    }

    default: {
      return absl::InvalidArgumentError(
          absl::StrCat("Parser transition type must be one of [default, "
                       "hexstr, parse_vset]. Found: ",
                       bmv2_transition.DebugString()));
    }
  }

  return result;
}

// Translates a parse state from the BMv2 protobuf message.
absl::StatusOr<ParseState> ExtractParseState(
    const bmv2::ParseState &bmv2_parse_state) {
  ParseState state;
  state.set_name(bmv2_parse_state.name());

  for (const auto &op : bmv2_parse_state.parser_ops()) {
    ASSIGN_OR_RETURN(*state.add_parser_ops(), ExtractParserOperation(op));
  }

  for (const auto &key_field : bmv2_parse_state.transition_key()) {
    ASSIGN_OR_RETURN(*state.add_transition_key_fields(),
                     ExtractParserTransitionKeyField(key_field));
  }

  for (const auto &transition : bmv2_parse_state.transitions()) {
    ASSIGN_OR_RETURN(*state.add_transitions(),
                     ExtractParserTransition(transition));
  }

  return state;
}

// Translates a parser from the BMv2 protobuf message.
absl::StatusOr<Parser> ExtractParser(const bmv2::Parser &bmv2_parser) {
  Parser parser;
  parser.set_name(bmv2_parser.name());
  parser.set_initial_state(bmv2_parser.init_state());

  for (const auto &parse_state : bmv2_parser.parse_states()) {
    ASSIGN_OR_RETURN((*parser.mutable_parse_states())[parse_state.name()],
                     ExtractParseState(parse_state));
  }

  return parser;
}

absl::StatusOr<Deparser> ExtractDeparser(const bmv2::Deparser &bmv2_deparser) {
  Deparser deparser;
  deparser.set_name(bmv2_deparser.name());
  for (const std::string &header_name : bmv2_deparser.order()) {
    deparser.add_header_order(header_name);
  }
  return deparser;
}

// Translate an error code definition from the BMv2 protobuf message.
absl::StatusOr<Error> ExtractError(
    const google::protobuf::ListValue &bmv2_error) {
  // A BMv2 error must have 2 elements.
  if (bmv2_error.values_size() != 2) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Error field must contain 2 elements. Found: "
           << bmv2_error.DebugString();
  }

  if (!bmv2_error.values(0).has_string_value() ||
      !bmv2_error.values(1).has_number_value()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Error field must be [string, int]. Found: "
           << bmv2_error.DebugString();
  }

  Error output;
  output.set_name(bmv2_error.values(0).string_value());
  output.set_value(bmv2_error.values(1).number_value());
  return output;
}

}  // namespace

// Main Translation function.
absl::StatusOr<P4Program> Bmv2AndP4infoToIr(const bmv2::P4Program &bmv2,
                                            const pdpi::IrP4Info &pdpi) {
  P4Program output;

  // Translate headers.
  for (const bmv2::Header &header : bmv2.headers()) {
    for (const bmv2::HeaderType &header_type : bmv2.header_types()) {
      if (header.header_type() == header_type.name()) {
        ASSIGN_OR_RETURN((*output.mutable_headers())[header.name()],
                         ExtractHeaderType(header_type));
        break;
      }
    }
  }

  // Check the number of parsers. The current implementation of the P4 compiler
  // compresses all the parsers in the P4 program into one big parser with name
  // mangling, where the name of each parse state is prefixed with the name of
  // its original parser.
  // For instance, the compilation output of the following P4 program snippet
  // may contain states named "main_parser_parse_ethernet" and
  // "ipv4_parser_parse_ipv4". Some trivial states may also be merged together
  // by the compiler.
  //
  //   ```p4
  //   parser main_parser(...) {
  //     state start {
  //       ...
  //     }
  //     state parse_ethernet {
  //       ...
  //       ipv4_parser.apply(...);
  //       transition accept;
  //     }
  //   }
  //
  //   parser ipv4_parser(...) {
  //     ...
  //   }
  //   ```
  if (bmv2.parsers_size() != 1) {
    return absl::InvalidArgumentError(
        absl::StrCat("Expected single parser. Found: ", bmv2.parsers_size()));
  }

  // Translate parsers from BMv2.
  for (const bmv2::Parser &bmv2_parser : bmv2.parsers()) {
    Parser &extracted_parser = (*output.mutable_parsers())[bmv2_parser.name()];
    ASSIGN_OR_RETURN(extracted_parser, ExtractParser(bmv2_parser));
  }

  // Check the number of deparsers. The current implementation of the P4
  // compiler compresses all the deparsers in the P4 program into one big
  // deparser. Since conditional statements are disallowed in parsers, the
  // compiler outputs one ordered list of header names in the output JSON. For
  // instance, the compilation output of the following P4 program snippet will
  // contain the header order: ["ethernet", "ipv4", "ipv4"].
  //
  //   ```p4
  //   control deparser2(packet_out packet, in headers hdr) {
  //       apply {
  //           packet.emit(hdr.ipv4);
  //       }
  //   }
  //   control main_deparser(packet_out packet, in headers hdr) {
  //       apply {
  //           packet.emit(hdr.ethernet);
  //           packet.emit(hdr.ipv4);
  //           deparser2.apply(packet, hdr);
  //       }
  //   }
  //   ```
  if (bmv2.deparsers_size() != 1) {
    return absl::InvalidArgumentError(absl::StrCat(
        "Expected single deparser. Found: ", bmv2.deparsers_size()));
  }

  // Translate deparsers from BMv2.
  for (const bmv2::Deparser &bmv2_deparser : bmv2.deparsers()) {
    Deparser &extracted_deparser =
        (*output.mutable_deparsers())[bmv2_deparser.name()];
    ASSIGN_OR_RETURN(extracted_deparser, ExtractDeparser(bmv2_deparser));
  }

  // In reality, pdpi.actions_by_name is keyed on aliases and
  // not fully qualified names.
  std::unordered_map<std::string, const pdpi::IrActionDefinition &>
      actions_by_qualified_name;
  for (const auto &[_, action] : pdpi.actions_by_name()) {
    const std::string &name = action.preamble().name();
    actions_by_qualified_name.insert({name, action});
  }

  // Keep a mapping between an action bmv2 json id and their parsed structure.
  // Bmv2 action id is different than that from p4info/pdpi, it is only used
  // during this parsing stage, to link the action to related fields in the bmv2
  // json that refer to it by that id.
  std::unordered_map<int, const Action &> actions_by_bmv2_id;

  // Translate actions.
  for (const bmv2::Action &bmv2_action : bmv2.actions()) {
    const std::string &action_name = bmv2_action.name();

    // Matching action should exist in p4info, unless if this is some implicit
    // action. For example, an action that is automatically generated to
    // correspond to an if statement branch.
    pdpi::IrActionDefinition pdpi_action;
    if (actions_by_qualified_name.count(action_name) != 1) {
      // Fill in the fully qualified action name.
      pdpi_action.mutable_preamble()->set_name(action_name);
      pdpi_action.mutable_preamble()->set_id(bmv2_action.id());

      // Fill in the action parameters.
      auto *params_by_id = pdpi_action.mutable_params_by_id();
      auto *params_by_name = pdpi_action.mutable_params_by_name();
      for (int i = 0; i < bmv2_action.runtime_data_size(); i++) {
        const bmv2::VariableDefinition &bmv2_parameter =
            bmv2_action.runtime_data(i);

        // Bmv2 parameters ids start from 1 and are incremented in order
        // of definition.
        p4::config::v1::Action::Param *pdpi_parameter =
            (*params_by_id)[i + 1].mutable_param();
        pdpi_parameter->set_id(i + 1);
        pdpi_parameter->set_name(bmv2_parameter.name());
        pdpi_parameter->set_bitwidth(bmv2_parameter.bitwidth());

        *(*params_by_name)[bmv2_parameter.name()].mutable_param() =
            *pdpi_parameter;
      }
    } else {
      // Safe, no exception.
      pdpi_action = actions_by_qualified_name.at(action_name);
    }

    Action &parsed_action =
        (*output.mutable_actions())[pdpi_action.preamble().name()];

    ASSIGN_OR_RETURN(parsed_action, ExtractAction(bmv2_action, pdpi_action));
    actions_by_bmv2_id.insert({bmv2_action.id(), parsed_action});
  }

  // Similarly, pdpi.tables_by_name is keyed on aliases.
  std::unordered_map<std::string, const pdpi::IrTableDefinition &>
      tables_by_qualified_name;
  for (const auto &[_, table] : pdpi.tables_by_name()) {
    const std::string &name = table.preamble().name();
    tables_by_qualified_name.insert({name, table});
  }

  // Translate pipelines.
  for (const auto &pipeline : bmv2.pipelines()) {
    ir::Pipeline &ir_pipeline = (*output.mutable_pipeline())[pipeline.name()];
    ir_pipeline.set_name(pipeline.name());
    ir_pipeline.set_initial_control(Bmv2ToIrControlName(pipeline.init_table()));

    // Translate tables.
    for (const bmv2::Table &bmv2_table : pipeline.tables()) {
      const std::string &table_name = bmv2_table.name();

      // Matching table should exist in p4info, unless if this is some implicit
      // table. For example, a table that is automatically generated to
      // correspond to a conditional.
      pdpi::IrTableDefinition pdpi_table;
      if (tables_by_qualified_name.count(table_name) != 1) {
        // Set table fully qualified name.
        pdpi_table.mutable_preamble()->set_name(table_name);

        // Fill in match field maps.
        auto *match_fields_by_id = pdpi_table.mutable_match_fields_by_id();
        auto *match_fields_by_name = pdpi_table.mutable_match_fields_by_name();
        for (int i = 0; i < bmv2_table.key_size(); i++) {
          const bmv2::TableKey &key = bmv2_table.key(i);

          // Match field ids start at 1 and are incremented by 1 in order
          // of definition.
          p4::config::v1::MatchField *match_field =
              (*match_fields_by_id)[i + 1].mutable_match_field();
          match_field->set_id(i + 1);
          match_field->set_name(key.name());
          switch (key.match_type()) {
            case bmv2::TableMatchType::exact: {
              match_field->set_match_type(p4::config::v1::MatchField::EXACT);
              break;
            }
            default:
              return absl::UnimplementedError(
                  absl::StrCat("Unsupported match type ", key.DebugString(),
                               " in table", table_name));
          }

          *(*match_fields_by_name)[key.name()].mutable_match_field() =
              *match_field;
        }
      } else {
        // Safe, no exception.
        pdpi_table = tables_by_qualified_name.at(table_name);
      }

      ASSIGN_OR_RETURN(
          (*output.mutable_tables())[pdpi_table.preamble().name()],
          ExtractTable(bmv2_table, pdpi_table, actions_by_bmv2_id));
    }

    // Translate conditionals.
    for (const auto &bmv2_conditional : pipeline.conditionals()) {
      Conditional conditional;
      conditional.set_name(bmv2_conditional.name());
      conditional.set_if_branch(
          Bmv2ToIrControlName(bmv2_conditional.true_next()));
      conditional.set_else_branch(
          Bmv2ToIrControlName(bmv2_conditional.false_next()));

      // Parse condition expression.
      google::protobuf::Value expression_wrapper;
      *(expression_wrapper.mutable_struct_value()) =
          bmv2_conditional.expression();
      ASSIGN_OR_RETURN(*(conditional.mutable_condition()),
                       ExtractRValue(expression_wrapper, {}));

      (*output.mutable_conditionals())[conditional.name()] = conditional;
    }
  }

  // Translate errors from BMv2.
  for (const google::protobuf::ListValue &bmv2_error : bmv2.errors()) {
    ASSIGN_OR_RETURN(Error error, ExtractError(bmv2_error));
    (*output.mutable_errors())[error.name()] = std::move(error);
  }

  // Create the Control Flow Graph (CFG) of the program and perform analysis for
  // optimized symbolic execution.
  ASSIGN_OR_RETURN(std::unique_ptr<ControlFlowGraph> cfg,
                   ControlFlowGraph::Create(output));
  // Set the optimized symbolic execution information in the IR program using
  // the result of CFG analysis.
  for (auto &[_, parser] : *output.mutable_parsers()) {
    for (auto &[name, parse_state] : *parser.mutable_parse_states()) {
      ASSIGN_OR_RETURN(*parse_state.mutable_optimized_symbolic_execution_info(),
                       cfg->GetOptimizedSymbolicExecutionInfo(name));
    }
  }
  for (auto &[name, conditional] : *output.mutable_conditionals()) {
    ASSIGN_OR_RETURN(*conditional.mutable_optimized_symbolic_execution_info(),
                     cfg->GetOptimizedSymbolicExecutionInfo(name));
  }
  for (auto &[name, table] : *output.mutable_tables()) {
    ASSIGN_OR_RETURN(*table.mutable_table_implementation()
                          ->mutable_optimized_symbolic_execution_info(),
                     cfg->GetOptimizedSymbolicExecutionInfo(name));
  }

  return output;
}

absl::StatusOr<ir::SymbolicTableEntry> CreateSymbolicIrTableEntry(
    int table_entry_index, const ir::Table &table,
    const TableEntryPriorityParams &priority_params) {
  // Build a symbolic table entry in P4-Symbolic IR.
  ir::SymbolicTableEntry result;
  result.set_index(table_entry_index);

  // Set table name.
  const std::string &table_name = table.table_definition().preamble().name();
  result.mutable_sketch()->set_table_name(table_name);

  bool has_ternary_or_optional = false;
  pdpi::IrMatch *lpm_match = nullptr;

  for (const auto &[match_name, match_definition] :
       Ordered(table.table_definition().match_fields_by_name())) {
    // Set match name.
    pdpi::IrMatch &ir_match = *result.mutable_sketch()->add_matches();
    ir_match.set_name(match_name);

    const auto &pi_match = match_definition.match_field();
    switch (pi_match.match_type()) {
      case p4::config::v1::MatchField::TERNARY:
      case p4::config::v1::MatchField::OPTIONAL: {
        has_ternary_or_optional = true;
        break;
      }
      case p4::config::v1::MatchField::LPM: {
        lpm_match = &ir_match;
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
  if (!has_ternary_or_optional && lpm_match != nullptr) {
    if (!priority_params.prefix_length.has_value()) {
      return gutil::InvalidArgumentErrorBuilder()
             << "Prefix length must be provided for tables with a single LPM"
                "match.";
    }
    lpm_match->mutable_lpm()->set_prefix_length(*priority_params.prefix_length);
  }

  // Set priority.
  if (has_ternary_or_optional && priority_params.priority <= 0) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Priority must be greater than 0 for tables with ternary or "
              "optional matches. Found: "
           << priority_params.priority;
  }
  result.mutable_sketch()->set_priority(
      has_ternary_or_optional ? priority_params.priority : 0);

  return result;
}

int GetIndex(const TableEntry &entry) {
  switch (entry.entry_case()) {
    case TableEntry::kConcreteEntry:
      return entry.concrete_entry().index();
    case TableEntry::kSymbolicEntry:
      return entry.symbolic_entry().index();
    case TableEntry::ENTRY_NOT_SET:
      break;
  }
  LOG(ERROR) << "p4_symbolic::ir::TableEntry of unknown type: "
             << absl::StrCat(entry);
  return 0;
}

std::string GetTableName(const TableEntry &entry) {
  switch (entry.entry_case()) {
    case TableEntry::kConcreteEntry:
      return GetTableName(entry.concrete_entry());
    case TableEntry::kSymbolicEntry:
      return GetTableName(entry.symbolic_entry());
    case TableEntry::ENTRY_NOT_SET:
      break;
  }
  LOG(ERROR) << "p4_symbolic::ir::TableEntry of unknown type: "
             << absl::StrCat(entry);
  return "<invalid>";
}
std::string GetTableName(const ConcreteTableEntry &entry) {
  absl::StatusOr<std::string> table_name =
      pdpi::EntityToTableName(entry.pdpi_ir_entity());
  return table_name.ok() ? std::move(*table_name) : "<invalid>";
}
std::string GetTableName(const SymbolicTableEntry &entry) {
  return entry.sketch().table_name();
}

int GetPriority(const TableEntry &entry) {
  switch (entry.entry_case()) {
    case TableEntry::kConcreteEntry: {
      const pdpi::IrEntity &entity = entry.concrete_entry().pdpi_ir_entity();
      switch (entity.entity_case()) {
        case pdpi::IrEntity::kTableEntry:
          return entity.table_entry().priority();
        case pdpi::IrEntity::kPacketReplicationEngineEntry:
          return 0;
        case pdpi::IrEntity::ENTITY_NOT_SET:
          return 0;
      }
      break;
    }
    case TableEntry::kSymbolicEntry:
      return entry.symbolic_entry().sketch().priority();
    case TableEntry::ENTRY_NOT_SET:
      return 0;
  }
  return 0;
}

}  // namespace p4_symbolic::ir
