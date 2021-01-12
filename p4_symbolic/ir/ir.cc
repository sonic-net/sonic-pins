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

#include "p4_symbolic/ir/ir.h"

#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/strip.h"
#include "google/protobuf/struct.pb.h"
#include "p4/config/v1/p4info.pb.h"

namespace p4_symbolic {
namespace ir {

namespace {

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
       bmv2::StatementOp::modify_field_with_hash_based_offset}};

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
      bmv2_expression.fields().count("condition") != 1) {
    return absl::InvalidArgumentError(
        absl::StrCat("TernaryExpression must contain 'left', and 'condition' ",
                     bmv2_expression.DebugString()));
  }

  const google::protobuf::Value &condition =
      bmv2_expression.fields().at("condition");
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
  RExpression output;
  // Integrity check.
  if (bmv2_expression.fields().count("op") != 1 ||
      bmv2_expression.fields().count("right") != 1) {
    return absl::InvalidArgumentError(
        absl::StrCat("RExpression must contain 'op' and 'right', found ",
                     bmv2_expression.DebugString()));
  }

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

  ASSIGN_OR_RETURN(bmv2::ExpressionType type_case, ExpressionTypeToEnum(type));
  switch (type_case) {
    case bmv2::ExpressionType::field: {
      const google::protobuf::ListValue &names =
          struct_value.fields().at("value").list_value();

      FieldValue *field_value = output.mutable_field_value();
      field_value->set_header_name(names.values(0).string_value());
      field_value->set_field_name(names.values(1).string_value());
      return output;
    }
    case bmv2::ExpressionType::runtime_data: {
      int variable_index = struct_value.fields().at("value").number_value();

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

  ASSIGN_OR_RETURN(bmv2::ExpressionType type_case, ExpressionTypeToEnum(type));
  switch (type_case) {
    case bmv2::ExpressionType::header: {
      const std::string &header_name =
          struct_value.fields().at("value").string_value();

      HeaderValue *header_value = output.mutable_header_value();
      header_value->set_header_name(header_name);
      return output;
    }
    case bmv2::ExpressionType::field: {
      const google::protobuf::ListValue &names =
          struct_value.fields().at("value").list_value();

      FieldValue *field_value = output.mutable_field_value();
      field_value->set_header_name(names.values(0).string_value());
      field_value->set_field_name(names.values(1).string_value());
      return output;
    }
    case bmv2::ExpressionType::runtime_data: {
      int variable_index = struct_value.fields().at("value").number_value();

      Variable *variable = output.mutable_variable_value();
      variable->set_name(variables[variable_index]);
      return output;
    }
    case bmv2::ExpressionType::hexstr_: {
      HexstrValue *hexstr_value = output.mutable_hexstr_value();
      std::string hexstr = struct_value.fields().at("value").string_value();
      if (absl::StartsWith(hexstr, "-")) {
        hexstr_value->set_value(std::string(absl::StripPrefix(hexstr, "-")));
        hexstr_value->set_negative(true);
      } else {
        hexstr_value->set_value(hexstr);
        hexstr_value->set_negative(false);
      }
      return output;
    }
    case bmv2::ExpressionType::bool_: {
      output.mutable_bool_value()->set_value(
          struct_value.fields().at("value").bool_value());
      return output;
    }
    case bmv2::ExpressionType::string_: {
      output.mutable_string_value()->set_value(
          struct_value.fields().at("value").string_value());
      return output;
    }
    case bmv2::ExpressionType::expression: {
      const google::protobuf::Struct *expression =
          &(struct_value.fields().at("value").struct_value());

      // This loop is only needed because bmv2 format has this annoying thing
      // where an expression may have its value be a single other expression
      // which value may also be another single expression, etc, until
      // finally the actual value of the expression is reached.
      // This is the bmv2 format analogous case to having an expression wrapped
      // in many useless paranthesis.
      // An example of this can be found at //p4-samples/ipv4-routing/basic.json
      // after `make build` is run in that directory.
      while (expression->fields().count("op") != 1) {
        if (expression->fields().count("type") != 1 ||
            expression->fields().at("type").string_value() != "expression" ||
            expression->fields().count("value") != 1) {
          return absl::InvalidArgumentError(
              absl::StrCat("Expression must contain 'op' at some level, found ",
                           expression->DebugString()));
        }
        expression = &(expression->fields().at("value").struct_value());
      }

      ASSIGN_OR_RETURN(*(output.mutable_expression_value()),
                       ExtractRExpression(*expression, variables));
      return output;
    }
    default:
      return absl::UnimplementedError(
          absl::StrCat("Unsupported rvalue ", bmv2_value.DebugString()));
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
  // When encoutering a parameter, look it up in the parameter map.
  for (const google::protobuf::Struct &primitive : bmv2_action.primitives()) {
    if (primitive.fields().count("op") != 1 ||
        primitive.fields().count("parameters") != 1) {
      return absl::InvalidArgumentError(absl::StrCat(
          "Primitive statement in action ", pdpi_action.preamble().name(),
          " should contain 'op', 'parameters', found ",
          primitive.DebugString()));
    }

    Statement *statement = action_impl->add_action_body();
    ASSIGN_OR_RETURN(
        bmv2::StatementOp op_case,
        StatementOpToEnum(primitive.fields().at("op").string_value()));
    switch (op_case) {
      case bmv2::StatementOp::assign: {
        AssignmentStatement *assignment = statement->mutable_assignment();
        const google::protobuf::Value &params =
            primitive.fields().at("parameters");
        if (params.kind_case() != google::protobuf::Value::kListValue ||
            params.list_value().values_size() != 2) {
          return absl::InvalidArgumentError(absl::StrCat(
              "Assignment statement in action ", pdpi_action.preamble().name(),
              " must contain 2 parameters, found ", primitive.DebugString()));
        }

        ASSIGN_OR_RETURN(
            *assignment->mutable_left(),
            ExtractLValue(params.list_value().values(0), parameter_map));
        ASSIGN_OR_RETURN(
            *assignment->mutable_right(),
            ExtractRValue(params.list_value().values(1), parameter_map));
        break;
      }
      case bmv2::StatementOp::mark_to_drop: {
        DropStatement *drop = statement->mutable_drop();
        const google::protobuf::Value &params =
            primitive.fields().at("parameters");
        if (params.kind_case() != google::protobuf::Value::kListValue ||
            params.list_value().values_size() != 1) {
          return absl::InvalidArgumentError(absl::StrCat(
              "Mark to drop statement in action ",
              pdpi_action.preamble().name(),
              " must contain 1 parameter, found ", primitive.DebugString()));
        }

        ASSIGN_OR_RETURN(
            RValue drop_rvalue,
            ExtractRValue(params.list_value().values(0), parameter_map));
        if (drop_rvalue.rvalue_case() != RValue::kHeaderValue) {
          return absl::InvalidArgumentError(absl::StrCat(
              "Mark to drop statement in action ",
              pdpi_action.preamble().name(), " must be passed a header, found ",
              primitive.DebugString()));
        }
        drop->set_allocated_header(drop_rvalue.release_header_value());
        break;
      }
      case bmv2::StatementOp::modify_field_with_hash_based_offset: {
        HashStatement *hash = statement->mutable_hash();

        const google::protobuf::Value &params =
            primitive.fields().at("parameters");
        if (params.kind_case() != google::protobuf::Value::kListValue ||
            params.list_value().values_size() < 1) {
          return absl::InvalidArgumentError(absl::StrCat(
              "hash statement in action ", pdpi_action.preamble().name(),
              " must at least specifiy target field, found ",
              primitive.DebugString()));
        }

        ASSIGN_OR_RETURN(
            LValue hash_lvalue,
            ExtractLValue(params.list_value().values(0), parameter_map));
        if (hash_lvalue.lvalue_case() != LValue::kFieldValue) {
          return absl::InvalidArgumentError(absl::StrCat(
              "Hash statement in action ", pdpi_action.preamble().name(),
              " must target a field, found ", primitive.DebugString()));
        }
        hash->set_allocated_field(hash_lvalue.release_field_value());
        break;
      }
      case bmv2::StatementOp::clone_ingress_pkt_to_egress: {
        statement->mutable_clone();
        break;
      }
      default:
        return absl::UnimplementedError(absl::StrCat(
            "Unsupported statement in action ", pdpi_action.preamble().name(),
            ", found ", primitive.DebugString()));
    }

    // Parse source_info struct into its own protobuf.
    // Applies to all types of statements.
    if (primitive.fields().count("source_info") != 1) {
      return absl::InvalidArgumentError(absl::StrCat(
          "Statement in action ", pdpi_action.preamble().name(),
          " does not have source_info, found ", primitive.DebugString()));
    }

    ASSIGN_OR_RETURN(
        *(statement->mutable_source_info()),
        ExtractSourceLocation(primitive.fields().at("source_info")));
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
    if (!next_control.empty()) {
      table_impl->mutable_action_to_next_control()->insert(
          {action_name, next_control});
    }
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

  // In reality, pdpi.actions_by_name is keyed on aliases and
  // not fully qualified names.
  std::unordered_map<std::string, const pdpi::IrActionDefinition &>
      actions_by_qualified_name;
  const auto &pdpi_actions = pdpi.actions_by_name();
  for (const auto &[_, action] : pdpi_actions) {
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

  // Translate tables.
  for (const auto &pipeline : bmv2.pipelines()) {
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
      conditional.set_if_branch(bmv2_conditional.true_next());
      conditional.set_else_branch(bmv2_conditional.false_next());

      // Parse condition expression.
      google::protobuf::Value expression_wrapper;
      *(expression_wrapper.mutable_struct_value()) =
          bmv2_conditional.expression();
      ASSIGN_OR_RETURN(*(conditional.mutable_condition()),
                       ExtractRValue(expression_wrapper, {}));

      (*output.mutable_conditionals())[conditional.name()] = conditional;
    }
  }

  // Find init_table.
  if (bmv2.pipelines_size() < 1) {
    return absl::InvalidArgumentError("BMV2 file contains no pipelines!");
  }
  output.set_initial_control(bmv2.pipelines(0).init_table());
  return output;
}

}  // namespace ir
}  // namespace p4_symbolic
