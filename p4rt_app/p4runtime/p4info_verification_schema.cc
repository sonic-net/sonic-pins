// Copyright 2022 Google LLC
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
#include "p4rt_app/p4runtime/p4info_verification_schema.h"

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/substitute.h"
#include "gutil/collections.h"
#include "gutil/proto.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4rt_app/p4runtime/p4info_verification_schema.pb.h"
#include "p4rt_app/p4runtime/p4info_verification_schema_embed.h"
#include "p4rt_app/utils/table_utility.h"

namespace p4rt_app {
namespace {
// Struct version of P4InfoVerificationSchema with name maps.
struct SchemaMap {
  struct Table {
    // Map of match fields by name.
    absl::flat_hash_map<std::string, MatchSchema> match_schemas;
    // Map of actions by name.
    absl::flat_hash_map<std::string, ActionSchema> action_schemas;
  };
  // Map of tables by name.
  absl::flat_hash_map<std::string, Table> tables;
};

// Return a version of the schema where tables, table actions, and table match
// fields are mapped by name.
SchemaMap ToSchemaMap(const P4InfoVerificationSchema& proto_schema) {
  SchemaMap schema_map;
  for (const auto& proto_table : proto_schema.tables()) {
    SchemaMap::Table struct_table;
    for (const auto& match_field : proto_table.match_fields()) {
      struct_table.match_schemas[match_field.name()] = match_field;
    }
    for (const auto& proto_action : proto_table.actions()) {
      struct_table.action_schemas[proto_action.name()] = proto_action;
    }
    schema_map.tables[proto_table.name()] = struct_table;
  }
  return schema_map;
}

// Return the Schema match type for the provided P4 match type or return an
// error if the match type is not supported.
absl::StatusOr<MatchSchema::MatchType> ToSchemaMatchType(
    p4::config::v1::MatchField::MatchType p4_match_type) {
  switch (p4_match_type) {
    case p4::config::v1::MatchField::EXACT:
    case p4::config::v1::MatchField::OPTIONAL:
      return MatchSchema::EXACT;
    case p4::config::v1::MatchField::LPM:
      return MatchSchema::LPM;
    case p4::config::v1::MatchField::TERNARY:
      return MatchSchema::TERNARY;
    case p4::config::v1::MatchField::RANGE:
    case p4::config::v1::MatchField::UNSPECIFIED:
    default:
      return gutil::InvalidArgumentErrorBuilder()
             << "Match type '"
             << p4::config::v1::MatchField::MatchType_Name(p4_match_type)
             << "' is unsupported.";
  }
}

// Build the MatchSchema from the IR match field or return an error if the match
// field cannot be translated to a supported schema.
absl::StatusOr<MatchSchema> ToMatchSchema(
    std::string name, const pdpi::IrMatchFieldDefinition& match_field) {
  MatchSchema match_schema;
  match_schema.set_name(name);

  match_schema.set_format(match_field.format());
  if (match_field.format() == pdpi::Format::HEX_STRING) {
    match_schema.set_bitwidth(match_field.match_field().bitwidth());
    if (match_schema.bitwidth() <= 0) {
      return gutil::InvalidArgumentErrorBuilder()
             << "HEX_STRING match fields must have a bitwidth.";
    }
  }

  // TODO Fill in: is_port

  ASSIGN_OR_RETURN(MatchSchema::MatchType match_type,
                   ToSchemaMatchType(match_field.match_field().match_type()));
  match_schema.set_type(match_type);
  return match_schema;
}

// Build the ActionSchema from the IR action or return an error if the action
// cannot be translated to a supported schema.
absl::StatusOr<ActionSchema> ToActionSchema(
    const pdpi::IrActionDefinition& action) {
  ActionSchema action_schema;
  action_schema.set_name(action.preamble().alias());
  for (const auto& [param_name, param] : action.params_by_name()) {
    auto& param_schema = *action_schema.add_parameters();
    param_schema.set_name(param_name);
    param_schema.set_format(param.format());
    if (param_schema.format() == pdpi::Format::HEX_STRING) {
      param_schema.set_bitwidth(param.param().bitwidth());
      if (param_schema.bitwidth() <= 0) {
        return gutil::InvalidArgumentErrorBuilder()
               << "HEX_STRING parameters must have a bitwidth.";
      }
    }
    // TODO Fill in: is_port
  }

  return action_schema;
}

// Build the TableSchema from the IR table or return an error if the table
// cannot be translated to a supported schema.
absl::StatusOr<FixedTableSchema> ToTableSchema(
    const std::string& table_name, const pdpi::IrTableDefinition& table) {
  if (table.has_counter()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Fixed tables may not contain counters.";
  }
  if (table.has_meter()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Fixed tables may not contain meters.";
  }

  FixedTableSchema table_schema;
  table_schema.set_name(table_name);
  if (table.match_fields_by_name().empty()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Table must contain at least one match field.";
  }
  for (const auto& [name, match_field] : table.match_fields_by_name()) {
    ASSIGN_OR_RETURN(*table_schema.add_match_fields(),
                     ToMatchSchema(name, match_field),
                     _.SetPrepend() << "match_field '" << name << "': ");
  }
  for (const auto& action_reference : table.entry_actions()) {
    ASSIGN_OR_RETURN(
        *table_schema.add_actions(), ToActionSchema(action_reference.action()),
        _.SetPrepend() << "action '"
                       << action_reference.action().preamble().alias()
                       << "': ");
  }
  return table_schema;
}

// Returns a description of the match type.
std::string MatchTypeDescription(MatchSchema::MatchType match_type) {
  if (match_type == MatchSchema::EXACT) return "EXACT/TERNARY";
  return MatchSchema::MatchType_Name(match_type);
}

// Return true if the match field is compatible with the known supported match
// field.
absl::Status MatchSchemaIsCompatible(MatchSchema schema,
                                     MatchSchema supported) {
  // This should never happen since we check the name before we get here.
  if (schema.name() != supported.name()) {
    return gutil::InternalErrorBuilder() << absl::Substitute(
               "Attempted to compare configured match field '$0' with schema "
               "field '$1'. This indicates a switch software bug.",
               schema.name(), supported.name());
  }
  if (schema.format() != supported.format()) {
    return gutil::InvalidArgumentErrorBuilder() << absl::Substitute(
               "Unsupported format '$1' in match field '$0'. Expected '$2'.",
               schema.name(), pdpi::Format_Name(schema.format()),
               pdpi::Format_Name(supported.format()));
  }
  if (schema.bitwidth() > supported.bitwidth()) {
    return gutil::InvalidArgumentErrorBuilder() << absl::Substitute(
               "Configured bitwidth '$1' in match field '$0' is larger than "
               "the supported bitwidth '$2'.",
               schema.name(), schema.bitwidth(), supported.bitwidth());
  }
  if (schema.type() != supported.type()) {
    return gutil::InvalidArgumentErrorBuilder() << absl::Substitute(
               "Unsupported match type '$1' in match field "
               "'$0'. Expected '$2'.",
               schema.name(), MatchTypeDescription(schema.type()),
               MatchTypeDescription(supported.type()));
  }
  return absl::OkStatus();
}

// Return true if the action is compatible with the known supported action.
absl::Status ActionSchemaIsCompatible(ActionSchema schema,
                                      ActionSchema supported) {
  // This should never happen since we check the name before we get here.
  if (schema.name() != supported.name()) {
    return gutil::InternalErrorBuilder() << absl::Substitute(
               "Attempted to compare configured action '$0' with schema action "
               "'$1'. This indicates a switch software bug.",
               schema.name(), supported.name());
  }

  // Check parameters.
  absl::flat_hash_map<std::string, const ActionSchema::ParameterSchema*>
      supported_params;
  for (const auto& param : supported.parameters()) {
    supported_params[param.name()] = &param;
  }

  if (schema.parameters_size() != supported.parameters_size()) {
    return gutil::InvalidArgumentErrorBuilder() << absl::Substitute(
               "Invalid parameter set configured in action '$0'. Parameters "
               "must be exactly [$1].",
               schema.name(),
               absl::StrJoin(gutil::Keys(supported_params), ", "));
  }
  if (schema.parameters().empty()) return absl::OkStatus();

  for (const auto& schema_param : schema.parameters()) {
    if (!supported_params.contains(schema_param.name())) {
      return gutil::NotFoundErrorBuilder() << absl::Substitute(
                 "Unrecognized parameter '$1' configured in action '$0'. "
                 "Parameters must be exactly [$2].",
                 schema.name(), schema_param.name(),
                 absl::StrJoin(gutil::Keys(supported_params), ", "));
    }
    const auto& supported_param = *supported_params.at(schema_param.name());
    if (schema_param.format() != supported_param.format()) {
      return gutil::InvalidArgumentErrorBuilder() << absl::Substitute(
                 "Unsupported format '$2' in action '$0' parameter '$1'. "
                 "Expected '$3'.",
                 schema.name(), schema_param.name(),
                 pdpi::Format_Name(schema_param.format()),
                 pdpi::Format_Name(supported_param.format()));
    }
    if (schema_param.bitwidth() > supported_param.bitwidth()) {
      return gutil::InvalidArgumentErrorBuilder() << absl::Substitute(
                 "Configured bitwidth '$2' in action '$0' parameter '$1' is "
                 "larger than the supported bitwidth '$3'.",
                 schema.name(), schema_param.name(), schema_param.bitwidth(),
                 supported_param.bitwidth());
    }
  }
  return absl::OkStatus();
}
}  // namespace

// Build the Schema from the IrP4Info or return an error if the IrP4Info cannot
// be translated to a valid schema.
absl::StatusOr<P4InfoVerificationSchema> ConvertToSchema(
    const pdpi::IrP4Info& ir_p4info) {
  P4InfoVerificationSchema schema;
  for (const auto& [table_name, table] : ir_p4info.tables_by_name()) {
    ASSIGN_OR_RETURN(table::Type table_type, GetTableType(table),
                     _.SetPrepend()
                         << "Failed to process table '" << table_name << "': ");
    if ((table_type != table::Type::kFixed) &&
                    (table_type != table::Type::kExt)) continue;

    ASSIGN_OR_RETURN(*schema.add_tables(), ToTableSchema(table_name, table),
                     _.SetPrepend()
                         << "Failed to process table '" << table_name << "': ");
  }
  return schema;
}

absl::StatusOr<P4InfoVerificationSchema> SupportedSchema() {
  const gutil::FileToc* toc = p4info_verification_schema_embed_create();
  std::string proto_string(toc[0].data, toc[0].size);
  P4InfoVerificationSchema schema;
  absl::Status result = gutil::ReadProtoFromString(proto_string, &schema);
  if (!result.ok()) {
    return gutil::InternalErrorBuilder()
           << "Failed to load the default schema. " << result.message();
  }
  return schema;
}

absl::Status IsSupportedBySchema(
    const pdpi::IrP4Info& ir_p4info,
    const P4InfoVerificationSchema& supported_schema) {
  const SchemaMap supported_schema_map = ToSchemaMap(supported_schema);

  ASSIGN_OR_RETURN(P4InfoVerificationSchema schema, ConvertToSchema(ir_p4info));
  SchemaMap schema_map = ToSchemaMap(schema);

  // The table list should be a subset of the known table tables.
  for (const auto& [table_name, candidate_table] : schema_map.tables) {
    const pdpi::IrTableDefinition *ir_table_def =
      gutil::FindOrNull(ir_p4info.tables_by_name(), table_name);
    if (ir_table_def == nullptr) {
      return gutil::NotFoundErrorBuilder()
             << "Table '" << table_name << "' can not be verified";
    }

    ASSIGN_OR_RETURN(table::Type table_type, GetTableType(*ir_table_def),
                     _ << "Failed to get table type for " << table_name << ".");
    if (table_type == table::Type::kExt) {
      // Bypass further checks for extension tables
      continue;
    }

    const auto* supported_table =
        gutil::FindOrNull(supported_schema_map.tables, table_name);
    if (supported_table == nullptr) {
      return gutil::NotFoundErrorBuilder()
             << "Table '" << table_name << "' is not a known table."
             << "If this is extension table, use table-id > 0x03000000";
    }

    // The match field list should be a subset of the known table match fields.
    // Each match field should be compatible with the known match field.
    for (const auto& [match_field_name, candidate_match_field] :
         candidate_table.match_schemas) {
      const auto* supported_match =
          gutil::FindOrNull(supported_table->match_schemas, match_field_name);
      if (supported_match == nullptr) {
        return gutil::NotFoundErrorBuilder() << absl::Substitute(
                   "Table '$0' contains unknown match field '$1'.", table_name,
                   match_field_name);
      }
      RETURN_IF_ERROR(
          MatchSchemaIsCompatible(candidate_match_field, *supported_match))
              .SetPrepend()
          << absl::Substitute("Table '$0' configuration is invalid: ",
                              table_name);
    }

    // The action list should be a subset of the known table actions.
    // Each match field should be compatible with the known match field.
    for (const auto& [action_name, candidate_action] :
         candidate_table.action_schemas) {
      const auto* supported_action =
          gutil::FindOrNull(supported_table->action_schemas, action_name);
      if (supported_action == nullptr) {
        return gutil::NotFoundErrorBuilder()
               << absl::Substitute("Table '$0' contains unknown action '$1'.",
                                   table_name, action_name);
      }
      RETURN_IF_ERROR(
          ActionSchemaIsCompatible(candidate_action, *supported_action))
              .SetPrepend()
          << absl::Substitute("Table '$0' configuration is invalid: ",
                              table_name);
    }
  }
  return absl::OkStatus();
}

}  // namespace p4rt_app
