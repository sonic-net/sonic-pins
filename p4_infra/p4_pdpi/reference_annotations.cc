// Copyright 2025 Google LLC
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


#include "p4_infra/p4_pdpi/reference_annotations.h"

#include <string>
#include <utility>
#include <vector>

#include "absl/container/btree_map.h"
#include "absl/container/flat_hash_map.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "google/protobuf/repeated_ptr_field.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_infra/p4_pdpi/built_ins.h"
#include "p4_infra/p4_pdpi/internal/ordered_map.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/utils/annotation_parser.h"

namespace pdpi {
namespace {

using ::google::protobuf::RepeatedPtrField;
using ::p4::config::v1::MatchField;

absl::StatusOr<ParsedRefersToAnnotation> ParseAsRefersToAnnotation(
    std::string body) {
  ASSIGN_OR_RETURN(auto arg_list, annotation::ParseAsArgList(body));
  if (arg_list.size() != 2) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Invalid argument. Expected 2 args, but got " << arg_list.size();
  }
  return ParsedRefersToAnnotation{
      .table = arg_list[0],
      .field = arg_list[1],
  };
}

absl::StatusOr<ParsedReferencedByAnnotation> ParseAsReferencedByAnnotation(
    std::string body) {
  ASSIGN_OR_RETURN(auto arg_list, annotation::ParseAsArgList(body));
  if (arg_list.size() != 2) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Invalid argument. Expected 2 args, but got " << arg_list.size();
  }
  return ParsedReferencedByAnnotation{
      .table = arg_list[0],
      .field = arg_list[1],
  };
}

// Returns an IrTable containing an IrP4Table whose name and id are from the
// definition of `table_name`. Returns error if `table_name` does not exist in
// `info`.
absl::StatusOr<IrTable> CreateIrP4Table(absl::string_view table_name,
                                        const IrP4Info &info) {
  ASSIGN_OR_RETURN(const IrTableDefinition *table,
                   gutil::FindPtrOrStatus(info.tables_by_name(), table_name));
  IrTable ir_table;
  ir_table.mutable_p4_table()->set_table_name(table_name);
  ir_table.mutable_p4_table()->set_table_id(table->preamble().id());
  return ir_table;
}

// Returns an IrTable containing an IrBuiltInTable whose enum is `table_name`.
// Returns error if `table_name`is not a built-in name.
absl::StatusOr<IrTable> CreateIrBuiltInTable(absl::string_view table_name) {
  ASSIGN_OR_RETURN(IrBuiltInTable table, StringToIrBuiltInTable(table_name));
  IrTable ir_table;
  ir_table.set_built_in_table(table);
  return ir_table;
}

absl::StatusOr<IrMatchField> CreateIrP4MatchField(absl::string_view table_name,
                                                  absl::string_view field_name,
                                                  const IrP4Info &info) {
  ASSIGN_OR_RETURN(const IrTableDefinition *table,
                   gutil::FindPtrOrStatus(info.tables_by_name(), table_name));
  ASSIGN_OR_RETURN(
      const IrMatchFieldDefinition *match_field,
      gutil::FindPtrOrStatus(table->match_fields_by_name(), field_name));

  IrMatchField ir_match_field;

  // TODO: b/329428288 - Allow optional type once it is supported.
  switch (match_field->match_field().match_type()) {
  case MatchField::EXACT: {
    break;
  }
  case MatchField::OPTIONAL: {
    ir_match_field.mutable_p4_match_field()->set_is_optional(true);
    break;
  }
  default:
    return gutil::UnimplementedErrorBuilder()
           << "Only match fields of type EXACT or OPTIONAL can be used in "
              "references. Match field '"
           << field_name << "' in '" << table_name << "' has type '"
           << MatchField_MatchType_Name(
                  match_field->match_field().match_type());
  }

  ir_match_field.mutable_p4_match_field()->set_field_name(field_name);
  ir_match_field.mutable_p4_match_field()->set_field_id(
      match_field->match_field().id());
  return ir_match_field;
}

absl::StatusOr<IrMatchField> CreateIrBuiltInMatchField(
    absl::string_view table_name, absl::string_view field_name) {
  ASSIGN_OR_RETURN(IrBuiltInTable table, StringToIrBuiltInTable(table_name));
  ASSIGN_OR_RETURN(IrBuiltInMatchField field,
                   StringToIrBuiltInMatchField(field_name));
  if (!BuiltInTableHasMatchField(table, field)) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Built-in table '" << table_name
           << "' does not have built-in match field '" << field_name << "'.";
  }
  IrMatchField ir_match_field;
  ir_match_field.set_built_in_match_field(field);
  return ir_match_field;
}

absl::StatusOr<IrActionField> CreateIrP4ActionField(
    absl::string_view action_name, absl::string_view param_name,
    const IrP4Info &info) {
  ASSIGN_OR_RETURN(const IrActionDefinition *action,
                   gutil::FindPtrOrStatus(info.actions_by_name(), action_name));
  ASSIGN_OR_RETURN(
      const IrActionDefinition::IrActionParamDefinition *param,
      gutil::FindPtrOrStatus(action->params_by_name(), param_name));

  IrActionField ir_action_field;
  ir_action_field.mutable_p4_action_field()->set_action_name(action_name);
  ir_action_field.mutable_p4_action_field()->set_action_id(
      action->preamble().id());
  ir_action_field.mutable_p4_action_field()->set_parameter_name(param_name);
  ir_action_field.mutable_p4_action_field()->set_parameter_id(
      param->param().id());
  return ir_action_field;
}

absl::StatusOr<IrActionField> CreateIrBuiltInActionField(
    absl::string_view action_name, absl::string_view param_name) {
  ASSIGN_OR_RETURN(IrBuiltInAction action,
                   StringToIrBuiltInAction(action_name));
  ASSIGN_OR_RETURN(IrBuiltInParameter parameter,
                   StringToIrBuiltInParameter(param_name));
  if (!BuiltInActionHasParameter(action, parameter)) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Built-in action '" << action_name
           << "' does not have built-in parameter '" << param_name << "'.";
  }
  IrActionField ir_action_field;
  ir_action_field.mutable_built_in_action_field()->set_action(action);
  ir_action_field.mutable_built_in_action_field()->set_parameter(parameter);
  return ir_action_field;
}

}  // namespace

bool FieldIsOptional(const IrP4MatchField &p4_match_field) {
  return p4_match_field.is_optional();
}
bool FieldIsOptional(const IrMatchField &match_field) {
  return FieldIsOptional(match_field.p4_match_field());
}
bool FieldIsOptional(const IrField &field) {
  return FieldIsOptional(field.match_field());
}

absl::StatusOr<IrTable> CreateIrTable(absl::string_view table_name,
                                      const IrP4Info &info) {
  if (IsBuiltInTable(table_name)) {
    return CreateIrBuiltInTable(table_name);
  } else {
    return CreateIrP4Table(table_name, info);
  }
}

absl::StatusOr<IrMatchField> CreateIrMatchField(absl::string_view table_name,
                                                absl::string_view field_name,
                                                const IrP4Info &info) {
  if (IsBuiltInTable(table_name)) {
    return CreateIrBuiltInMatchField(table_name, field_name);
  } else {
    return CreateIrP4MatchField(table_name, field_name, info);
  }
}

absl::StatusOr<IrActionField> CreateIrActionField(absl::string_view action_name,
                                                  absl::string_view param_name,
                                                  const IrP4Info &info) {
  if (IsBuiltInAction(action_name)) {
    return CreateIrBuiltInActionField(action_name, param_name);
  } else {
    return CreateIrP4ActionField(action_name, param_name, info);
  }
}

absl::StatusOr<std::string> GetNameOfField(const IrField &field) {
  switch (field.field_case()) {
    case IrField::kMatchField: {
      switch (field.match_field().match_field_case()) {
        case IrMatchField::kP4MatchField: {
          return field.match_field().p4_match_field().field_name();
        }
        case IrMatchField::kBuiltInMatchField: {
          return IrBuiltInMatchFieldToString(
              field.match_field().built_in_match_field());
        }
        case IrMatchField::MATCH_FIELD_NOT_SET: {
          return gutil::InvalidArgumentErrorBuilder()
                 << "IrMatchField match_field oneof not set."
                 << field.DebugString();
        }
      }
    }
    case IrField::kActionField: {
      switch (field.action_field().action_field_case()) {
        case IrActionField::kP4ActionField: {
          return absl::StrCat(
              field.action_field().p4_action_field().action_name(), ".",
              field.action_field().p4_action_field().parameter_name());
        }
        case IrActionField::kBuiltInActionField: {
          return IrBuiltInParameterToString(
              field.action_field().built_in_action_field().parameter());
        }
        case IrActionField::ACTION_FIELD_NOT_SET: {
          return gutil::InvalidArgumentErrorBuilder()
                 << "IrActionField action_field oneof not set."
                 << field.DebugString();
        }
      }
    }
    case IrField::FIELD_NOT_SET: {
      return gutil::InvalidArgumentErrorBuilder()
             << "IrField field oneof not set.";
    }
  }
}

absl::StatusOr<std::string> GetNameOfAction(const IrActionField &field) {
  switch (field.action_field_case()) {
    case IrActionField::kP4ActionField: {
      return field.p4_action_field().action_name();
    }
    case IrActionField::kBuiltInActionField: {
      return IrBuiltInActionToString(field.built_in_action_field().action());
    }
    case IrField::FIELD_NOT_SET: {
      return gutil::InvalidArgumentErrorBuilder()
             << "IrActionField field oneof not set.";
    }
  }
}

absl::StatusOr<std::string> GetNameOfTable(const IrTable &table) {
  switch (table.table_case()) {
    case IrTable::kP4Table: {
      return table.p4_table().table_name();
    }
    case IrTable::kBuiltInTable: {
      return IrBuiltInTableToString(table.built_in_table());
    }
    case IrTable::TABLE_NOT_SET: {
      return gutil::InvalidArgumentErrorBuilder()
             << "IrTable table oneof not set.";
    }
  }
}

absl::StatusOr<std::vector<ParsedRefersToAnnotation>>
ParseAllRefersToAnnotations(const RepeatedPtrField<std::string> &annotations) {
  return GetAllParsedAnnotations<ParsedRefersToAnnotation>(
      "refers_to", annotations, ParseAsRefersToAnnotation);
}

absl::StatusOr<std::vector<ParsedReferencedByAnnotation>>
ParseAllReferencedByAnnotations(
    const RepeatedPtrField<std::string> &annotations) {
  return GetAllParsedAnnotations<ParsedReferencedByAnnotation>(
      "referenced_by", annotations, ParseAsReferencedByAnnotation);
}

absl::StatusOr<IrField> CreateIrFieldFromRefersTo(
    const ParsedRefersToAnnotation &annotation, const IrP4Info &info) {
  if (info.actions_by_name().contains(annotation.table) ||
      (IsBuiltInTable(annotation.table) &&
       StringToIrBuiltInParameter(annotation.field).ok())) {
    return gutil::UnimplementedErrorBuilder()
           << "@refers_to(" << annotation.table << "," << annotation.field
           << ") refers to an action. References to actions are not "
              "supported.";
  }

  IrField result;
  ASSIGN_OR_RETURN(*result.mutable_match_field(),
                   CreateIrMatchField(annotation.table, annotation.field, info),
                   _.SetPrepend()
                       << "Failed to create IrField from @refers_to: ");
  return result;
}

absl::StatusOr<IrField> CreateIrFieldFromReferencedBy(
    const ParsedReferencedByAnnotation &annotation, const IrP4Info &info) {
  absl::StatusOr<IrBuiltInTable> built_in_table =
      StringToIrBuiltInTable(annotation.table);
  std::string error_string = "Failed to create IrField from @referenced_by: ";

  if (!built_in_table.ok()) {
    return gutil::UnimplementedErrorBuilder()
           << error_string
           << "@reference_by should only be used for built-ins, references "
              "from p4 tables or actions should be captured using @refers_to. "
              "@referenced_by("
           << annotation.table << "," << annotation.field
           << ") should be replaced with an appropriate @refers_to annotation "
              "at field '"
           << annotation.field << "' in table '" << annotation.table << "'.";
  }

  IrField result;
  if (StringToIrBuiltInMatchField(annotation.field).ok()) {
    ASSIGN_OR_RETURN(
        *result.mutable_match_field(),
        CreateIrMatchField(annotation.table, annotation.field, info),
        _.SetPrepend() << error_string);
  } else if (absl::StatusOr<IrBuiltInParameter> param =
                 StringToIrBuiltInParameter(annotation.field);
             param.ok()) {
    ASSIGN_OR_RETURN(IrBuiltInAction action,
                     GetBuiltInActionFromBuiltInParameter(*param));
    ASSIGN_OR_RETURN(std::string action_name, IrBuiltInActionToString(action));
    if (!BuiltInTableHasAction(*built_in_table, action)) {
      return gutil::InvalidArgumentErrorBuilder()
             << error_string << "Built-in table '" << annotation.table
             << "' does not have built-in action '" << action_name << "'.";
    }
    ASSIGN_OR_RETURN(*result.mutable_action_field(),
                     CreateIrActionField(action_name, annotation.field, info),
                     _.SetPrepend() << error_string);
  } else {
    return gutil::InvalidArgumentErrorBuilder()
           << error_string << "'" << annotation.field << "' in @referenced_by("
           << annotation.table << "," << annotation.field
           << ") is not a known built-in match field or parameter.";
  }

  return result;
}

absl::StatusOr<std::vector<IrTableReference>> ParseIrTableReferences(
    const IrP4Info &info) {
  // References coming from actions are inherited by the tables that can use
  // those actions. This map stores the list of references from an action to a
  // destination table, keyed by the source action and destination table name.
  absl::flat_hash_map<
      std::string,  // Source action name
      absl::flat_hash_map<
          std::string,  // Destination table name
          google::protobuf::RepeatedPtrField<IrTableReference::FieldReference>>>
      field_references_by_dst_table_by_src_action;

  // Parse reference annotations on action parameters.
  for (const auto &[action_name, action_def] : info.actions_by_name()) {
    for (const auto &[param_name, param_def] :
         Ordered(action_def.params_by_name())) {
      // Parse @refers_by annotations on parameter.
      ASSIGN_OR_RETURN(
          const std::vector<ParsedRefersToAnnotation> refers_to_annotations,
          ParseAllRefersToAnnotations(param_def.param().annotations()));
      for (const ParsedRefersToAnnotation &annotation : refers_to_annotations) {
        IrTableReference::FieldReference field_reference;
        ASSIGN_OR_RETURN(*field_reference.mutable_destination(),
                         CreateIrFieldFromRefersTo(annotation, info));
        ASSIGN_OR_RETURN(
            *field_reference.mutable_source()->mutable_action_field(),
            CreateIrActionField(action_name, param_name, info));

        if (FieldIsOptional(field_reference.destination())) {
          return gutil::UnimplementedErrorBuilder()
                 << "References to optional fields are not supported. "
                    "Parameter "
                 << param_name << "in action " << action_name
                 << " refers to optional field " << annotation.field
                 << " in table " << annotation.table;
        }

        field_references_by_dst_table_by_src_action[action_name]
                                                   [annotation.table]
                                                       .Add(std::move(
                                                           field_reference));
      }

      // Parse @reference_by annotations on parameter.
      ASSIGN_OR_RETURN(
          const std::vector<ParsedReferencedByAnnotation>
              referenced_by_annotations,
          ParseAllReferencedByAnnotations(param_def.param().annotations()));
      if (!referenced_by_annotations.empty()) {
        return gutil::UnimplementedErrorBuilder()
               << "References to actions are unsupported: parameter '"
               << param_def.param().name() << "' in action '"
               << action_def.preamble().alias()
               << "' contains @referenced_by annotation.";
      }
    }
  }

  // A map used to store all `IrTableReferences`, keyed by source table name and
  // destination table name. We use a btree map to keep the result
  // deterministic (sorting the result vector is non-trivial due to proto
  // oneof's that are not easily comparable).
  absl::btree_map<std::string, absl::btree_map<std::string, IrTableReference>>
      table_references_by_dst_table_by_src_table;

  // Parse all annotations on table match fields.
  for (const auto &[table_name, table_def] : Ordered(info.tables_by_name())) {
    for (const auto &[match_field_name, match_field_def] :
         Ordered(table_def.match_fields_by_name())) {
      // Parse all @refers_to annotations on table match field.
      ASSIGN_OR_RETURN(
          const std::vector<ParsedRefersToAnnotation> refers_to_annotations,
          ParseAllRefersToAnnotations(
              match_field_def.match_field().annotations()));
      for (const ParsedRefersToAnnotation &annotation : refers_to_annotations) {
        IrTableReference &table_reference =
            table_references_by_dst_table_by_src_table[table_name]
                                                      [annotation.table];
        IrTableReference::FieldReference *field_reference =
            table_reference.add_field_references();
        ASSIGN_OR_RETURN(*field_reference->mutable_destination(),
                         CreateIrFieldFromRefersTo(annotation, info));
        ASSIGN_OR_RETURN(
            *field_reference->mutable_source()->mutable_match_field(),
            CreateIrMatchField(table_name, match_field_name, info));

        if (FieldIsOptional(field_reference->destination())) {
          return gutil::UnimplementedErrorBuilder()
                 << "References to optional fields are not supported. Match "
                    "field "
                 << match_field_name << "in table " << table_name
                 << " refers to optional field " << annotation.field
                 << " in table " << annotation.table;
        }
      }

      // Parse all @referenced_by annotations on table match field.
      ASSIGN_OR_RETURN(const std::vector<ParsedReferencedByAnnotation>
                           referenced_by_annotations,
                       ParseAllReferencedByAnnotations(
                           match_field_def.match_field().annotations()));
      for (const ParsedReferencedByAnnotation &annotation :
           referenced_by_annotations) {
        IrTableReference &table_reference =
            table_references_by_dst_table_by_src_table[annotation.table]
                                                      [table_name];
        IrTableReference::FieldReference *field_reference =
            table_reference.add_field_references();

        ASSIGN_OR_RETURN(*field_reference->mutable_source(),
                         CreateIrFieldFromReferencedBy(annotation, info));
        ASSIGN_OR_RETURN(
            *field_reference->mutable_destination()->mutable_match_field(),
            CreateIrMatchField(table_name, match_field_name, info));

        if (FieldIsOptional(field_reference->destination())) {
          return gutil::UnimplementedErrorBuilder()
                 << "References to optional fields are not supported. Match "
                    "field "
                 << annotation.field << "in table " << annotation.table
                 << " refers to optional field " << match_field_name
                 << " in table " << table_name;
        }
      }
    }

    // Inherit field references of table's actions.
    for (const auto &action_ref : table_def.entry_actions()) {
      const IrActionDefinition &action_def = action_ref.action();
      if (!field_references_by_dst_table_by_src_action.contains(
              action_def.preamble().alias())) {
        continue;
      }
      for (const auto &[dst_table, field_references] :
           field_references_by_dst_table_by_src_action[action_def.preamble()
                                                           .alias()]) {
        table_references_by_dst_table_by_src_table[table_name][dst_table]
            .mutable_field_references()
            ->MergeFrom(field_references);
      }
    }

    // Ensure that default actions do not contain references.
    for (const auto &action_ref : table_def.default_only_actions()) {
      const IrActionDefinition &action_def = action_ref.action();
      if (field_references_by_dst_table_by_src_action.contains(
              action_def.preamble().alias())) {
        return gutil::UnimplementedErrorBuilder()
               << "Defaults actions that contain references are not supported. "
               << action_def.preamble().alias()
               << " contains references and is a default action for table "
               << table_name;
      }
    }
  }

  // Assemble final result.
  std::vector<IrTableReference> result;
  for (auto &[src_table, table_references_by_dst_table] :
       table_references_by_dst_table_by_src_table) {
    for (auto &[dst_table, table_references] : table_references_by_dst_table) {
      if (table_references.field_references().empty()) {
        return gutil::InternalErrorBuilder()
               << "Empty table references should not be created. "
                  "Reference from '"
               << src_table << "' to '" << dst_table << "' is empty.";
      }

      ASSIGN_OR_RETURN(*table_references.mutable_source_table(),
                       CreateIrTable(src_table, info));
      ASSIGN_OR_RETURN(*table_references.mutable_destination_table(),
                       CreateIrTable(dst_table, info));

      result.push_back(std::move(table_references));
    }
  }
  return result;
}

}  // namespace pdpi
