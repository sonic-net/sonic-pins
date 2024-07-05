#include "p4_pdpi/reference_annotations.h"

#include <string>
#include <vector>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "google/protobuf/repeated_ptr_field.h"
#include "gutil/collections.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_pdpi/built_ins.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/utils/annotation_parser.h"

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
  return ParsedRefersToAnnotation{.table = arg_list[0], .field = arg_list[1]};
}

absl::StatusOr<ParsedReferencedByAnnotation> ParseAsReferencedByAnnotation(
    std::string body) {
  ASSIGN_OR_RETURN(auto arg_list, annotation::ParseAsArgList(body));
  if (arg_list.size() != 2) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Invalid argument. Expected 2 args, but got " << arg_list.size();
  }
  return ParsedReferencedByAnnotation{.table = arg_list[0],
                                      .field = arg_list[1]};
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
}  // namespace

absl::StatusOr<IrTable> CreateIrTable(absl::string_view table_name,
                                      const IrP4Info &info) {
  if (IsBuiltInTable(table_name)) {
    return CreateIrBuiltInTable(table_name);
  } else {
    return CreateIrP4Table(table_name, info);
  }
}

absl::StatusOr<IrBuiltInField> CreateIrBuiltInField(
    absl::string_view table_name, absl::string_view field_name) {
  ASSIGN_OR_RETURN(IrBuiltInTable table, StringToIrBuiltInTable(table_name));
  ASSIGN_OR_RETURN(IrBuiltInField field, StringToIrBuiltInField(field_name));
  if (!BuiltInTableHasField(table, field)) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Built-in table '" << table_name << "' does have built-in field '"
           << field_name << "'.";
  }

  return field;
}

absl::StatusOr<IrMatchField> CreateIrMatchField(absl::string_view table_name,
                                                absl::string_view field_name,
                                                const IrP4Info &info) {
  ASSIGN_OR_RETURN(const IrTableDefinition *table,
                   gutil::FindPtrOrStatus(info.tables_by_name(), table_name));
  ASSIGN_OR_RETURN(
      const IrMatchFieldDefinition *match_field,
      gutil::FindPtrOrStatus(table->match_fields_by_name(), field_name));

  if (match_field->match_field().match_type() != MatchField::EXACT) {
    return gutil::UnimplementedErrorBuilder()
           << "Only match fields of type EXACT can be used in references. "
              "Match field '"
           << field_name << "' in '" << table_name << "' has type '"
           << MatchField_MatchType_Name(
                  match_field->match_field().match_type());
  }

  IrMatchField field;
  field.set_field_name(field_name);
  field.set_field_id(match_field->match_field().id());
  return field;
}

absl::StatusOr<IrActionField> CreateIrActionField(absl::string_view action_name,
                                                  absl::string_view param_name,
                                                  const IrP4Info &info) {
  ASSIGN_OR_RETURN(const IrActionDefinition *action,
                   gutil::FindPtrOrStatus(info.actions_by_name(), action_name));
  ASSIGN_OR_RETURN(
      const IrActionDefinition::IrActionParamDefinition *param,
      gutil::FindPtrOrStatus(action->params_by_name(), param_name));

  IrActionField field;
  field.set_action_name(action_name);
  field.set_action_id(action->preamble().id());
  field.set_parameter_name(param_name);
  field.set_parameter_id(param->param().id());
  return field;
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
  if (info.actions_by_name().contains(annotation.table)) {
    return gutil::UnimplementedErrorBuilder()
           << "@refers_to(" << annotation.table << "," << annotation.field
           << ") refers to an action. References to actions are not "
              "supported.";
  }

  IrField result;
  if (IsBuiltInTable(annotation.table)) {
    ASSIGN_OR_RETURN(IrBuiltInField built_in_field,
                     CreateIrBuiltInField(annotation.table, annotation.field),
                     _.SetPrepend()
                         << "Failed to create IrField from @refers_to: ");
    result.set_built_in_field(built_in_field);
  } else {
    ASSIGN_OR_RETURN(
        *result.mutable_match_field(),
        CreateIrMatchField(annotation.table, annotation.field, info),
        _.SetPrepend() << "Failed to create IrField from @refers_to: ");
  }

  return result;
}

absl::StatusOr<IrField> CreateIrFieldFromReferencedBy(
    const ParsedReferencedByAnnotation &annotation, const IrP4Info &info) {
  if (info.tables_by_name().contains(annotation.table) ||
      info.actions_by_name().contains(annotation.table)) {
    return gutil::UnimplementedErrorBuilder()
           << "@reference_by should only be used for built-ins, references "
              "from p4 tables or actions should be captured using "
              "@refers_to. @referenced_by("
           << annotation.table << "," << annotation.field
           << ") should be replaced with an appropriate @refers_to annotation "
              "at field '"
           << annotation.field << "' in table '" << annotation.table << "'.";
  }

  IrField result;
  ASSIGN_OR_RETURN(IrBuiltInField built_in_field,
                   CreateIrBuiltInField(annotation.table, annotation.field),
                   _.SetPrepend()
                       << "Failed to create IrField from @referenced_by: ");
  result.set_built_in_field(built_in_field);
  return result;
}
}  // namespace pdpi
