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

#include "p4rt_app/sonic/app_db_acl_def_table_manager.h"

#include <iterator>
#include <list>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/ascii.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/str_replace.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/types/optional.h"
#include "gutil/gutil/status.h"
#include "include/nlohmann/json.hpp"
#include "p4_pdpi/utils/annotation_parser.h"
#include "p4rt_app/sonic/redis_connections.h"
#include "p4rt_app/sonic/response_handler.h"
#include "p4rt_app/utils/table_utility.h"
#include "swss/rediscommand.h"
#include "swss/saiaclschema.h"
#include "swss/table.h"

namespace p4rt_app {
namespace sonic {

namespace {
constexpr absl::string_view kStageAnnotationLabel = "sai_acl";
constexpr absl::string_view kBasicMatchAnnotationLabel = "sai_field";
constexpr absl::string_view kCompositeMatchAnnotationLabel = "composite_field";
constexpr absl::string_view kUdfMatchAnnotationLabel = "sai_udf";
constexpr absl::string_view kActionAnnotationLabel = "sai_action";
constexpr absl::string_view kActionParamAnnotationLabel = "sai_action_param";
constexpr absl::string_view kActionParamObjectTypeAnnotationLabel =
    "sai_action_param_object_type";

using ::absl::Status;
using ::absl::StatusOr;
using ::gutil::InvalidArgumentErrorBuilder;
using ::pdpi::IrActionDefinition;
using ::pdpi::IrActionReference;
using ::pdpi::IrMatchFieldDefinition;
using ::pdpi::IrTableDefinition;

swss::acl::Stage GetStage(const std::string& name) {
  if (name == "PRE_INGRESS") return swss::acl::Stage::kLookup;
  return swss::acl::StageFromName(name);
}

std::string GetStageName(swss::acl::Stage stage) {
  if (stage == swss::acl::Stage::kLookup) return "PRE_INGRESS";
  return swss::acl::StageName(stage);
}

bool IsValidColor(absl::string_view color) {
  return color == "SAI_PACKET_COLOR_GREEN" ||
         color == "SAI_PACKET_COLOR_YELLOW" || color == "SAI_PACKET_COLOR_RED";
}

bool IsValidRedirectObjectType(absl::string_view type) {
  return type == "SAI_OBJECT_TYPE_BRIDGE_PORT" ||
         type == "SAI_OBJECT_TYPE_IPMC_GROUP" ||
         type == "SAI_OBJECT_TYPE_L2MC_GROUP" ||
         type == "SAI_OBJECT_TYPE_LAG" || type == "SAI_OBJECT_TYPE_NEXT_HOP" ||
         type == "SAI_OBJECT_TYPE_NEXT_HOP_GROUP" ||
         type == "SAI_OBJECT_TYPE_PORT" ||
         type == "SAI_OBJECT_TYPE_SYSTEM_PORT";
}

// Generates the AppDB DEFINITION:ACL_* Entry key for an ACL table name.
std::string GenerateSonicDbKeyFromTableName(absl::string_view table_name) {
  return absl::Substitute("$0:ACL_$1",
                          table::TypeName(table::Type::kAclDefinition),
                          absl::AsciiStrToUpper(table_name));
}

// Generates the AppDB DEFINITION:ACL_* Entry key for an ACL table.
StatusOr<std::string> GenerateSonicDbKeyFromIrTable(
    const IrTableDefinition& table) {
  if (table.preamble().alias().empty()) {
    return InvalidArgumentErrorBuilder()
           << "Table [" << table.ShortDebugString() << "] is missing an alias.";
  }
  return GenerateSonicDbKeyFromTableName(table.preamble().alias());
}

// Generates the AppDB DEFINITION:ACL_ Entry tuple value for stage.
StatusOr<swss::FieldValueTuple> StageTuple(const IrTableDefinition& ir_table) {
  std::string stage;
  auto result = pdpi::GetAnnotationAsArgList(kStageAnnotationLabel,
                                             ir_table.preamble().annotations());
  if (!result.ok()) {
    return InvalidArgumentErrorBuilder()
           << "Table " << ir_table.preamble().alias()
           << " is not an ACL table: " << result.status();
  }
  if (result.value().empty()) {
    return InvalidArgumentErrorBuilder()
           << "Label @" << kStageAnnotationLabel << " requires a stage.";
  }
  if (result.value().size() > 1) {
    return InvalidArgumentErrorBuilder()
           << "Label @" << kStageAnnotationLabel << " only accepts one stage.";
  }
  return swss::FieldValueTuple({"stage", result.value()[0]});
}

absl::Status VerifyMatchFieldAgainstSchema(
    swss::acl::Stage stage, const IrMatchFieldDefinition& match_field,
    const std::string& sai_field) {
  swss::acl::MatchFieldSchema schema;
  try {
    schema = swss::acl::MatchFieldSchemaByName(sai_field);
  } catch (...) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Match field references unknown SAI field '" << sai_field << "'.";
  }

  if (schema.stages.count(stage) <= 0) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Sai field '" << sai_field << "' is not supported in ACL stage '"
           << GetStageName(stage) << "'.";
  }

  int bitwidth = match_field.match_field().bitwidth();
  std::string format = pdpi::Format_Name(match_field.format());
  if (match_field.format() != pdpi::STRING && bitwidth == 0) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Match field format '" << format
           << "' requires a bitwidth but none was provided for '" << sai_field
           << "'.";
  }
  if (match_field.format() != pdpi::STRING && bitwidth > schema.bitwidth) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Bitwidth '" << bitwidth << "' is larger than the SAI bitwidth '"
           << schema.bitwidth << "' for '" << sai_field << "'.";
  }
  if (format != swss::acl::FormatName(schema.format)) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Match field format '" << format
           << "' does not match the schema format '"
           << swss::acl::FormatName(schema.format) << "' for '" << sai_field
           << "'.";
  }
  return absl::OkStatus();
}

// Generate the AppDB json format of an IrMatchField with a sai_field
// annotation.
//
//   P4 annotation:
//     @sai_field(SaiMatch)
//
//   Tuple: { match/p4_match_name,
//            {
//              "kind": "sai_field",
//              "format": "HEX_STRING",
//              "bitwidth": 10,
//              "sai_field": "SaiMatch",
//            }
//          }
absl::StatusOr<nlohmann::json> GenerateBasicMatchJson(
    swss::acl::Stage stage, const IrMatchFieldDefinition& match_field,
    const pdpi::annotation::AnnotationComponents& annotation) {
  std::string sai_field = absl::StrReplaceAll(annotation.body, {{" ", ""}});
  if (sai_field.empty()) {
    return gutil::InvalidArgumentErrorBuilder()
           << kBasicMatchAnnotationLabel
           << " annotation was found but is empty.";
  }
  // RETURN_IF_ERROR(VerifyMatchFieldAgainstSchema(stage, match_field, sai_field));

  nlohmann::json json;
  json["kind"] = "sai_field";
  json["format"] = pdpi::Format_Name(match_field.format());
  if (match_field.format() != pdpi::STRING) {
    json["bitwidth"] = match_field.match_field().bitwidth();
  }
  json["sai_field"] = sai_field;

  return json;
}

// Generate the AppDB json format of an IrMatchField with a udf_field
// annotation.
//
//   P4 annotation:
//     @sai_udf(base=SAI_UDF_BASE_L3, offset=10, length=2)
//
//   Tuple: { match/p4_match_name,
//            {
//              "kind": "udf",
//              "format": "HEX_STRING",
//              "base": "SAI_UDF_BASE_L3",
//              "offset": 10,
//              "bitwidth": 16,
//            }
//          }
StatusOr<nlohmann::json> GenerateUdfMatchFieldJson(
    const IrMatchFieldDefinition& match_field,
    const pdpi::annotation::AnnotationComponents annotation) {
  // UDF field component names.
  static constexpr absl::string_view kBase = "base";
  static constexpr absl::string_view kOffset = "offset";
  static constexpr absl::string_view kByteWidth = "length";

  struct {
    absl::optional<std::string> base;
    absl::optional<int> offset;
    absl::optional<int> bitwidth;
  } udf_components;

  static const auto* const kFormatError = new std::string(absl::Substitute(
      "Bad annotation. Expected: @$0($1=<%s>, $2=<%d>, $3=<%d>)",
      kUdfMatchAnnotationLabel, kBase, kOffset, kByteWidth));

  ASSIGN_OR_RETURN(auto annotation_components,
                   pdpi::annotation::ParseAsArgList(annotation.body),
                   _.SetPrepend() << "[P4RT/PDPI] ");
  for (const std::string& annotation_component : annotation_components) {
    std::vector<std::string> split_component =
        absl::StrSplit(annotation_component, '=');
    if (split_component.size() != 2) {
      return InvalidArgumentErrorBuilder() << *kFormatError;
    }
    const std::string& component_name = split_component.at(0);
    const std::string& component_value = split_component.at(1);

    if (component_name == kBase) {
      if (udf_components.base.has_value()) {
        return InvalidArgumentErrorBuilder()
               << *kFormatError << ". " << component_name
               << " appeared multiple times";
      }
      udf_components.base = component_value;
    } else if (component_name == kOffset || component_name == kByteWidth) {
      int int_val;
      if (!absl::SimpleAtoi(component_value, &int_val)) {
        return InvalidArgumentErrorBuilder()
               << *kFormatError << ". " << annotation_component
               << " is not an integer.";
      }
      if (int_val < 0) {
        return InvalidArgumentErrorBuilder()
               << *kFormatError << ". " << annotation_component
               << " is negative.";
      }
      if (component_name == kOffset) {
        if (udf_components.offset.has_value()) {
          return InvalidArgumentErrorBuilder()
                 << *kFormatError << ". " << component_name
                 << " appeared multiple times";
        }
        udf_components.offset = int_val;
      } else {
        if (udf_components.bitwidth.has_value()) {
          return InvalidArgumentErrorBuilder()
                 << *kFormatError << ". " << component_name
                 << " appeared multiple times";
        }
        udf_components.bitwidth = int_val * 8;  // Convert bytes to bits.
      }
    } else {
      return InvalidArgumentErrorBuilder()
             << *kFormatError << ". Field " << annotation_component
             << " is unknown.";
    }
  }

  nlohmann::json json;
  json["kind"] = "udf";
  json["format"] = pdpi::Format_Name(match_field.format());

  if (!udf_components.base.has_value()) {
    return InvalidArgumentErrorBuilder()
           << *kFormatError << ". Field " << kBase << " is missing.";
  }
  json["base"] = udf_components.base.value();

  if (!udf_components.offset.has_value()) {
    return InvalidArgumentErrorBuilder()
           << *kFormatError << ". Field " << kOffset << " is missing.";
  }
  json["offset"] = udf_components.offset.value();

  if (!udf_components.bitwidth.has_value()) {
    return InvalidArgumentErrorBuilder()
           << *kFormatError << ". Field " << kByteWidth << " is missing.";
  }
  json["bitwidth"] = udf_components.bitwidth.value();

  if (match_field.match_field().bitwidth() != 0 &&
      match_field.match_field().bitwidth() != udf_components.bitwidth) {
    return InvalidArgumentErrorBuilder()
           << "UDF Annotation " << kByteWidth << " ("
           << udf_components.bitwidth.value()
           << ") does not match match_field bitwidth ("
           << match_field.match_field().bitwidth() << ")";
  }

  return json;
}

// Generate the AppDB json format of an IrMatchField with a composite_field
// annotation.
//
// Composite field annotation:
//  @format(IPV6)
//  @composite_field(@sai_field(SAI_ACL_TABLE_ATTR_FIELD_SRC_IPV6_WORD3),
//                   @sai_field(SAI_ACL_TABLE_ATTR_FIELD_SRC_IPV6_WORD2))
//
// JSON:
//  "match/src_ipv6_64bit" = {
//    "kind": "composite",
//    "format": "IPV6"
//    "bitwidth": 64,
//    "elements": [{
//        "kind": "sai_field",
//        "sai_field": "SAI_ACL_TABLE_ATTR_FIELD_SRC_IPV6_WORD3",
//        "bitwidth": 32,
//      }, {
//        "kind": "sai_field",
//        "sai_field": "SAI_ACL_TABLE_ATTR_FIELD_SRC_IPV6_WORD2",
//        "bitwidth": 32,
//    }]
//  },
//
//
// Composite field annotation:
//  @format(HEX_STRING)
//  @composite_field(@sai_udf(base=SAIUDF_BASE_L3, offset=24, length=2),
//                   @sai_udf(base=SAIUDF_BASE_L3, offset=26, length=2))
//
// JSON:
//  "match/arp_tpa" = {
//    "kind": "composite",
//    "format": "HEX_STRING"
//    "bitwidth": 32,
//    "elements": [{
//      "kind": "udf",
//      "bitwidth": 16,
//      "base": "SAI_UDF_BASE_L3",
//      "offset": 24,
//    }, {
//      "kind": "udf",
//      "bitwidth": 16,
//      "base": "SAI_UDF_BASE_L3",
//      "offset": 26,
//    }]
//  },
StatusOr<nlohmann::json> GenerateCompositeMatchFieldJson(
    swss::acl::Stage stage, const IrMatchFieldDefinition& match_field,
    const pdpi::annotation::AnnotationComponents annotation) {
  nlohmann::json json;
  json["kind"] = "composite";
  json["format"] = pdpi::Format_Name(match_field.format());
  if (match_field.format() != pdpi::STRING) {
    json["bitwidth"] = match_field.match_field().bitwidth();
  }
  ASSIGN_OR_RETURN(
      std::vector<std::string> element_annotation_strings,
      pdpi::annotation::ParseAsArgList(annotation.body),
      _.SetPrepend()
          << "[P4RT/PDPI] Failed to parse composite element annotations: ");
  std::vector<pdpi::annotation::AnnotationComponents> element_annotations =
      pdpi::GetAllAnnotations(element_annotation_strings);
  if (element_annotations.size() != element_annotation_strings.size()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "One or more arguments in an @" << kCompositeMatchAnnotationLabel
           << " annotation is not in the expected @lable(body) format. "
           << "Annotation: " << annotation.body;
  }
  int total_element_bitwidth = 0;
  for (const auto& element_annotation : element_annotations) {
    nlohmann::json element_json;
    if (element_annotation.label == kBasicMatchAnnotationLabel) {
      IrMatchFieldDefinition element_match_field;
      const std::string element_match_field_name =
          absl::StrReplaceAll(element_annotation.body, {{" ", ""}});
      if (element_match_field_name.empty()) {
        return gutil::InvalidArgumentErrorBuilder()
               << kBasicMatchAnnotationLabel << " within an @"
               << kCompositeMatchAnnotationLabel << " annotion is empty.";
      }
      try {
        // Fill in unspecified values with data from the schema.
        const swss::acl::MatchFieldSchema& element_schema =
            swss::acl::MatchFieldSchemaByName(element_match_field_name);
        element_match_field.mutable_match_field()->set_bitwidth(
            element_schema.bitwidth);
        pdpi::Format format;
        if (!pdpi::Format_Parse(swss::acl::FormatName(element_schema.format),
                                &format)) {
          return gutil::InternalErrorBuilder()
                 << "Failed to match schema format '"
                 << swss::acl::FormatName(element_schema.format)
                 << " with any pdpi::Format. This indicates a bug in the "
                 << "switch ACL schema.";
        }
        element_match_field.set_format(format);
      } catch (...) {
        return gutil::InvalidArgumentErrorBuilder()
               << "Unknown SAI Match Field (" << element_match_field_name
               << ") in annotation @" << annotation.label << "("
               << annotation.body << ")";
      }
      ASSIGN_OR_RETURN(element_json,
                       GenerateBasicMatchJson(stage, element_match_field,
                                              element_annotation),
                       _.SetPrepend()
                           << "Failed within composite match annotation @"
                           << annotation.label << "(" << annotation.body
                           << "). ");
      element_json.erase("format");  // Format isn't needed for elements.
    } else if (element_annotation.label == kUdfMatchAnnotationLabel) {
      IrMatchFieldDefinition element_match_field;
      element_match_field.set_format(pdpi::Format::HEX_STRING);
      ASSIGN_OR_RETURN(
          element_json,
          GenerateUdfMatchFieldJson(element_match_field, element_annotation),
          _.SetPrepend() << "Failed to parse UDF annotation @"
                         << element_annotation.label << "("
                         << element_annotation.body << ") in annotation @"
                         << annotation.label << "(" << annotation.body << ")");
      element_json.erase("format");  // Format isn't needed for elements.
    } else {
      return gutil::InvalidArgumentErrorBuilder()
             << "Only @" << kBasicMatchAnnotationLabel << " or @"
             << kUdfMatchAnnotationLabel
             << " annotations are allowed within a composite field.";
    }
    json["elements"].push_back(element_json);
    total_element_bitwidth += element_json["bitwidth"].get<int>();
  }
  if (total_element_bitwidth != static_cast<int>(json["bitwidth"])) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Composite field bitwidth (" << json["bitwidth"]
           << ") does not match total element bitwidth ("
           << total_element_bitwidth << "). Annotation: "
           << "@" << annotation.label << "(" << annotation.body << ")";
  }
  return json;
}

// Generates the AppDB P4RT_ACL_TABLE_DEFINITION Entry tuple value for a match
// field.
//
// Match tuples are of the form:
// { match/<match_field_name>, <sai_match_field_json> }
//
// Example:
//   Match field:
//     match_field {
//       name: "p4_match_name"
//       annotations: "@sai_field(SaiMatch)
//     }
//   Tuple: { match/p4_match_name,
//            {
//              "kind": "sai_field",
//              "format": "HEX_STRING",
//              "bitwidth": 10
//              "sai_field": "SaiMatch"
//            }
//          }
StatusOr<swss::FieldValueTuple> MatchTuple(
    swss::acl::Stage stage, const IrMatchFieldDefinition& match_field) {
  static const auto* const kAnnotationCountError = new std::string(absl::StrCat(
      "Exactly one of the following annotations "
      "must be applied to a match field: (@",
      kBasicMatchAnnotationLabel, ", @", kCompositeMatchAnnotationLabel, ", @",
      kUdfMatchAnnotationLabel, ")"));

  std::string name = match_field.match_field().name();
  if (name.empty()) {
    return InvalidArgumentErrorBuilder()
           << "Match field [" << match_field.ShortDebugString()
           << "] is missing a name.";
  }

  auto annotations =
      pdpi::GetAllAnnotations(match_field.match_field().annotations());
  bool label_already_processed = false;
  nlohmann::json json;
  for (const pdpi::annotation::AnnotationComponents& annotation : annotations) {
    if (annotation.label == kBasicMatchAnnotationLabel) {
      if (label_already_processed) {
        return InvalidArgumentErrorBuilder() << *kAnnotationCountError;
      }
      ASSIGN_OR_RETURN(json,
                       GenerateBasicMatchJson(stage, match_field, annotation));
      label_already_processed = true;
    } else if (annotation.label == kCompositeMatchAnnotationLabel) {
      if (label_already_processed) {
        return InvalidArgumentErrorBuilder() << *kAnnotationCountError;
      }
      ASSIGN_OR_RETURN(json, GenerateCompositeMatchFieldJson(stage, match_field,
                                                             annotation));
      label_already_processed = true;
    } else if (annotation.label == kUdfMatchAnnotationLabel) {
      if (label_already_processed) {
        return InvalidArgumentErrorBuilder() << *kAnnotationCountError;
      }
      ASSIGN_OR_RETURN(json,
                       GenerateUdfMatchFieldJson(match_field, annotation));
      label_already_processed = true;
    }
  }
  if (!label_already_processed) {
    return InvalidArgumentErrorBuilder()
           << *kAnnotationCountError << ". None were provided";
  }
  return swss::FieldValueTuple(
      {absl::StrCat("match/", match_field.match_field().name()), json.dump()});
}

// IrActionInfo holds the action information needed to generate the action JSON.
struct IrActionInfo {
  struct SaiAction {
    std::string action;     // SAI action name.
    std::string parameter;  // Parameter name (empty for unparameterized action)
    std::string color;      // SaiAction color (empty for unmetered actions)
    std::string object_type;  // SAI object type (empty by default)
  };

  std::string name;  // Action name
  std::vector<SaiAction> sai_actions;
};

// If the sai_action includes an action/color combination,
//   Returns a SaiAction associated action & color.
// Otherwise,
//   Returns a SaiAction with the associated action.
StatusOr<IrActionInfo::SaiAction> ExtractActionAndColor(
    const std::vector<std::string>& arg_list) {
  IrActionInfo::SaiAction sai_action;

  if (arg_list.empty()) {
    return InvalidArgumentErrorBuilder()
           << "ACL action annotation is missing arguments.";
  }
  if (arg_list.size() > 2) {
    return InvalidArgumentErrorBuilder()
           << "ACL action annotation has too many arguments. "
           << "Expected (action[, color]).";
  }
  sai_action.action = arg_list[0];
  if (arg_list.size() > 1) {
    sai_action.color = arg_list[1];
    if (!IsValidColor(sai_action.color)) {
      return InvalidArgumentErrorBuilder()
             << "Annotation argument '" << sai_action.color
             << "' is not a valid color value. "
             << "Annotation format: (action[, color]).";
    }
  }

  return sai_action;
}

// If the sai_action_param_object_type is included,
//   Returns the sai_object_type.
// Otherwise,
//   Returns an empty string.
StatusOr<std::string> ExtractActionParamSaiObjectType(
    const std::vector<std::string>& arg_list) {
  if (arg_list.empty()) {
    return "";
  }
  if (arg_list.size() > 1) {
    return InvalidArgumentErrorBuilder()
           << "ACL action parameter object type annotation '@"
           << kActionParamObjectTypeAnnotationLabel << "("
           << absl::StrJoin(arg_list, ",")
           << ")' has too many arguments (expected 1).";
  }
  if (!IsValidRedirectObjectType(arg_list[0])) {
    return InvalidArgumentErrorBuilder()
           << "Annotation argument '" << arg_list[0]
           << "' is not a valid sai object type.";
  }
  return arg_list[0];
}

StatusOr<IrActionInfo::SaiAction> ParseActionParam(
    const IrActionDefinition::IrActionParamDefinition& param) {
  auto annotation_args_result = pdpi::GetAnnotationAsArgList(
      kActionParamAnnotationLabel, param.param().annotations());
  if (annotation_args_result.status().code() == absl::StatusCode::kNotFound) {
    return InvalidArgumentErrorBuilder()
           << "Action parameter [" << param.ShortDebugString()
           << "] is missing a sai action annotation: @"
           << kActionParamAnnotationLabel << ".";
  }
  if (!annotation_args_result.ok()) {
    return InvalidArgumentErrorBuilder()
           << " Failed to process action parameter ["
           << param.ShortDebugString()
           << "]: " << annotation_args_result.status();
  }
  ASSIGN_OR_RETURN(IrActionInfo::SaiAction sai_action,
                   ExtractActionAndColor(annotation_args_result.value()),
                   _ << " Failed to process action parameter ["
                     << param.ShortDebugString() << "].");
  // This is an optional annotation.
  auto annotation_object_type_args_list = pdpi::GetAnnotationAsArgList(
      kActionParamObjectTypeAnnotationLabel, param.param().annotations());
  if (annotation_object_type_args_list.ok()) {
    ASSIGN_OR_RETURN(sai_action.object_type,
                     ExtractActionParamSaiObjectType(
                         annotation_object_type_args_list.value()),
                     _ << " Failed to process action parameter ["
                       << param.ShortDebugString() << "].");
  }
  if (param.param().name().empty()) {
    return InvalidArgumentErrorBuilder()
           << "ACL action parameter [" << param.ShortDebugString()
           << "] is missing an alias.";
  }
  sai_action.parameter = param.param().name();
  return sai_action;
}

absl::Status VerifyActionAgainstSchema(absl::string_view action_name,
                                       IrActionInfo::SaiAction sai_action) {
  swss::acl::ActionSchema schema;
  try {
    schema = swss::acl::ActionSchemaByName(sai_action.action);
  } catch (...) {
    return InvalidArgumentErrorBuilder() << absl::Substitute(
               "Action '$0' references unknown SAI action '$1'.", action_name,
               sai_action.action);
  }
  if (schema.format != swss::acl::Format::kNone) {
    return InvalidArgumentErrorBuilder() << absl::Substitute(
               "SAI action '$1' referenced in annotation for Action '$0' may "
               "only be applied to an action parameter.",
               action_name, sai_action.action);
  }
  return absl::OkStatus();
}

absl::Status VerifyActionParamAgainstSchema(
    absl::string_view action_name,
    const IrActionDefinition::IrActionParamDefinition& ir_param,
    const IrActionInfo::SaiAction& sai_param) {
  swss::acl::ActionSchema schema;
  const auto& param_name = ir_param.param().name();
  try {
    if (sai_param.object_type.empty()) {
      schema = swss::acl::ActionSchemaByName(sai_param.action);
    } else {
      schema = swss::acl::ActionSchemaByNameAndObjectType(
          sai_param.action, sai_param.object_type);
    }
  } catch (...) {
    return InvalidArgumentErrorBuilder() << absl::Substitute(
               "Action '$0' Param '$1' references unknown SAI field '$2'.",
               action_name, param_name, sai_param.action);
  }
  if (schema.format == swss::acl::Format::kNone) {
    return InvalidArgumentErrorBuilder() << absl::Substitute(
               "SAI action '$2' mapped to Action '$0' Param '$1' may not be "
               "applied to an action parameter.",
               action_name, param_name, sai_param.action);
  }
  std::string ir_format = pdpi::Format_Name(ir_param.format());
  std::string schema_format = swss::acl::FormatName(schema.format);
  if (ir_format != schema_format) {
    return InvalidArgumentErrorBuilder() << absl::Substitute(
               "Unsupported format '$2' declared for Action '$0' Param '$1'. "
               "Expected '$3'.",
               action_name, param_name, ir_format, schema_format);
  }
  if (schema.bitwidth > 0 && ir_param.param().bitwidth() == 0) {
    return gutil::InvalidArgumentErrorBuilder() << absl::Substitute(
               "Action format '$2' declared for Action '$0' Param '$1' "
               "requires a bitwidth but none was provided.",
               action_name, param_name, ir_format);
  }
  if (schema.bitwidth > 0 && ir_param.param().bitwidth() > schema.bitwidth) {
    return InvalidArgumentErrorBuilder() << absl::Substitute(
               "Bitwidth '$2' declared for Action '$0' Param '$1' is larger "
               "than the SAI bitwidth '$3'.",
               action_name, param_name, ir_param.param().bitwidth(),
               schema.bitwidth);
  }
  return absl::OkStatus();
}

// Generates an IrActionInfo from a given IrActionDefinition.
StatusOr<IrActionInfo> ParseAction(const IrActionDefinition& action) {
  IrActionInfo action_info;
  action_info.name = action.preamble().alias();
  if (action_info.name.empty()) {
    return InvalidArgumentErrorBuilder()
           << "Action '" << action.ShortDebugString()
           << "' is missing an alias.";
  }
  auto result = pdpi::GetAllAnnotationsAsArgList(
      kActionAnnotationLabel, action.preamble().annotations());
  if (result.ok()) {
    for (const std::vector<std::string>& annotation_args : result.value()) {
      ASSIGN_OR_RETURN(IrActionInfo::SaiAction sai_action,
                       ExtractActionAndColor(annotation_args));
      // RETURN_IF_ERROR(VerifyActionAgainstSchema(action_info.name, sai_action));
      action_info.sai_actions.push_back(sai_action);
    }
  }

  // Sort the SaiActions to maintain consistency in the resulting JSON.
  std::map<uint32_t, IrActionInfo::SaiAction> sorted_sai_actions;
  for (const auto& [id, ir_param] : action.params_by_id()) {
    ASSIGN_OR_RETURN(IrActionInfo::SaiAction sai_param,
                     ParseActionParam(ir_param),
                     _ << "In action '" << action_info.name << "'.");
    // RETURN_IF_ERROR(
    //     VerifyActionParamAgainstSchema(action_info.name, ir_param, sai_param));
    sorted_sai_actions[id] = sai_param;
  }
  for (const auto& [id, sai_action] : sorted_sai_actions) {
    action_info.sai_actions.push_back(sai_action);
  }
  return action_info;
}

// Formats an IrActionInfo::SaiAction as a JSON.
//
// Examples:
//  {"action": "SAI_PACKET_ACTION_SET_TC", "param": "tc"}
//  {"action": "SAI_PACKET_ACTION_DROP", "packet_color": "RED"}
//  {"action": "SAI_PACKET_ACTION_COPY"}
//  {"action": "SAI_ACL_ENTRY_ATTR_ACTION_REDIRECT", "param": "0x0001",
//   "object_type": "SAI_OBJECT_TYPE_IPMC_GROUP"}
nlohmann::json CreateSaiActionJson(const IrActionInfo::SaiAction& parameter) {
  nlohmann::json json;
  json["action"] = parameter.action;
  if (!parameter.parameter.empty()) {
    json["param"] = parameter.parameter;
  }
  if (!parameter.color.empty()) {
    json["packet_color"] = parameter.color;
  }
  if (!parameter.object_type.empty()) {
    json["object_type"] = parameter.object_type;
  }

  return json;
}

// Formats an IrActionInfo as a JSON.
//
// Example:
//  [{"action": "SAI_PACKET_ACTION_PUNT"},
//   {"action": "SAI_ACL_ENTRY_ATTR_ACTION_SET_TC", "param": "traffic_class"}]
std::string IrActionInfoToJsonString(IrActionInfo& action_info) {
  nlohmann::json json;
  for (const IrActionInfo::SaiAction& parameter : action_info.sai_actions) {
    json.push_back(CreateSaiActionJson(parameter));
  }
  return json.dump();
}

// Generates the AppDB P4RT_ACL_TABLE_DEFINITION Entry tuple value for an
// action.
StatusOr<swss::FieldValueTuple> ActionTuple(const IrActionDefinition& action) {
  static const auto* const kEmptyTuple = new swss::FieldValueTuple({"", ""});

  ASSIGN_OR_RETURN(IrActionInfo action_info, ParseAction(action));
  // Return an empty response if the action doesn't have any SAI mappings.
  if (action_info.sai_actions.empty()) return *kEmptyTuple;
  return swss::FieldValueTuple({absl::StrCat("action/", action_info.name),
                                IrActionInfoToJsonString(action_info)});
}

// Verifies that the const default action is either:
// * Present & Null, or
// * Not present (and emits a warning).
absl::Status VerifyConstDefaultActionInIrTable(
    const IrTableDefinition& ir_table) {
  if (ir_table.has_const_default_action()) {
    ASSIGN_OR_RETURN(IrActionInfo action_info,
                     ParseAction(ir_table.const_default_action()));
    if (action_info.name != "NoAction") {
      return InvalidArgumentErrorBuilder()
             << "const_default_action must refer to NoAction.";
    }
  } else {
    LOG(INFO)
        << "No const_default_action has been defined. Updates to the default "
        << "action, although allowed by P4 protocol, will be rejected by the "
        << "switch.";
  }
  return absl::OkStatus();
}

StatusOr<std::vector<swss::FieldValueTuple>> GenerateSonicDbValuesFromIrTable(
    const IrTableDefinition& ir_table) {
  std::vector<swss::FieldValueTuple> values;

  ASSIGN_OR_RETURN(swss::FieldValueTuple stage_tuple, StageTuple(ir_table));
  swss::acl::Stage stage;
  try {
    stage = GetStage(stage_tuple.second);
  } catch (...) {
    return gutil::InvalidArgumentErrorBuilder()
           << "ACL table references unknown stage '" << stage_tuple.second
           << "'.";
  }
  values.push_back(stage_tuple);

  if (ir_table.match_fields_by_id().empty()) {
    return InvalidArgumentErrorBuilder()
           << "ACL table requires at least one match field.";
  }
  for (const auto& [id, match_field] : ir_table.match_fields_by_id()) {
    ASSIGN_OR_RETURN(
        swss::FieldValueTuple match_tuple, MatchTuple(stage, match_field),
        _.SetPrepend() << "Failed to process match field '"
                       << match_field.match_field().name() << "'. ");
    values.push_back(match_tuple);
  }

  if (ir_table.entry_actions().empty()) {
    return InvalidArgumentErrorBuilder()
           << "ACL table requires at least one action for entries.";
  }
  for (const IrActionReference& action_ref : ir_table.entry_actions()) {
    ASSIGN_OR_RETURN(swss::FieldValueTuple action_tuple,
                     ActionTuple(action_ref.action()));
    if (action_tuple.first.empty()) {
      return InvalidArgumentErrorBuilder()
             << "ACL action [" << action_ref.action().preamble().alias()
             << "] has no SAI mapping.";
    }
    values.push_back(action_tuple);
  }

  // RETURN_IF_ERROR(VerifyConstDefaultActionInIrTable(ir_table));

  if (ir_table.size() > 0) {
    values.push_back({"size", absl::StrCat(ir_table.size())});
  }

  if (ir_table.meter().unit() != p4::config::v1::MeterSpec::UNSPECIFIED) {
    // Meter units: BYTES, PACKETS, BOTH
    values.push_back({"meter/unit", p4::config::v1::MeterSpec::Unit_Name(
                                        ir_table.meter().unit())});
  }
  if (ir_table.counter().unit() != p4::config::v1::CounterSpec::UNSPECIFIED) {
    // Counter units: BYTES, PACKETS, BOTH
    values.push_back({"counter/unit", p4::config::v1::CounterSpec::Unit_Name(
                                          ir_table.counter().unit())});
  }

  // Process optional priority setting if it exists. Skip if it doesn't.
  auto priority = pdpi::GetAnnotationBody("sai_acl_priority",
                                          ir_table.preamble().annotations());
  if (priority.ok()) {
    int priority_value;
    if (!absl::SimpleAtoi(*priority, &priority_value)) {
      return InvalidArgumentErrorBuilder()
             << "Expected integer value in @sai_acl_priority() annotation but "
             << "got '" << *priority << "'";
    }
    values.push_back({"priority", *priority});
  }

  return values;
}

absl::Status RemoveAclTableDefinitionByKey(P4rtTable& p4rt_table,
                                           absl::string_view key) {
  swss::KeyOpFieldsValuesTuple kfv;
  kfvKey(kfv) = key;
  kfvOp(kfv) = "DEL";
  p4rt_table.producer->send({kfv});

  ASSIGN_OR_RETURN(pdpi::IrUpdateStatus status,
                   GetAndProcessResponseNotificationWithoutRevertingState(
                       *p4rt_table.producer, kfvKey(kfv)));
  if (status.code() == google::rpc::OK) return absl::OkStatus();
  return gutil::InvalidArgumentErrorBuilder() << status.message();
}

}  // namespace

StatusOr<swss::KeyOpFieldsValuesTuple> AppDbAclTableDefinition(
    const pdpi::IrTableDefinition& ir_table) {
  swss::KeyOpFieldsValuesTuple kfv;
  ASSIGN_OR_RETURN(kfvKey(kfv), GenerateSonicDbKeyFromIrTable(ir_table));
  ASSIGN_OR_RETURN(kfvFieldsValues(kfv),
                   GenerateSonicDbValuesFromIrTable(ir_table));
  return kfv;
}

absl::Status InsertAclTableDefinition(P4rtTable& p4rt_table,
                                      const IrTableDefinition& ir_table) {
  swss::KeyOpFieldsValuesTuple kfv;
  ASSIGN_OR_RETURN(kfvKey(kfv), GenerateSonicDbKeyFromIrTable(ir_table));
  kfvOp(kfv) = "SET";
  ASSIGN_OR_RETURN(kfvFieldsValues(kfv),
                   GenerateSonicDbValuesFromIrTable(ir_table));
  p4rt_table.producer->send({kfv});

  ASSIGN_OR_RETURN(pdpi::IrUpdateStatus status,
                   GetAndProcessResponseNotificationWithoutRevertingState(
                       *p4rt_table.producer, kfvKey(kfv)));
  if (status.code() == google::rpc::OK) return absl::OkStatus();
  return gutil::InvalidArgumentErrorBuilder() << status.message();
}

absl::Status RemoveAclTableDefinition(P4rtTable& p4rt_table,
                                      const IrTableDefinition& ir_table) {
  swss::KeyOpFieldsValuesTuple kfv;
  ASSIGN_OR_RETURN(std::string key, GenerateSonicDbKeyFromIrTable(ir_table));
  return RemoveAclTableDefinitionByKey(p4rt_table, key);
}

absl::Status RemoveAclTableDefinition(P4rtTable& p4rt_table,
                                      absl::string_view table_name) {
  return RemoveAclTableDefinitionByKey(
      p4rt_table, GenerateSonicDbKeyFromTableName(table_name));
}

}  // namespace sonic
}  // namespace p4rt_app
