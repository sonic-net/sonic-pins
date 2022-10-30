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

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/str_replace.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/types/optional.h"
#include "glog/logging.h"
#include "p4_pdpi/utils/annotation_parser.h"
#include "p4rt_app/sonic/adapters/producer_state_table_adapter.h"
#include "p4rt_app/utils/table_utility.h"
#include "swss/json.h"
#include "swss/json.hpp"
#include "swss/saiaclschema.h"

namespace p4rt_app {
namespace sonic {

namespace {
constexpr absl::string_view kStageAnnotationLabel = "sai_acl";
constexpr absl::string_view kBasicMatchAnnotationLabel = "sai_field";
constexpr absl::string_view kCompositeMatchAnnotationLabel = "composite_field";
constexpr absl::string_view kUdfMatchAnnotationLabel = "sai_udf";
constexpr absl::string_view kActionAnnotationLabel = "sai_action";
constexpr absl::string_view kActionParamAnnotationLabel = "sai_action_param";

using ::absl::StatusOr;
using ::gutil::InvalidArgumentErrorBuilder;
using ::pdpi::IrActionDefinition;
using ::pdpi::IrActionReference;
using ::pdpi::IrMatchFieldDefinition;
using ::pdpi::IrTableDefinition;

// Generates the AppDB DEFINITION:ACL_* Entry key for an ACL table.
StatusOr<std::string> GenerateSonicDbKeyFromIrTable(
    const IrTableDefinition& table) {
  if (table.preamble().alias().empty()) {
    return InvalidArgumentErrorBuilder()
           << "Table [" << table.ShortDebugString() << "] is missing an alias.";
  }
  return absl::Substitute("$0:ACL_$1",
                          table::TypeName(table::Type::kAclDefinition),
                          absl::AsciiStrToUpper(table.preamble().alias()));
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
nlohmann::json GenerateBasicMatchJson(
    const IrMatchFieldDefinition& match_field,
    const pdpi::annotation::AnnotationComponents& annotation) {
  nlohmann::json json;
  json["kind"] = "sai_field";
  json["format"] = pdpi::Format_Name(match_field.format());
  if (match_field.format() != pdpi::STRING) {
    json["bitwidth"] = match_field.match_field().bitwidth();
  }
  json["sai_field"] = absl::StrReplaceAll(annotation.body, {{" ", ""}});
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
    const IrMatchFieldDefinition& match_field,
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
      try {
        const swss::acl::MatchFieldSchema& element_schema =
            swss::acl::MatchFieldSchemaByName(element_match_field_name);
        element_match_field.mutable_match_field()->set_bitwidth(
            element_schema.bitwidth);
        element_match_field.set_format(pdpi::Format::HEX_STRING);
      } catch (...) {
        return gutil::InvalidArgumentErrorBuilder()
               << "Unknown SAI Match Field (" << element_match_field_name
               << ") in annotation @" << annotation.label << "("
               << annotation.body << ")";
      }
      element_json =
          GenerateBasicMatchJson(element_match_field, element_annotation);
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
    const IrMatchFieldDefinition& match_field) {
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
      json = GenerateBasicMatchJson(match_field, annotation);
      label_already_processed = true;
    } else if (annotation.label == kCompositeMatchAnnotationLabel) {
      if (label_already_processed) {
        return InvalidArgumentErrorBuilder() << *kAnnotationCountError;
      }
      ASSIGN_OR_RETURN(
          json, GenerateCompositeMatchFieldJson(match_field, annotation));
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
           << kAnnotationCountError << ". None were provided";
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
           << "Expected (action[, color])";
  }
  sai_action.action = arg_list[0];
  if (arg_list.size() > 1) {
    sai_action.color = arg_list[1];
  }

  return sai_action;
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
  if (param.param().name().empty()) {
    return InvalidArgumentErrorBuilder()
           << "ACL action parameter [" << param.ShortDebugString()
           << "] is missing an alias.";
  }
  sai_action.parameter = param.param().name();
  return sai_action;
}

// Generates an IrActionInfo from a given IrActionDefinition.
StatusOr<IrActionInfo> ParseAction(const IrActionDefinition& action) {
  IrActionInfo action_info;
  action_info.name = action.preamble().alias();
  if (action_info.name.empty()) {
    return InvalidArgumentErrorBuilder()
           << "Action [" << action.ShortDebugString()
           << "] is missing an alias.";
  }

  auto result = pdpi::GetAllAnnotationsAsArgList(
      kActionAnnotationLabel, action.preamble().annotations());
  if (result.ok()) {
    for (const std::vector<std::string>& annotation_args : result.value()) {
      ASSIGN_OR_RETURN(IrActionInfo::SaiAction sai_action,
                       ExtractActionAndColor(annotation_args));
      action_info.sai_actions.push_back(sai_action);
    }
  }

  // Sort the SaiActions to maintain consistency in the resulting JSON.
  std::map<uint32_t, IrActionInfo::SaiAction> sorted_sai_actions;
  for (const auto& pair : action.params_by_id()) {
    ASSIGN_OR_RETURN(IrActionInfo::SaiAction parameter,
                     ParseActionParam(pair.second));
    sorted_sai_actions[pair.first] = parameter;
  }
  for (const auto& pair : sorted_sai_actions) {
    action_info.sai_actions.push_back(pair.second);
  }
  return action_info;
}

// Formats an IrActionInfo::SaiAction as a JSON.
//
// Examples:
//   {"action": "SAI_PACKET_ACTION_SET_TC", "param": "tc", "color": "RED"}
//   {"action": "SAI_PACKET_ACTION_DROP", "color": "RED"}
//   {"action": "SAI_PACKET_ACTION_COPY"}
nlohmann::json CreateSaiActionJson(const IrActionInfo::SaiAction& parameter) {
  nlohmann::json json;
  json["action"] = parameter.action;
  if (!parameter.parameter.empty()) {
    json["param"] = parameter.parameter;
  }
  if (!parameter.color.empty()) {
    json["color"] = parameter.color;
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

// Example AppDB Table
//  P4RT_ACL_TABLE_DEFINITION:P4RT_ACL_PUNT_TABLE
//    "stage" = "INGRESS"
//    "match/ether_type" = "SAI_ACL_ENTRY_ATTR_FIELD_ETHER_TYPE"
//    "match/ether_dst" = "SAI_ACL_ENTRY_ATTR_FIELD_DST_MAC"
//    "match/ipv6_dst" = "SAI_ACL_ENTRY_ATTR_FIELD_DST_IPV6"
//    "match/ipv6_next_header" = "SAI_ACL_ENTRY_ATTR_FIELD_IPV6_NEXT_HEADER"
//    "match/ttl" = "SAI_ACL_ENTRY_ATTR_FIELD_TTL"
//    "match/icmp_type" = "SAI_ACL_ENTRY_ATTR_FIELD_ICMP_TYPE"
//    "match/l4_dst_port" = "SAI_ACL_ENTRY_ATTR_FIELD_L4_DST_PORT"
//    "action/copy_and_set_tc" = JsonToString([
//      {"action": "SAI_PACKET_ACTION_COPY"},
//      {"action": "SAI_ACL_ENTRY_ATTR_ACTION_SET_TC", "param": "traffic_class"}
//    ])
//    "action/punt_and_set_tc" = JsonToString([
//      {"action": "SAI_PACKET_ACTION_PUNT"},
//      {"action": "SAI_ACL_ENTRY_ATTR_ACTION_SET_TC", "param": "traffic_class"}
//    ])
//    "meter/unit" = "BYTES"
//    "counter/unit" = "PACKETS"
//    "size" = "123"
//    "priority" = "234"
StatusOr<std::vector<swss::FieldValueTuple>> GenerateSonicDbValuesFromIrTable(
    const IrTableDefinition& ir_table) {
  std::vector<swss::FieldValueTuple> values;

  ASSIGN_OR_RETURN(swss::FieldValueTuple stage, StageTuple(ir_table));
  values.push_back(stage);

  if (ir_table.match_fields_by_id().empty()) {
    return InvalidArgumentErrorBuilder()
           << "ACL table requires at least one match field.";
  }
  for (const auto& pair : ir_table.match_fields_by_id()) {
    ASSIGN_OR_RETURN(swss::FieldValueTuple match_tuple,
                     MatchTuple(pair.second));
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

  RETURN_IF_ERROR(VerifyConstDefaultActionInIrTable(ir_table));

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

  // TODO: Priority
  return values;
}

}  // namespace

StatusOr<std::string> InsertAclTableDefinition(
    ProducerStateTableAdapter& sonic_db_producer,
    const IrTableDefinition& ir_table) {
  ASSIGN_OR_RETURN(std::string key, GenerateSonicDbKeyFromIrTable(ir_table));
  ASSIGN_OR_RETURN(std::vector<swss::FieldValueTuple> values,
                   GenerateSonicDbValuesFromIrTable(ir_table));
  sonic_db_producer.set(key, values);
  return key;
}

absl::Status RemoveAclTableDefinition(
    ProducerStateTableAdapter& sonic_db_producer,
    const IrTableDefinition& ir_table) {
  ASSIGN_OR_RETURN(std::string key, GenerateSonicDbKeyFromIrTable(ir_table));
  sonic_db_producer.del(key);
  return absl::OkStatus();
}

}  // namespace sonic
}  // namespace p4rt_app
