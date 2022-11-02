// Copyright 2021 Google LLC
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
#include "p4rt_app/p4runtime/ir_translation.h"

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/escaping.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/strip.h"
#include "glog/logging.h"
#include "gutil/collections.h"
#include "gutil/status.h"
#include "p4/config/v1/p4types.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/netaddr/ipv6_address.h"
#include "p4_pdpi/utils/annotation_parser.h"

namespace p4rt_app {
namespace {

bool IsPortType(const p4::config::v1::P4NamedType& type) {
  return type.name() == "port_id_t";
}

absl::Status TranslatePortValue(
    TranslationDirection direction,
    const boost::bimap<std::string, std::string>& port_map,
    pdpi::IrValue& value) {
  switch (value.format_case()) {
    case pdpi::IrValue::kStr: {
      ASSIGN_OR_RETURN(*value.mutable_str(),
                       TranslatePort(direction, port_map, value.str()));
      break;
    }
    default:
      return gutil::InvalidArgumentErrorBuilder()
             << "Port value must use Format::STRING, but found "
             << value.format_case() << " instead.";
  }

  return absl::OkStatus();
}

absl::Status TranslateAction(const TranslateTableEntryOptions& options,
                             const pdpi::IrTableDefinition& table_def,
                             pdpi::IrActionInvocation& action) {
  // Find the action definition from the ir table definition.
  absl::optional<pdpi::IrActionDefinition> action_def;
  for (const auto& entry_action : table_def.entry_actions()) {
    if (entry_action.action().preamble().alias() == action.name()) {
      action_def = entry_action.action();
    }
  }
  if (!action_def.has_value()) {
    return gutil::InternalErrorBuilder()
           << "Could not find action definition for " << action.name() << ".";
  }

  for (auto& param : *action.mutable_params()) {
    // If the paramter field isn't a port then ignore it.
    const pdpi::IrActionDefinition::IrActionParamDefinition* param_def =
        gutil::FindOrNull(action_def->params_by_name(), param.name());
    if (param_def == nullptr) {
      return gutil::InternalErrorBuilder()
             << "Could not find action param definition for " << param.name()
             << ".";
    }
    if (options.translate_port_ids &&
        IsPortType(param_def->param().type_name())) {
      RETURN_IF_ERROR(TranslatePortValue(options.direction, options.port_map,
                                         *param.mutable_value()))
          << " Found in action parameter '" << param.name() << "' of action '"
          << action.name() << "'.";
    }
  }
  return absl::OkStatus();
}

absl::Status TranslateActionSet(const TranslateTableEntryOptions& options,
                                const pdpi::IrTableDefinition& table_def,
                                pdpi::IrActionSet& action_set) {
  for (auto& action : *action_set.mutable_actions()) {
    RETURN_IF_ERROR(
        TranslateAction(options, table_def, *action.mutable_action()));

    if (options.translate_port_ids && !action.watch_port().empty()) {
      ASSIGN_OR_RETURN(*action.mutable_watch_port(),
                       TranslatePort(options.direction, options.port_map,
                                     action.watch_port()));
    }
  }
  return absl::OkStatus();
}

absl::Status TranslatePortInMatchField(
    TranslationDirection direction,
    const boost::bimap<std::string, std::string>& port_map,
    pdpi::IrMatch& match) {
  // We expect the port field to be an exact match or optional field.
  switch (match.match_value_case()) {
    case pdpi::IrMatch::kExact:
      RETURN_IF_ERROR(
          TranslatePortValue(direction, port_map, *match.mutable_exact()))
          << " Found in match field '" << match.name() << "'.";
      break;
    case pdpi::IrMatch::kOptional:
      RETURN_IF_ERROR(TranslatePortValue(
          direction, port_map, *match.mutable_optional()->mutable_value()))
          << " Found in match field '" << match.name() << "'.";
      break;
    default:
      return gutil::InvalidArgumentErrorBuilder()
             << "The port match field is not an exact or optional match "
             << "type: " << match.name();
  }
  return absl::OkStatus();
}

absl::Status TranslateMatchField(const TranslateTableEntryOptions& options,
                                 const pdpi::IrTableDefinition& table_def,
                                 pdpi::IrMatch& match) {
  // Get the match field definition to check the field type.
  const pdpi::IrMatchFieldDefinition* match_def =
      gutil::FindOrNull(table_def.match_fields_by_name(), match.name());
  if (match_def == nullptr) {
    return gutil::InternalErrorBuilder()
           << "Could not find match field definition for " << match.name()
           << ".";
  }

  if (options.translate_port_ids &&
      IsPortType(match_def->match_field().type_name())) {
    RETURN_IF_ERROR(
        TranslatePortInMatchField(options.direction, options.port_map, match));
  }

  return absl::OkStatus();
}

void SetCompositeUdfFieldFormatToHexString(
    pdpi::IrMatchFieldDefinition& match_def) {
  static constexpr absl::string_view kCompositeMatchLabel = "composite_field";
  static constexpr absl::string_view kUdfMatchLabel = "sai_udf";

  if (match_def.format() == pdpi::Format::HEX_STRING) return;

  auto parse_result = pdpi::GetAnnotationAsArgList(
      kCompositeMatchLabel, match_def.match_field().annotations());
  if (!parse_result.ok()) return;     // Composite annotation not found.
  if (parse_result->empty()) return;  // No sub-fields.

  // Check if all sub-fields are UDF.
  for (const pdpi::annotation::AnnotationComponents& annotation :
       pdpi::GetAllAnnotations(*parse_result)) {
    if (annotation.label != kUdfMatchLabel) {
      return;
    }
  }

  match_def.set_format(pdpi::Format::HEX_STRING);
}

void TranslateIrTableDefForOrchAgent(pdpi::IrTableDefinition& table_def) {
  for (auto& [match_id, match_def] : *table_def.mutable_match_fields_by_id()) {
    SetCompositeUdfFieldFormatToHexString(match_def);
  }
  for (auto& [match_name, match_def] :
       *table_def.mutable_match_fields_by_name()) {
    SetCompositeUdfFieldFormatToHexString(match_def);
  }
}

}  // namespace

absl::StatusOr<std::string> TranslatePort(
    TranslationDirection direction,
    const boost::bimap<std::string, std::string>& port_map,
    const std::string& port_key) {
  switch (direction) {
    case TranslationDirection::kForController: {
      auto value = port_map.left.find(port_key);
      if (value == port_map.left.end()) {
        return gutil::InvalidArgumentErrorBuilder()
               << "[P4RT App] Cannot translate port '"
               << absl::CHexEscape(port_key)
               << "' to P4RT ID. Has the port been configured with an ID?";
      }
      return value->second;
    }
    case TranslationDirection::kForOrchAgent: {
      auto value = port_map.right.find(port_key);
      if (value == port_map.right.end()) {
        return gutil::InvalidArgumentErrorBuilder()
               << "[P4RT App] Cannot translate port '"
               << absl::CHexEscape(port_key)
               << "' to SONiC name. Has the port been configured with an ID?";
      }
      return value->second;
    }
  }
  return gutil::InternalErrorBuilder() << "Could not translate port because "
                                          "unsupported direction was selected.";
}

absl::Status TranslateTableEntry(const TranslateTableEntryOptions& options,
                                 pdpi::IrTableEntry& entry) {
  // Get the IR table definition for the table entry.
  const pdpi::IrTableDefinition* ir_table_def = gutil::FindOrNull(
      options.ir_p4_info.tables_by_name(), entry.table_name());
  if (ir_table_def == nullptr) {
    return gutil::InternalErrorBuilder()
           << "Could not find table definition for " << entry.table_name()
           << ".";
  }

  // Handle match fields.
  for (auto& match : *entry.mutable_matches()) {
    RETURN_IF_ERROR(TranslateMatchField(options, *ir_table_def, match));
  }

  // Handle both a single action, and a action set.
  if (entry.has_action()) {
    RETURN_IF_ERROR(
        TranslateAction(options, *ir_table_def, *entry.mutable_action()));
  } else if (entry.has_action_set()) {
    RETURN_IF_ERROR(TranslateActionSet(options, *ir_table_def,
                                       *entry.mutable_action_set()));
  }

  return absl::OkStatus();
}

void TranslateIrP4InfoForOrchAgent(pdpi::IrP4Info& p4_info) {
  for (auto& [table_id, table_def] : *p4_info.mutable_tables_by_id()) {
    TranslateIrTableDefForOrchAgent(table_def);
  }
  for (auto& [table_id, table_def] : *p4_info.mutable_tables_by_name()) {
    TranslateIrTableDefForOrchAgent(table_def);
  }
}

// TODO: Remove this when P4Info uses 64-bit IPv6 ACL match fields.
void Convert64BitIpv6AclMatchFieldsTo128Bit(
    pdpi::IrTableEntry& ir_table_entry) {
  for (pdpi::IrMatch& match : *ir_table_entry.mutable_matches()) {
    if (!match.has_ternary()) continue;
    if (match.ternary().value().format_case() !=
        pdpi::IrValue::FormatCase::kIpv6) {
      continue;
    }

    const std::string& value = match.ternary().value().ipv6();
    auto value_address = netaddr::Ipv6Address::OfString(value);
    if (!value_address.ok()) {
      LOG(WARNING) << "Unexpected unconvertable IPv6 value: " << value;
      continue;
    }
    const std::string& mask = match.ternary().mask().ipv6();
    auto mask_address = netaddr::Ipv6Address::OfString(mask);
    if (!mask_address.ok()) {
      LOG(WARNING) << "Unexpected unconvertable IPv6 mask: " << mask;
      continue;
    }
    // If none of the upper 64-bits are set, we assume that the address has
    // mistakenly been shifted rightward by 64-bits. Shift the address left
    // 64-bit to correct. This logic supports controller/switch mismatch when
    // transitioning to 64-bit IPv6 match fields at the expense of being able to
    // create lower 64-bit matches.
    if (*mask_address ==
        (*mask_address & ~netaddr::Ipv6Address::Upper64BitMask())) {
      match.mutable_ternary()->mutable_value()->set_ipv6(
          (*value_address << 64).ToString());
      match.mutable_ternary()->mutable_mask()->set_ipv6(
          (*mask_address << 64).ToString());
    }
  }
}

}  // namespace p4rt_app
