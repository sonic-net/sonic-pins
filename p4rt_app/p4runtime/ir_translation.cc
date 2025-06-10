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

#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/escaping.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_format.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/status.h"
#include "p4/config/v1/p4types.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/netaddr/ipv6_address.h"
#include "p4_infra/p4_pdpi/annotation_parser.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/translation_options.h"
#include "p4rt_app/p4runtime/queue_translator.h"
#include "utf8_validity.h"

namespace p4rt_app {
namespace {

bool IsPortType(const p4::config::v1::P4NamedType& type) {
  return type.name() == "port_id_t";
}

bool IsCpuQueue(const p4::config::v1::P4NamedType& type) {
  return type.name() == "qos_queue_t" || type.name() == "cpu_queue_t";
}

bool IsFrontPanelQueue(const p4::config::v1::P4NamedType& type) {
  return type.name() == "unicast_queue_t" || type.name() == "multicast_queue_t";
}

absl::Status TranslatePortValue(
    TranslationDirection direction,
    const boost::bimap<std::string, std::string>& port_map,
    pdpi::IrValue& value) {
  if (value.format_case() != pdpi::IrValue::kStr) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Port value must use Format::STRING, but found "
           << value.format_case() << " instead.";
  }
  ASSIGN_OR_RETURN(*value.mutable_str(),
                   TranslatePort(direction, port_map, value.str()));
  return absl::OkStatus();
}

// Optionally translates a queue between queue name and queue ID syntax.
absl::Status OptionallyTranslateQueue(TranslationDirection direction,
                                      const QueueTranslator& translator,
                                      pdpi::IrValue& value) {
  if (value.format_case() != pdpi::IrValue::kStr) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Queue must use Format::STRING, but found " << value.format_case()
           << " instead.";
  }
  switch (direction) {
    case TranslationDirection::kForController: {
      int queue_id;
      if (!absl::SimpleHexAtoi(value.str(), &queue_id)) {
        return gutil::InvalidArgumentErrorBuilder()
               << "Expected AppDB queue as hex string. Got '" << value.str()
               << "'.";
      }
      auto queue_name = translator.IdToName(queue_id);
      if (queue_name.ok()) value.set_str(*queue_name);
      return absl::OkStatus();
    }
    case TranslationDirection::kForOrchAgent: {
      value.set_str(
          translator.OptionallyTranslateNameToIdInHexString(value.str()));
      return absl::OkStatus();
    }
  }
  // Should never be hit.
  return gutil::InternalErrorBuilder()
         << "Invalid TranslationDirection provided.";
}

absl::Status TranslateAction(const TranslateTableEntryOptions& options,
                             const pdpi::IrTableDefinition& table_def,
                             pdpi::IrActionInvocation& action) {
  // Find the action definition from the ir table definition.
  const pdpi::IrActionDefinition* action_def = nullptr;
  for (const auto& entry_action : table_def.entry_actions()) {
    if (entry_action.action().preamble().alias() == action.name()) {
      action_def = &entry_action.action();
      break;
    }
  }
  if (action_def == nullptr) {
    return gutil::InternalErrorBuilder()
           << "Could not find action definition for " << action.name() << ".";
  }

  for (auto& param : *action.mutable_params()) {
    // If the parameter field isn't a port then ignore it.
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
      continue;
    }

    if (IsCpuQueue(param_def->param().type_name())) {
      RETURN_IF_ERROR(OptionallyTranslateQueue(options.direction,
                                               options.cpu_queue_translator,
                                               *param.mutable_value()));
    } else if (IsFrontPanelQueue(param_def->param().type_name())) {
      RETURN_IF_ERROR(OptionallyTranslateQueue(
          options.direction, options.front_panel_queue_translator,
          *param.mutable_value()));
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

absl::Status TranslatePortInReplica(const TranslateTableEntryOptions& options,
                                    pdpi::IrReplica& replica) {
  if (options.translate_port_ids) {
    ASSIGN_OR_RETURN(
        *replica.mutable_port(),
        TranslatePort(options.direction, options.port_map, replica.port()));
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
  if (!utf8_range::IsStructurallyValid(port_key)) {
    return gutil::InvalidArgumentErrorBuilder() << "Invalid UTF-8 string";
  }
  switch (direction) {
    case TranslationDirection::kForController: {
      auto value = port_map.left.find(port_key);
      if (value == port_map.left.end()) {
        return gutil::InvalidArgumentErrorBuilder().LogError()
               << "[P4RT App] Cannot translate port '"
               << absl::CHexEscape(port_key)
               << "' to P4RT ID. Has the port been configured with an ID?";
      }
      return value->second;
    }
    case TranslationDirection::kForOrchAgent: {
      auto value = port_map.right.find(port_key);
      if (value == port_map.right.end()) {
        return gutil::InvalidArgumentErrorBuilder().LogError()
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

absl::Status TranslatePacketReplicationEntry(
    const TranslateTableEntryOptions& options,
    pdpi::IrPacketReplicationEngineEntry& entry) {
  // Update ports in each replica.
  for (auto& replica :
       *entry.mutable_multicast_group_entry()->mutable_replicas()) {
    RETURN_IF_ERROR(TranslatePortInReplica(options, replica));
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

absl::StatusOr<pdpi::IrEntity> TranslatePiEntityForOrchAgent(
    const p4::v1::Entity& pi_entity, const pdpi::IrP4Info& ir_p4_info,
    bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map,
    const QueueTranslator& cpu_queue_translator,
    const QueueTranslator& front_panel_queue_translator,
    bool translate_key_only) {
  pdpi::IrEntity ir_entity;
  switch (pi_entity.entity_case()) {
    case p4::v1::Entity::kTableEntry: {
      ASSIGN_OR_RETURN(
          *ir_entity.mutable_table_entry(),
          TranslatePiTableEntryForOrchAgent(
              pi_entity.table_entry(), ir_p4_info, translate_port_ids,
              port_translation_map, cpu_queue_translator,
              front_panel_queue_translator, translate_key_only));
      break;
    }
    case p4::v1::Entity::kPacketReplicationEngineEntry: {
      ASSIGN_OR_RETURN(
          *ir_entity.mutable_packet_replication_engine_entry(),
          TranslatePiPacketReplicationEngineEntryForOrchAgent(
              pi_entity.packet_replication_engine_entry(), ir_p4_info,
              translate_port_ids, port_translation_map, cpu_queue_translator,
              front_panel_queue_translator, translate_key_only));
      break;
    }
    default: {
      ASSIGN_OR_RETURN(ir_entity,
                       pdpi::PiEntityToIr(ir_p4_info, pi_entity,
                                          pdpi::TranslationOptions{
                                              .key_only = translate_key_only,
                                          }));
    }
  }
  return ir_entity;
}

absl::StatusOr<pdpi::IrTableEntry> TranslatePiTableEntryForOrchAgent(
    const p4::v1::TableEntry& pi_table_entry, const pdpi::IrP4Info& ir_p4_info,
    bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map,
    const QueueTranslator& cpu_queue_translator,
    const QueueTranslator& front_panel_queue_translator,
    bool translate_key_only) {
  auto ir_table_entry =
      pdpi::PiTableEntryToIr(ir_p4_info, pi_table_entry,
                             pdpi::TranslationOptions{
                                 .key_only = translate_key_only,
                             });
  if (!ir_table_entry.ok()) {
    LOG(ERROR) << "PDPI could not translate PI table entry to IR: "
               << pi_table_entry.ShortDebugString();
    return gutil::StatusBuilder(ir_table_entry.status().code())
           << "[P4RT/PDPI] " << ir_table_entry.status().message();
  }

  RETURN_IF_ERROR(UpdateIrTableEntryForOrchAgent(
      *ir_table_entry, ir_p4_info, translate_port_ids, port_translation_map,
      cpu_queue_translator, front_panel_queue_translator));
  return *ir_table_entry;
}

absl::StatusOr<pdpi::IrPacketReplicationEngineEntry>
TranslatePiPacketReplicationEngineEntryForOrchAgent(
    const p4::v1::PacketReplicationEngineEntry& pi_packet_replication_entry,
    const pdpi::IrP4Info& ir_p4_info, bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map,
    const QueueTranslator& cpu_queue_translator,
    const QueueTranslator& front_panel_queue_translator,
    bool translate_key_only) {
  auto ir_packet_replication_engine_entry =
      pdpi::PiPacketReplicationEngineEntryToIr(
          ir_p4_info, pi_packet_replication_entry,
          pdpi::TranslationOptions{
              .key_only = translate_key_only,
          });
  if (!ir_packet_replication_engine_entry.ok()) {
    LOG(ERROR) << "PDPI could not translate PI packet replication entry to IR: "
               << pi_packet_replication_entry.ShortDebugString();
    return gutil::StatusBuilder(
               ir_packet_replication_engine_entry.status().code())
           << "[P4RT/PDPI] "
           << ir_packet_replication_engine_entry.status().message();
  }
  RETURN_IF_ERROR(UpdateIrPacketReplicationEngineEntryForOrchAgent(
      *ir_packet_replication_engine_entry, ir_p4_info, translate_port_ids,
      port_translation_map, cpu_queue_translator,
      front_panel_queue_translator));
  return *ir_packet_replication_engine_entry;
}

absl::Status UpdateIrEntityForOrchAgent(
    pdpi::IrEntity& ir_entity, const pdpi::IrP4Info& ir_p4_info,
    bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map,
    const QueueTranslator& cpu_queue_translator,
    const QueueTranslator& front_panel_queue_translator) {
  switch (ir_entity.entity_case()) {
    case pdpi::IrEntity::kTableEntry:
      RETURN_IF_ERROR(UpdateIrTableEntryForOrchAgent(
          *ir_entity.mutable_table_entry(), ir_p4_info, translate_port_ids,
          port_translation_map, cpu_queue_translator,
          front_panel_queue_translator));
      break;
    case pdpi::IrEntity::kPacketReplicationEngineEntry:
      RETURN_IF_ERROR(UpdateIrPacketReplicationEngineEntryForOrchAgent(
          *ir_entity.mutable_packet_replication_engine_entry(), ir_p4_info,
          translate_port_ids, port_translation_map, cpu_queue_translator,
          front_panel_queue_translator));
      break;
    default:
      return gutil::InvalidArgumentErrorBuilder()
             << "[P4RT App] Cannot update IR entity for unsupported type: "
             << ir_entity.ShortDebugString();
      break;
  }
  return absl::OkStatus();
}

absl::Status UpdateIrTableEntryForOrchAgent(
    pdpi::IrTableEntry& ir_table_entry, const pdpi::IrP4Info& ir_p4_info,
    bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map,
    const QueueTranslator& cpu_queue_translator,
    const QueueTranslator& front_panel_queue_translator) {
  // TODO: Remove this when P4Info uses 64-bit IPv6 ACL matchess.
  // We don't allow overwriting of the p4info, so static is ok here.

  Convert64BitIpv6AclMatchFieldsTo128Bit(ir_table_entry);
  RETURN_IF_ERROR(TranslateTableEntry(
      TranslateTableEntryOptions{
          .direction = TranslationDirection::kForOrchAgent,
          .ir_p4_info = ir_p4_info,
          .translate_port_ids = translate_port_ids,
          .port_map = port_translation_map,
          .cpu_queue_translator = cpu_queue_translator,
          .front_panel_queue_translator = front_panel_queue_translator,
      },
      ir_table_entry));
  return absl::OkStatus();
}

absl::Status UpdateIrPacketReplicationEngineEntryForOrchAgent(
    pdpi::IrPacketReplicationEngineEntry& ir_packet_replication_entry,
    const pdpi::IrP4Info& ir_p4_info, bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map,
    const QueueTranslator& cpu_queue_translator,
    const QueueTranslator& front_panel_queue_translator) {
  RETURN_IF_ERROR(TranslatePacketReplicationEntry(
      TranslateTableEntryOptions{
          .direction = TranslationDirection::kForOrchAgent,
          .ir_p4_info = ir_p4_info,
          .translate_port_ids = translate_port_ids,
          .port_map = port_translation_map,
          .cpu_queue_translator = cpu_queue_translator,
          .front_panel_queue_translator = front_panel_queue_translator,
      },
      ir_packet_replication_entry));
  return absl::OkStatus();
}

}  // namespace p4rt_app
