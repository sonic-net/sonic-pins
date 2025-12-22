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
#include "p4rt_app/p4runtime/p4runtime_read.h"

#include <string>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_format.h"
#include "boost/bimap.hpp"
#include "gutil/status.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/entity_keys.h"
#include "p4_pdpi/ir.pb.h"
#include "p4rt_app/p4runtime/ir_translation.h"
#include "p4rt_app/p4runtime/queue_translator.h"
#include "p4rt_app/sonic/app_db_manager.h"
#include "p4rt_app/sonic/redis_connections.h"
#include "p4rt_app/utils/table_utility.h"

namespace p4rt_app {
namespace {

absl::Status SupportedTableEntryRequest(const p4::v1::TableEntry& table_entry) {
  if (table_entry.table_id() != 0 || !table_entry.match().empty() ||
      table_entry.priority() != 0 || !table_entry.metadata().empty() ||
      table_entry.has_action() || table_entry.is_default_action() != false) {
    return gutil::UnimplementedErrorBuilder()
           << "Read request for table entry: "
           << table_entry.ShortDebugString();
  }
  return absl::OkStatus();
}

absl::Status SupportedPacketReplicationEntryRequest(
    const p4::v1::PacketReplicationEngineEntry& replication_entry) {
  if (replication_entry.clone_session_entry().session_id() != 0 ||
      !replication_entry.clone_session_entry().replicas().empty()) {
    return gutil::UnimplementedErrorBuilder()
           << "Read request for packet_replication_engine_entry's "
              "clone_session_entry is not empty: "
           << replication_entry.ShortDebugString();
  }
  if (replication_entry.multicast_group_entry().multicast_group_id() != 0 ||
      !replication_entry.multicast_group_entry().replicas().empty()) {
    return gutil::UnimplementedErrorBuilder()
	    << "Read request for packet_replication_engine_entry's "
              "multicast_group_entry is not empty: "
           << replication_entry.ShortDebugString();
  }
  return absl::OkStatus();
}

absl::Status AppendAclCounterData(
    p4::v1::TableEntry& pi_table_entry, const pdpi::IrP4Info& ir_p4_info,
    bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map,
    const QueueTranslator& cpu_queue_translator,
    const QueueTranslator& front_panel_queue_translator,
    sonic::P4rtTable& p4rt_table) {
  ASSIGN_OR_RETURN(
      pdpi::IrTableEntry ir_table_entry,
      TranslatePiTableEntryForOrchAgent(
          pi_table_entry, ir_p4_info, translate_port_ids, port_translation_map,
          cpu_queue_translator, front_panel_queue_translator,
          /*translate_key_only=*/false));

  RETURN_IF_ERROR(sonic::AppendCounterDataForTableEntry(
      ir_table_entry, p4rt_table, ir_p4_info));
  if (ir_table_entry.has_counter_data()) {
    *pi_table_entry.mutable_counter_data() = ir_table_entry.counter_data();
  }
  if (ir_table_entry.has_meter_counter_data()) {
    *pi_table_entry.mutable_meter_counter_data() =
        ir_table_entry.meter_counter_data();
  }

  return absl::OkStatus();
}

absl::Status AppendTableEntryReads(
    p4::v1::ReadResponse& response, const p4::v1::TableEntry& cached_entry,
    const std::string& role_name, const pdpi::IrP4Info& ir_p4_info,
    bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map,
    const QueueTranslator& cpu_queue_translator,
    const QueueTranslator& front_panel_queue_translator,
    sonic::P4rtTable& p4rt_table) {
  // Fetch the table definition since it will inform how we process the read
  // request.
  auto table_def = ir_p4_info.tables_by_id().find(cached_entry.table_id());
  if (table_def == ir_p4_info.tables_by_id().end()) {
    return gutil::InternalErrorBuilder() << absl::StreamFormat(
               "Could not find table ID %u when checking role access. Did an "
               "IR translation fail somewhere?",
               cached_entry.table_id());
  }

  // Multiple roles can be connected to a switch so we need to ensure the
  // reader has access to the table. Otherwise, we just ignore reporting it.
  if (!role_name.empty() && table_def->second.role() != role_name) {
    VLOG(2) << absl::StreamFormat(
        "Role '%s' is not allowed access to table '%s'.", role_name,
        table_def->second.preamble().name());
    return absl::OkStatus();
  }

  // Update the response to include the table entry.
  p4::v1::TableEntry* response_entry =
      response.add_entities()->mutable_table_entry();
  *response_entry = cached_entry;

  // For ACL tables we need to check for counter/meter data, and append it as
  // needed.
  ASSIGN_OR_RETURN(table::Type table_type, GetTableType(table_def->second),
                   _ << "Could not determine table type for table '"
                     << table_def->second.preamble().name() << "'.");
  if (table_type == table::Type::kAcl) {
    RETURN_IF_ERROR(AppendAclCounterData(
        *response_entry, ir_p4_info, translate_port_ids, port_translation_map,
        cpu_queue_translator, front_panel_queue_translator, p4rt_table));
  }

  return absl::OkStatus();
}

absl::Status AppendPacketReplicationEntryReads(
    p4::v1::ReadResponse& response, const p4::v1::Entity& cached_entry) {
  // Update the response to include the packet replication entry.
  *response.add_entities() = cached_entry;
  return absl::OkStatus();
}

}  // namespace

absl::StatusOr<std::vector<p4::v1::ReadResponse>> ReadAllEntitiesInBatches(
    int batch_size, const p4::v1::ReadRequest& request,
    const pdpi::IrP4Info& ir_p4_info,
    const absl::flat_hash_map<pdpi::EntityKey, p4::v1::Entity>& entity_cache,
    bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map,
    QueueTranslator& cpu_queue_translator,
    QueueTranslator& front_panel_queue_translator,
    sonic::P4rtTable& p4rt_table) {
  std::vector<p4::v1::ReadResponse> responses;
  responses.push_back(p4::v1::ReadResponse{});
  for (const auto& entity : request.entities()) {
    VLOG(1) << "Read request: " << entity.ShortDebugString();
    switch (entity.entity_case()) {
      case p4::v1::Entity::kTableEntry: {
        RETURN_IF_ERROR(SupportedTableEntryRequest(entity.table_entry()));
        for (const auto& [_, entry] : entity_cache) {
          if (entry.entity_case() == p4::v1::Entity::kTableEntry) {
            RETURN_IF_ERROR(AppendTableEntryReads(
                responses.back(), entry.table_entry(), request.role(),
                ir_p4_info, translate_port_ids, port_translation_map,
                cpu_queue_translator, front_panel_queue_translator,
                p4rt_table));
            if (responses.size() >= batch_size) {
              responses.push_back(p4::v1::ReadResponse{});
            }
          }
        }
        break;
      }
      case p4::v1::Entity::kPacketReplicationEngineEntry: {
        RETURN_IF_ERROR(SupportedPacketReplicationEntryRequest(
            entity.packet_replication_engine_entry()));
        for (const auto& [_, entry] : entity_cache) {
          if (entry.entity_case() ==
		  p4::v1::Entity::kPacketReplicationEngineEntry &&
              (entity.packet_replication_engine_entry().type_case() ==
                   entry.packet_replication_engine_entry().type_case() ||
               entity.packet_replication_engine_entry().type_case() ==
                   p4::v1::PacketReplicationEngineEntry::TYPE_NOT_SET)) {
            RETURN_IF_ERROR(
                AppendPacketReplicationEntryReads(responses.back(), entry));
            if (responses.size() >= batch_size) {
              responses.push_back(p4::v1::ReadResponse{});
            }
          }
        }
        break;
      }
      default:
        return gutil::UnimplementedErrorBuilder()
               << "Read has not been implemented for: "
               << entity.ShortDebugString();
    }
  }
  if (responses.size() > 1 && responses.back().entities().empty()) {
    responses.pop_back();
  }
  return responses;
}

}  // namespace p4rt_app
