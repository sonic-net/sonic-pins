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

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_format.h"
#include "boost/bimap.hpp"
#include "glog/logging.h"
#include "gutil/status.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/entity_keys.h"
#include "p4_pdpi/ir.pb.h"
#include "p4rt_app/p4runtime/cpu_queue_translator.h"
#include "p4rt_app/p4runtime/ir_translation.h"
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

absl::Status AppendAclCounterData(
    p4::v1::TableEntry& pi_table_entry, const pdpi::IrP4Info& ir_p4_info,
    bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map,
    const CpuQueueTranslator& cpu_queue_translator,
    sonic::P4rtTable& p4rt_table) {
  ASSIGN_OR_RETURN(pdpi::IrTableEntry ir_table_entry,
                   TranslatePiTableEntryForOrchAgent(
                       pi_table_entry, ir_p4_info, translate_port_ids,
                       port_translation_map, cpu_queue_translator,
                       /*translate_key_only=*/false));

  RETURN_IF_ERROR(sonic::AppendCounterDataForTableEntry(
      ir_table_entry, p4rt_table, ir_p4_info));
  if (ir_table_entry.has_counter_data()) {
    *pi_table_entry.mutable_counter_data() = ir_table_entry.counter_data();
  }

  return absl::OkStatus();
}

absl::Status AppendTableEntryReads(
    p4::v1::ReadResponse& response, const p4::v1::TableEntry& cached_entry,
    const std::string& role_name, const pdpi::IrP4Info& ir_p4_info,
    bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map,
    const CpuQueueTranslator& cpu_queue_translator,
    sonic::P4rtTable& p4rt_table) {
  // Fetch the table defintion since it will inform how we process the read
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
        cpu_queue_translator, p4rt_table));
  }

  return absl::OkStatus();
}

}  // namespace

absl::StatusOr<p4::v1::ReadResponse> ReadAllTableEntries(
    const p4::v1::ReadRequest& request, const pdpi::IrP4Info& ir_p4_info,
    const absl::flat_hash_map<pdpi::TableEntryKey, p4::v1::TableEntry>&
        table_entry_cache,
    bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map,
    CpuQueueTranslator& cpu_queue_translator, sonic::P4rtTable& p4rt_table) {
  p4::v1::ReadResponse response;
  for (const auto& entity : request.entities()) {
    VLOG(1) << "Read request: " << entity.ShortDebugString();
    switch (entity.entity_case()) {
      case p4::v1::Entity::kTableEntry: {
        RETURN_IF_ERROR(SupportedTableEntryRequest(entity.table_entry()));
        for (const auto& [_, entry] : table_entry_cache) {
          RETURN_IF_ERROR(AppendTableEntryReads(
              response, entry, request.role(), ir_p4_info, translate_port_ids,
              port_translation_map, cpu_queue_translator, p4rt_table));
        }
        break;
      }
      default:
        return gutil::UnimplementedErrorBuilder()
               << "Read has not been implemented for: "
               << entity.ShortDebugString();
    }
  }
  return response;
}

}  // namespace p4rt_app
