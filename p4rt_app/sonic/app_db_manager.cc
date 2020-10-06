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
#include "p4rt_app/sonic/app_db_manager.h"

#include <memory>
#include <type_traits>
#include <unordered_map>
#include <utility>

#include "absl/container/btree_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_split.h"
#include "boost/bimap.hpp"
#include "glog/logging.h"
#include "gutil/collections.h"
#include "gutil/status.h"
#include "p4_pdpi/ir.pb.h"
#include "p4rt_app/sonic/app_db_to_pdpi_ir_translator.h"
#include "p4rt_app/sonic/response_handler.h"
#include "p4rt_app/sonic/vrf_entry_translation.h"
#include "p4rt_app/utils/status_utility.h"
#include "p4rt_app/utils/table_utility.h"
#include "swss/consumernotifierinterface.h"
#include "swss/dbconnectorinterface.h"
#include "swss/json.h"
#include "swss/json.hpp"
#include "swss/producerstatetableinterface.h"

namespace p4rt_app {
namespace sonic {
namespace {

absl::StatusOr<std::string> GetP4rtTableKey(const pdpi::IrTableEntry& entry,
                                            const pdpi::IrP4Info& p4_info) {
  // Determine the table type.
  const pdpi::IrTableDefinition* ir_table_def =
      gutil::FindOrNull(p4_info.tables_by_name(), entry.table_name());
  if (ir_table_def == nullptr) {
    return gutil::InternalErrorBuilder()
           << "Table name '" << entry.table_name() << "' does not exist";
  }
  ASSIGN_OR_RETURN(auto table_type, GetTableType(*ir_table_def));

  // Determine the AppDb match key.
  ASSIGN_OR_RETURN(const std::string json_key, IrTableEntryToAppDbKey(entry));

  // The final AppDb Key format is: <table_type>_<table_name>:<json_key>
  return absl::StrCat(
      absl::AsciiStrToUpper(absl::Substitute(
          "$0_$1:", table::TypeName(table_type), entry.table_name())),
      json_key);
}

absl::flat_hash_set<std::string> FindDuplicateKeys(
    const AppDbUpdates& updates, const pdpi::IrP4Info& p4_info) {
  absl::flat_hash_set<std::string> duplicates;
  absl::flat_hash_set<std::string> keys;

  for (const auto& entry : updates.entries) {
    auto key = GetP4rtTableKey(entry.entry, p4_info);
    if (key.ok()) {
      if (keys.count(*key) > 0) duplicates.insert(*key);
      keys.insert(*key);
    }
  }

  return duplicates;
}

// Validates the AppDb entry to be deleted and updates the p4rt_deletes (to be
// deleted in a batch later). On success the P4RT key to be deleted is returned.
absl::StatusOr<std::string> CreateEntryForAppDbDelete(
    const pdpi::IrTableEntry& entry, const pdpi::IrP4Info& p4_info,
    const absl::flat_hash_set<std::string>& duplicate_keys,
    std::vector<std::string>& p4rt_deletes,
    swss::ProducerStateTableInterface& p4rt_table,
    swss::DBConnectorInterface& app_db_client) {
  LOG(INFO) << "Delete PDPI IR entry: " << entry.ShortDebugString();

  ASSIGN_OR_RETURN(std::string key, GetP4rtTableKey(entry, p4_info));

  // Verify key has not been duplicated in this batch request.
  if (duplicate_keys.count(key) > 0) {
    return gutil::InvalidArgumentErrorBuilder()
           << "[P4RT App] Found duplicated key in the same batch request.";
  }

  std::string p4rt_prefix_key =
      absl::StrCat(p4rt_table.get_table_name(), ":", key);
  // Check that key exists in the table.
  if (!app_db_client.exists(p4rt_prefix_key)) {
    LOG(WARNING) << "Could not delete missing entry: " << key;
    return gutil::NotFoundErrorBuilder()
           << "[P4RT App] Table entry with the given key does not exist in '"
           << entry.table_name() << "'.";
  }

  // Get table entry from the APP_DB (before delete) instead of the one from the
  // request.
  ASSIGN_OR_RETURN(
      auto ir_table_entry,
      AppDbKeyAndValuesToIrTableEntry(p4_info, p4rt_prefix_key,
                                      app_db_client.hgetall(p4rt_prefix_key)));

  LOG(INFO) << "Delete AppDb entry: " << key;
  p4rt_deletes.push_back(key);
  return key;
}

// Formats the IR entry as a AppDb entry and updates the p4rt_inserts (to be
// inserted in a batch later). On success the P4RT key is returned.
absl::StatusOr<std::string> CreateEntryForAppDbInsert(
    const pdpi::IrTableEntry& entry, const pdpi::IrP4Info& p4_info,
    const absl::flat_hash_set<std::string>& duplicate_keys,
    std::vector<swss::KeyOpFieldsValuesTuple>& p4rt_inserts,
    swss::ProducerStateTableInterface& p4rt_table,
    swss::DBConnectorInterface& app_db_client,
    swss::DBConnectorInterface& state_db_client) {
  LOG(INFO) << "Insert PDPI IR entry: " << entry.ShortDebugString();

  ASSIGN_OR_RETURN(std::string key, GetP4rtTableKey(entry, p4_info));

  // Verify key has not been duplicated in this batch request.
  if (duplicate_keys.count(key) > 0) {
    return gutil::InvalidArgumentErrorBuilder()
           << "[P4RT App] Found duplicated key in the same batch request.";
  }

  // Check that key does not already exist in the table.
  if (app_db_client.exists(
          absl::StrCat(p4rt_table.get_table_name(), ":", key))) {
    LOG(WARNING) << "Could not insert duplicate entry: " << key;
    return gutil::AlreadyExistsErrorBuilder()
           << "[P4RT App] Table entry with the given key already exist in '"
           << entry.table_name() << "'.";
  }

  LOG(INFO) << "Insert AppDb entry: " << key;
  swss::KeyOpFieldsValuesTuple key_value;
  kfvKey(key_value) = key;
  ASSIGN_OR_RETURN(kfvFieldsValues(key_value),
                   IrTableEntryToAppDbValues(entry));
  p4rt_inserts.push_back(std::move(key_value));
  return key;
}

// Formats the IR entry as a AppDb entry and updates the p4rt_modifies (to be
// modified in a batch later). On success the P4RT key is returned.
absl::StatusOr<std::string> CreateEntryForAppDbModify(
    const pdpi::IrTableEntry& entry, const pdpi::IrP4Info& p4_info,
    const absl::flat_hash_set<std::string>& duplicate_keys,
    std::vector<swss::KeyOpFieldsValuesTuple>& p4rt_modifies,
    swss::ProducerStateTableInterface& p4rt_table,
    swss::DBConnectorInterface& app_db_client,
    swss::DBConnectorInterface& state_db_client) {
  LOG(INFO) << "Modify PDPI IR entry: " << entry.ShortDebugString();

  ASSIGN_OR_RETURN(std::string key, GetP4rtTableKey(entry, p4_info));

  std::string app_db_key = absl::StrCat(p4rt_table.get_table_name(), ":", key);
  // Verify key has not been duplicated in this batch request.
  if (duplicate_keys.count(key) > 0) {
    return gutil::InvalidArgumentErrorBuilder()
           << "[P4RT App] Found duplicated key in the same batch request.";
  }

  // Check that key already exist in the table.
  if (!app_db_client.exists(app_db_key)) {
    LOG(WARNING) << "Could not modify missing entry: " << key;
    return gutil::NotFoundErrorBuilder()
           << "[P4RT App] Table entry with the given key does not exist in '"
           << entry.table_name() << "'.";
  }

  LOG(INFO) << "Modify AppDb entry: " << key;
  swss::KeyOpFieldsValuesTuple key_value;
  kfvKey(key_value) = key;
  ASSIGN_OR_RETURN(kfvFieldsValues(key_value),
                   IrTableEntryToAppDbValues(entry));
  p4rt_modifies.push_back(std::move(key_value));
  return key;
}

absl::Status AppendCounterData(
    pdpi::IrTableEntry& table_entry,
    const std::unordered_map<std::string, std::string>& counter_data) {
  // Update packet count only if data is present.
  if (auto packets_iter = counter_data.find("packets");
      packets_iter != counter_data.end()) {
    uint64_t packets = 0;
    if (absl::SimpleAtoi(packets_iter->second, &packets)) {
      table_entry.mutable_counter_data()->set_packet_count(packets);
    } else {
      LOG(ERROR) << "Unexpected packets value '" << packets_iter->second
                 << "' in CountersDB for table entry: "
                 << table_entry.ShortDebugString();
    }
  }

  // Update byte count only if data is present.
  if (auto bytes_iter = counter_data.find("bytes");
      bytes_iter != counter_data.end()) {
    uint64_t bytes = 0;
    if (absl::SimpleAtoi(bytes_iter->second, &bytes)) {
      table_entry.mutable_counter_data()->set_byte_count(bytes);
    } else {
      LOG(ERROR) << "Unexpected bytes value '" << bytes_iter->second
                 << "' in CountersDB for table entry: "
                 << table_entry.ShortDebugString();
    }
  }
  return absl::OkStatus();
}

// Writes into the APP_DB Producer Table using the bulk option.
void WriteBatchToAppDb(
    const std::vector<swss::KeyOpFieldsValuesTuple>& p4rt_inserts,
    const std::vector<swss::KeyOpFieldsValuesTuple>& p4rt_modifies,
    const std::vector<std::string>& p4rt_deletes,
    swss::DBConnectorInterface& app_db_client,
    swss::ProducerStateTableInterface& p4rt_table) {
  if (!p4rt_inserts.empty()) p4rt_table.set(p4rt_inserts);

  if (!p4rt_modifies.empty()) {
    std::vector<std::string> del_keys(p4rt_modifies.size());
    for (const auto& key_value : p4rt_modifies) {
      del_keys.push_back(
          absl::StrCat(p4rt_table.get_table_name(), ":", kfvKey(key_value)));
    }
    // On modify we need to first remove the existing entries to get rid of any
    // action paramters that may be replaced with a new action. Doing this
    // through the app_db_client will not invoke an action in the OrchAgent.
    app_db_client.del(del_keys);

    // Then we re-insert the entries through the ProducerStateTable which will
    // inoke an update action in the OrchAgent.
    p4rt_table.set(p4rt_modifies);
  }

  if (!p4rt_deletes.empty()) p4rt_table.del(p4rt_deletes);
}

}  // namespace

absl::StatusOr<pdpi::IrTableEntry> ReadAppDbP4TableEntry(
    const pdpi::IrP4Info& p4info, swss::DBConnectorInterface& app_db_client,
    swss::DBConnectorInterface& counters_db_client, const std::string& key) {
  VLOG(1) << "Read AppDb entry: " << key;
  ASSIGN_OR_RETURN(
      pdpi::IrTableEntry table_entry,
      AppDbKeyAndValuesToIrTableEntry(p4info, key, app_db_client.hgetall(key)));

  RETURN_IF_ERROR(AppendCounterData(
      table_entry, counters_db_client.hgetall(absl::StrCat("COUNTERS:", key))));
  return table_entry;
}

std::vector<std::string> GetAllAppDbP4TableEntryKeys(
    swss::DBConnectorInterface& app_db_client) {
  std::vector<std::string> p4rt_keys;

  for (const auto& key : app_db_client.keys("*")) {
    const std::vector<std::string> split = absl::StrSplit(key, ':');
    if (split.size() < 2) continue;

    // The P4RT table entries will either start with "_P4RT" (if orchagent has
    // not installed the entry) or "P4RT" (if orchagent has installed the
    // entry). When getting the P4 table entries we are only concerned with what
    // orchagent has installed.
    if (split[0] != "P4RT") continue;

    // The P4RT:DEFINITION table does not hold any P4RT entries, and should also
    // be ignored.
    if (split[1] == "DEFINITION") continue;

    p4rt_keys.push_back(key);
  }
  return p4rt_keys;
}

absl::Status UpdateAppDb(const AppDbUpdates& updates,
                         const pdpi::IrP4Info& p4_info,
                         swss::ProducerStateTableInterface& p4rt_table,
                         swss::ConsumerNotifierInterface& p4rt_notification,
                         swss::DBConnectorInterface& app_db_client,
                         swss::DBConnectorInterface& state_db_client,
                         swss::ProducerStateTableInterface& vrf_table,
                         swss::ConsumerNotifierInterface& vrf_notification,
                         pdpi::IrWriteResponse* response) {
  // We keep a temporary cache of any keys that are duplicated in the batch
  // request so the flow can be rejected.
  absl::flat_hash_set<std::string> duplicate_keys =
      FindDuplicateKeys(updates, p4_info);

  // We break the requests up by type (i.e. INSERT/MODIFY/DELETE), but P4Runtime
  // error reporting requires the response ordering to match the request
  // ordering. So we keep a mapping of the statuses.
  std::vector<swss::KeyOpFieldsValuesTuple> p4rt_inserts;
  std::vector<swss::KeyOpFieldsValuesTuple> p4rt_modifies;
  std::vector<std::string> p4rt_deletes;
  absl::btree_map<std::string, pdpi::IrUpdateStatus*> app_db_status;

  for (const auto& entry : updates.entries) {
    // If we cannot determine the table type then something went wrong with the
    // IR translation, and we should not continue with this request.
    if (entry.appdb_table == AppDbTableType::UNKNOWN) {
      return gutil::InternalErrorBuilder()
             << "Could not determine AppDb table type for entry: "
             << entry.entry.DebugString();
    }

    // Update non AppDb:P4RT entries (e.g. VRF_TABLE).
    if (entry.appdb_table == AppDbTableType::VRF_TABLE) {
      RETURN_IF_ERROR(UpdateAppDbVrfTable(
          entry.update_type, entry.rpc_index, entry.entry, vrf_table,
          vrf_notification, app_db_client, state_db_client, *response));
      continue;
    }

    // Otherwise we default to updating the P4RT table.
    absl::StatusOr<std::string> key;
    switch (entry.update_type) {
      case p4::v1::Update::INSERT:
        key = CreateEntryForAppDbInsert(entry.entry, p4_info, duplicate_keys,
                                        p4rt_inserts, p4rt_table, app_db_client,
                                        state_db_client);
        break;
      case p4::v1::Update::MODIFY:
        key = CreateEntryForAppDbModify(entry.entry, p4_info, duplicate_keys,
                                        p4rt_modifies, p4rt_table,
                                        app_db_client, state_db_client);
        break;
      case p4::v1::Update::DELETE:
        key =
            CreateEntryForAppDbDelete(entry.entry, p4_info, duplicate_keys,
                                      p4rt_deletes, p4rt_table, app_db_client);
        break;
      default:
        key = gutil::InvalidArgumentErrorBuilder()
              << "Unsupported update type: " << entry.update_type;
    }

    if (!key.ok()) {
      LOG(WARNING) << "Could not update in AppDb: " << key.status();
      *response->mutable_statuses(entry.rpc_index) =
          GetIrUpdateStatus(key.status());
      continue;
    }

    app_db_status[*key] = response->mutable_statuses(entry.rpc_index);
  }

  WriteBatchToAppDb(p4rt_inserts, p4rt_modifies, p4rt_deletes, app_db_client,
                    p4rt_table);
  RETURN_IF_ERROR(GetAndProcessResponseNotification(
      p4rt_table.get_table_name(), p4rt_notification, app_db_client,
      state_db_client, app_db_status));

  return absl::OkStatus();
}

absl::StatusOr<boost::bimap<std::string, std::string>> GetPortIdTranslationMap(
    swss::DBConnectorInterface& app_db_client) {
  boost::bimap<std::string, std::string> translation_map;

  for (const std::string& key : app_db_client.keys("PORT_TABLE:Ethernet*")) {
    std::string sonic_port_name(absl::StripPrefix(key, "PORT_TABLE:"));
    std::unordered_map<std::string, std::string> port_entry =
        app_db_client.hgetall(key);

    // If the port entry must have an 'id' field.
    std::string* port_id = gutil::FindOrNull(port_entry, "id");
    if (port_id == nullptr) {
      std::string msg = absl::StrFormat(
          "The port configuration for '%s' is invalid: missing 'id' field.",
          key);
      LOG(WARNING) << msg;
      return gutil::InternalErrorBuilder() << msg;
    }

    // Try to insert the new entry. If the insert fails then either the port's
    // name or it's id was duplicated in the config.
    auto result = translation_map.insert({sonic_port_name, *port_id});
    if (result.second == false) {
      std::string msg = absl::StrFormat(
          "The port configuration for '%s' with ID '%s' is invalid: duplicated "
          "port name or port ID.",
          sonic_port_name, *port_id);
      LOG(WARNING) << msg;
      return gutil::InternalErrorBuilder() << msg;
    }
  }

  return translation_map;
}

}  // namespace sonic
}  // namespace p4rt_app
