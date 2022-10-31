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
#include <utility>
#include <vector>

#include "absl/container/btree_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_split.h"
#include "glog/logging.h"
#include "gutil/collections.h"
#include "gutil/status.h"
#include "p4_pdpi/ir.pb.h"
#include "p4rt_app/sonic/app_db_to_pdpi_ir_translator.h"
#include "p4rt_app/sonic/redis_connections.h"
#include "p4rt_app/sonic/response_handler.h"
#include "p4rt_app/utils/status_utility.h"
#include "p4rt_app/utils/table_utility.h"
#include "swss/json.h"
#include "swss/json.hpp"

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
    P4rtTable& p4rt_table, const pdpi::IrTableEntry& entry,
    const pdpi::IrP4Info& p4_info,
    const absl::flat_hash_set<std::string>& duplicate_keys,
    std::vector<std::string>& p4rt_deletes) {
  VLOG(1) << "Delete PDPI IR entry: " << entry.ShortDebugString();

  ASSIGN_OR_RETURN(std::string key, GetP4rtTableKey(entry, p4_info));

  // Verify key has not been duplicated in this batch request.
  if (duplicate_keys.count(key) > 0) {
    return gutil::InvalidArgumentErrorBuilder()
           << "[P4RT App] Found duplicated key in the same batch request.";
  }

  // Check that key exists in the table.
  if (!p4rt_table.app_db->exists(key)) {
    LOG(WARNING) << "Could not delete missing entry: " << key;
    return gutil::NotFoundErrorBuilder()
           << "[P4RT App] Table entry with the given key does not exist in '"
           << entry.table_name() << "'.";
  }

  // Get table entry from the APP_DB (before delete) instead of the one from the
  // request.
  ASSIGN_OR_RETURN(auto ir_table_entry,
                   AppDbKeyAndValuesToIrTableEntry(
                       p4_info, key, p4rt_table.app_db->get(key)));

  LOG(INFO) << "Delete AppDb entry: " << key;
  p4rt_deletes.push_back(key);
  return key;
}

// Formats the IR entry as a AppDb entry and updates the p4rt_inserts (to be
// inserted in a batch later). On success the P4RT key is returned.
absl::StatusOr<std::string> CreateEntryForAppDbInsert(
    P4rtTable& p4rt_table, const pdpi::IrTableEntry& entry,
    const pdpi::IrP4Info& p4_info,
    const absl::flat_hash_set<std::string>& duplicate_keys,
    std::vector<swss::KeyOpFieldsValuesTuple>& p4rt_inserts) {
  VLOG(1) << "Insert PDPI IR entry: " << entry.ShortDebugString();

  ASSIGN_OR_RETURN(std::string key, GetP4rtTableKey(entry, p4_info));

  // Verify key has not been duplicated in this batch request.
  if (duplicate_keys.count(key) > 0) {
    return gutil::InvalidArgumentErrorBuilder()
           << "[P4RT App] Found duplicated key in the same batch request.";
  }

  // Check that key does not already exist in the table.
  if (p4rt_table.app_db->exists(key)) {
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
    P4rtTable& p4rt_table, const pdpi::IrTableEntry& entry,
    const pdpi::IrP4Info& p4_info,
    const absl::flat_hash_set<std::string>& duplicate_keys,
    std::vector<swss::KeyOpFieldsValuesTuple>& p4rt_modifies) {
  VLOG(1) << "Modify PDPI IR entry: " << entry.ShortDebugString();

  ASSIGN_OR_RETURN(std::string key, GetP4rtTableKey(entry, p4_info));

  // Verify key has not been duplicated in this batch request.
  if (duplicate_keys.count(key) > 0) {
    return gutil::InvalidArgumentErrorBuilder()
           << "[P4RT App] Found duplicated key in the same batch request.";
  }

  // Check that key already exist in the table.
  if (!p4rt_table.app_db->exists(key)) {
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
    const std::vector<std::pair<std::string, std::string>>& counter_data) {
  for (const auto& [field, data] : counter_data) {
    // Update packet count only if data is present.
    if (field == "packets") {
      uint64_t packets = 0;
      if (absl::SimpleAtoi(data, &packets)) {
        table_entry.mutable_counter_data()->set_packet_count(packets);
      } else {
        LOG(ERROR) << "Unexpected packets value '" << data
                   << "' in CountersDB for table entry: "
                   << table_entry.ShortDebugString();
      }
    }

    // Update byte count only if data is present.
    if (field == "bytes") {
      uint64_t bytes = 0;
      if (absl::SimpleAtoi(data, &bytes)) {
        table_entry.mutable_counter_data()->set_byte_count(bytes);
      } else {
        LOG(ERROR) << "Unexpected bytes value '" << data
                   << "' in CountersDB for table entry: "
                   << table_entry.ShortDebugString();
      }
    }
  }

  return absl::OkStatus();
}

// Writes into the APP_DB Producer Table using the bulk option.
void WriteBatchToAppDb(
    P4rtTable& p4rt_table,
    const std::vector<swss::KeyOpFieldsValuesTuple>& p4rt_inserts,
    const std::vector<swss::KeyOpFieldsValuesTuple>& p4rt_modifies,
    const std::vector<std::string>& p4rt_deletes) {
  if (!p4rt_inserts.empty()) p4rt_table.producer_state->batch_set(p4rt_inserts);

  if (!p4rt_modifies.empty()) {
    std::vector<std::string> del_keys(p4rt_modifies.size());
    for (int i = 0; i < p4rt_modifies.size(); ++i) {
      del_keys[i] = kfvKey(p4rt_modifies[i]);
    }

    // On modify we need to first remove the existing entries to get rid of any
    // action paramters that may be replaced with a new action. Doing this
    // through the app_db_client will not invoke an action in the OrchAgent.
    p4rt_table.app_db->batch_del(del_keys);

    // Then we re-insert the entries through the ProducerStateTable which will
    // inoke an update action in the OrchAgent.
    p4rt_table.producer_state->batch_set(p4rt_modifies);
  }

  if (!p4rt_deletes.empty()) p4rt_table.producer_state->batch_del(p4rt_deletes);
}

}  // namespace

absl::StatusOr<pdpi::IrTableEntry> ReadP4TableEntry(
    P4rtTable& p4rt_table, const pdpi::IrP4Info& p4info,
    const std::string& key) {
  VLOG(1) << "Read AppDb entry: " << key;
  ASSIGN_OR_RETURN(pdpi::IrTableEntry table_entry,
                   AppDbKeyAndValuesToIrTableEntry(
                       p4info, key, p4rt_table.app_state_db->get(key)));

  // CounterDb entries will include the full AppDb entry key.
  RETURN_IF_ERROR(AppendCounterData(
      table_entry, p4rt_table.counter_db->get(absl::StrCat(
                       p4rt_table.app_db->getTablePrefix(), key))));
  return table_entry;
}

std::vector<std::string> GetAllP4TableEntryKeys(P4rtTable& p4rt_table) {
  std::vector<std::string> p4rt_keys;

  for (const auto& key : p4rt_table.app_state_db->keys()) {
    const std::vector<std::string> split = absl::StrSplit(key, ':');

    // The DEFINITION sub-table does not hold any P4RT_TABLE entries, and should
    // be ignored.
    if (split.size() > 1 && split[0] == "DEFINITION") {
      continue;
    }

    p4rt_keys.push_back(key);
  }
  return p4rt_keys;
}

absl::Status UpdateAppDb(P4rtTable& p4rt_table,
                         const AppDbUpdates& updates,
                         const pdpi::IrP4Info& p4_info,
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
             << entry.entry.ShortDebugString();
    }

    // Otherwise we default to updating the P4RT table.
    absl::StatusOr<std::string> key;
    switch (entry.update_type) {
      case p4::v1::Update::INSERT:
        key = CreateEntryForAppDbInsert(p4rt_table, entry.entry, p4_info,
                                        duplicate_keys, p4rt_inserts);
        break;
      case p4::v1::Update::MODIFY:
        key = CreateEntryForAppDbModify(p4rt_table, entry.entry, p4_info,
                                        duplicate_keys, p4rt_modifies);
        break;
      case p4::v1::Update::DELETE:
        key = CreateEntryForAppDbDelete(p4rt_table, entry.entry, p4_info,
                                        duplicate_keys, p4rt_deletes);
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

  WriteBatchToAppDb(p4rt_table, p4rt_inserts, p4rt_modifies, p4rt_deletes);
  RETURN_IF_ERROR(GetAndProcessResponseNotification(
      *p4rt_table.notifier, *p4rt_table.app_db, *p4rt_table.app_state_db,
      app_db_status, ResponseTimeMonitor::kP4rtTableWrite));

  return absl::OkStatus();
}

}  // namespace sonic
}  // namespace p4rt_app
