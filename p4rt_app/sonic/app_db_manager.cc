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
#include "absl/strings/numbers.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_split.h"
#include "glog/logging.h"
#include "gutil/collections.h"
#include "gutil/status.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4rt_app/sonic/app_db_to_pdpi_ir_translator.h"
#include "p4rt_app/sonic/redis_connections.h"
#include "p4rt_app/sonic/response_handler.h"
#include "p4rt_app/sonic/vrf_entry_translation.h"
#include "p4rt_app/utils/status_utility.h"
#include "p4rt_app/utils/table_utility.h"
#include "swss/json.h"
#include <nlohmann/json.hpp>
#include "swss/rediscommand.h"
#include "swss/schema.h"
#include "swss/table.h"

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

// Translates the IR entry into a format understood by the OA layer. Also
// verifies that the entry can be deleted (i.e. alreay exist). On success the
// P4RT key is returned.
absl::StatusOr<std::string> CreateEntryForDelete(
    P4rtTable& p4rt_table, const pdpi::IrTableEntry& entry,
    const pdpi::IrP4Info& p4_info,
    const absl::flat_hash_set<std::string>& duplicate_keys,
    std::vector<swss::KeyOpFieldsValuesTuple>& p4rt_deletes) {
  VLOG(2) << "Delete PDPI IR entry: " << entry.ShortDebugString();

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

  // Get table entry from the AppDB (before delete) instead of the one from the
  // request.
  ASSIGN_OR_RETURN(auto ir_table_entry,
                   AppDbKeyAndValuesToIrTableEntry(
                       p4_info, key, p4rt_table.app_db->get(key)));

  VLOG(1) << "Delete AppDb entry: " << key;
  swss::KeyOpFieldsValuesTuple key_value;
  kfvKey(key_value) = key;
  kfvOp(key_value) = "DEL";
  p4rt_deletes.push_back(key_value);
  return key;
}

// Translates the IR entry into a format understood by the OA layer. Also
// verifies that the entry can be inserted (i.e. doesn't alreay exist). On
// success the P4RT key is returned.
absl::StatusOr<std::string> CreateEntryForInsert(
    P4rtTable& p4rt_table, const pdpi::IrTableEntry& entry,
    const pdpi::IrP4Info& p4_info,
    const absl::flat_hash_set<std::string>& duplicate_keys,
    std::vector<swss::KeyOpFieldsValuesTuple>& p4rt_inserts) {
  VLOG(2) << "Insert PDPI IR entry: " << entry.ShortDebugString();

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

  VLOG(1) << "Insert AppDb entry: " << key;
  swss::KeyOpFieldsValuesTuple key_value;
  kfvKey(key_value) = key;
  kfvOp(key_value) = "SET";
  ASSIGN_OR_RETURN(kfvFieldsValues(key_value),
                   IrTableEntryToAppDbValues(entry));
  p4rt_inserts.push_back(std::move(key_value));
  return key;
}

// Translates the IR entry into a format understood by the OA layer. Also
// verifies that the entry can be modified (i.e. alreay exist). On success the
// P4RT key is returned.
absl::StatusOr<std::string> CreateEntryForModify(
    P4rtTable& p4rt_table, const pdpi::IrTableEntry& entry,
    const pdpi::IrP4Info& p4_info,
    const absl::flat_hash_set<std::string>& duplicate_keys,
    std::vector<swss::KeyOpFieldsValuesTuple>& p4rt_modifies) {
  VLOG(2) << "Modify PDPI IR entry: " << entry.ShortDebugString();

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

  VLOG(1) << "Modify AppDb entry: " << key;
  swss::KeyOpFieldsValuesTuple key_value;
  kfvKey(key_value) = key;
  kfvOp(key_value) = "SET";
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

}  // namespace

// Generates the table definition in json format
//
//{
//  "tables": [
//      {
//        "id": <value>,
//        "name": "table-name 1",
//        "alias": "table-alias 1",
//        "matchfields": [
//          {
//              "id": <value>,
//              "name": "match-field 1",
//              "bitwidth": <value>,
//              "format": <value>,
//              "references": [
//                  {
//                      "table": "reference table",
//                      "match": "reference match"
//                  }
//              ]
//          },
//          {
//              "id": <value>,
//              "name": "match-field 2",
//              ....
//              ....
//          }
//        ],
//        "actions": [
//          {
//              "id": <value>,
//              "name": "action-name 1",
//              "alias": "action-alias 1",
//              "params": [
//                  {
//                      "id": <value>,
//                      "name": "param-name 1",
//                      "bitwidth": <value>,
//                      "format": <value>,
//                      "references": [
//                          {
//                              "table": "reference table",
//                              "match": "reference match"
//                          }
//                      ]
//                  },
//                  {
//                      "id": <value>,
//                      "name": "param-name 2",
//                      ....
//                      ....
//                  }
//              ]
//          },
//          {
//              "id": <value>,
//              "name": "action-name 2",
//              "alias": "action-alias 2",
//              ....
//              ....
//          }
//        ],
//        "counter/unit": <value>
//      },
//      {
//        "id": <value>,
//        "name": "table-name 2",
//        "alias": "table-alias 2",
//        ....
//        ....
//      }
//  ]
//}
//
//
absl::Status AppendExtTableDefinition(
    nlohmann::json &tables,
    const pdpi::IrTableDefinition& ir_table) {

  nlohmann::json table_json = nlohmann::json({});

  table_json["id"] = ir_table.preamble().id();
  table_json["name"] = ir_table.preamble().name();
  table_json["alias"] = ir_table.preamble().alias();

  nlohmann::json matchfields_json = {};
  for (const auto& match_pair : ir_table.match_fields_by_name()) {
    nlohmann::json match_json = nlohmann::json({});
    pdpi::IrMatchFieldDefinition ir_match = match_pair.second;

    match_json["id"] = ir_match.match_field().id();
    match_json["name"] = ir_match.match_field().name();
    match_json["bitwidth"] = ir_match.match_field().bitwidth();
    match_json["format"] = pdpi::Format_Name(ir_match.format());
    nlohmann::json references_json = {};
    for (const auto& ref_pair : ir_match.references()) {
      nlohmann::json ref_json = nlohmann::json({});
      ref_json["table"] = ref_pair.table();
      ref_json["match"] = ref_pair.match_field();
      references_json.push_back(ref_json);
    }
    match_json.push_back(
         nlohmann::json::object_t::value_type("references", references_json));
    matchfields_json.push_back(match_json);
  }
  table_json.push_back(
       nlohmann::json::object_t::value_type("matchFields", matchfields_json));

  nlohmann::json actions_json = {};
  for (const auto& action : ir_table.entry_actions()) {
    nlohmann::json action_json = nlohmann::json({});
    pdpi::IrActionDefinition ir_action = action.action();

    action_json["id"] = ir_action.preamble().id();
    action_json["name"] = ir_action.preamble().name();
    action_json["alias"] = ir_action.preamble().alias();
    nlohmann::json params_json = {};
    for (const auto& param : ir_action.params_by_name()) {
      nlohmann::json param_json = nlohmann::json({});
      pdpi::IrActionDefinition::IrActionParamDefinition ir_param = param.second;

      param_json["id"] = ir_param.param().id();
      param_json["name"] = ir_param.param().name();
      param_json["bitwidth"] = ir_param.param().bitwidth();
      param_json["format"] = pdpi::Format_Name(ir_param.format());
      nlohmann::json references_json = {};
      for (const auto& ref_pair : ir_param.references()) {
        nlohmann::json ref_json = nlohmann::json({});
        ref_json["table"] = ref_pair.table();
        ref_json["match"] = ref_pair.match_field();
        references_json.push_back(ref_json);
      }
      param_json.push_back(
           nlohmann::json::object_t::value_type("references", references_json));
      params_json.push_back(param_json);
    }
    action_json.push_back(
          nlohmann::json::object_t::value_type("params", params_json));
    actions_json.push_back(action_json);
  }
  table_json.push_back(
       nlohmann::json::object_t::value_type("actions", actions_json));

  if (ir_table.counter().unit() != p4::config::v1::CounterSpec::UNSPECIFIED) {
    // Counter units: BYTES, PACKETS, BOTH
    table_json.push_back(nlohmann::json::object_t::value_type("counter/unit",
         p4::config::v1::CounterSpec::Unit_Name(ir_table.counter().unit())));
  }

  tables.push_back(table_json);

  return absl::OkStatus();
}

// Publish set of tables in json formatted string to AppDb
absl::StatusOr<std::string> PublishExtTablesDefinitionToAppDb(
    const nlohmann::json &tables_json,
    uint64_t cookie,
    P4rtTable& p4rt_table) {

  nlohmann::json json_key;
  std::ostringstream oss;
  swss::KeyOpFieldsValuesTuple kfv;
  oss << cookie;

  json_key["context"] = oss.str();

  std::string key = absl::Substitute("$0:$1",
                          table::TypeName(table::Type::kTblsDefinitionSet),
                          json_key.dump());

  nlohmann::json info_json = nlohmann::json({});
  info_json.push_back(
        nlohmann::json::object_t::value_type("tables", tables_json));
  std::vector<swss::FieldValueTuple> values;
  values.push_back(std::make_pair("info", info_json.dump()));
  kfvKey(kfv) = key;
  kfvOp(kfv) = "SET";
  kfvFieldsValues(kfv) = values;
  p4rt_table.notification_producer->send({kfv});

  return key;

}

absl::StatusOr<pdpi::IrTableEntry> ReadP4TableEntry(
    P4rtTable& p4rt_table, const pdpi::IrP4Info& p4info,
    const std::string& key) {
  VLOG(1) << "Read AppDb entry: " << key;
  ASSIGN_OR_RETURN(pdpi::IrTableEntry table_entry,
                   AppDbKeyAndValuesToIrTableEntry(
                       p4info, key, p4rt_table.app_db->get(key)));

  // Counters should only exist for ACL table entries.
  if (absl::StartsWith(key, table::TypeName(table::Type::kAcl))) {
    // CounterDb entries will include the full AppDb entry key.
    RETURN_IF_ERROR(AppendCounterData(
        table_entry, p4rt_table.counter_db->get(absl::StrCat(
                         p4rt_table.app_db->getTablePrefix(), key))));
  }
  return table_entry;
}

absl::Status AppendCounterDataForTableEntry(pdpi::IrTableEntry& ir_table_entry,
                                            P4rtTable& p4rt_table,
                                            const pdpi::IrP4Info& p4info) {
  ASSIGN_OR_RETURN(std::string key, GetP4rtTableKey(ir_table_entry, p4info));
  return AppendCounterData(ir_table_entry,
                           p4rt_table.counter_db->get(absl::StrCat(
                               p4rt_table.app_db->getTablePrefix(), key)));
}

std::vector<std::string> GetAllP4TableEntryKeys(P4rtTable& p4rt_table) {
  std::vector<std::string> p4rt_keys;

  for (const auto& key : p4rt_table.app_db->keys()) {
    const std::vector<std::string> split = absl::StrSplit(key, ':');

    // The DEFINITION sub-table does not hold any P4RT_TABLE entries, and should
    // be ignored.
    if (split.size() > 1 &&
                ((split[0] == APP_P4RT_ACL_TABLE_DEFINITION_NAME) ||
                 (split[0] == APP_P4RT_TABLES_DEFINITION_TABLE_NAME))) {
      continue;
    }

    p4rt_keys.push_back(key);
  }
  return p4rt_keys;
}

absl::Status UpdateAppDb(P4rtTable& p4rt_table, VrfTable& vrf_table,
                         const AppDbUpdates& updates,
                         const pdpi::IrP4Info& p4_info,
                         pdpi::IrWriteResponse* response) {
  // We keep a temporary cache of any keys that are duplicated in the batch
  // request so the flow can be rejected.
  absl::flat_hash_set<std::string> duplicate_keys =
      FindDuplicateKeys(updates, p4_info);

  std::vector<swss::KeyOpFieldsValuesTuple> kfv_updates;
  absl::btree_map<std::string, pdpi::IrUpdateStatus*> app_db_status;

  for (const auto& entry : updates.entries) {
    if (entry.appdb_table == AppDbTableType::UNKNOWN) {
      // If we cannot determine the table type then something went wrong with
      // the IR translation, and we should not continue with this request.
      return gutil::InternalErrorBuilder()
             << "Could not determine AppDb table type for entry: "
             << entry.entry.ShortDebugString();
    } else if (entry.appdb_table == AppDbTableType::VRF_TABLE) {
      // Update non AppDb:P4RT entries (e.g. VRF_TABLE).
      RETURN_IF_ERROR(UpdateAppDbVrfTable(vrf_table, entry.update_type,
                                          entry.rpc_index, entry.entry,
                                          *response));
      continue;
    }

    // Otherwise we default to updating the P4RT table.
    absl::StatusOr<std::string> key;
    switch (entry.update_type) {
      case p4::v1::Update::INSERT:
        key = CreateEntryForInsert(p4rt_table, entry.entry, p4_info,
                                   duplicate_keys, kfv_updates);
        break;
      case p4::v1::Update::MODIFY:
        key = CreateEntryForModify(p4rt_table, entry.entry, p4_info,
                                   duplicate_keys, kfv_updates);
        break;
      case p4::v1::Update::DELETE:
        key = CreateEntryForDelete(p4rt_table, entry.entry, p4_info,
                                   duplicate_keys, kfv_updates);
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

  // Send all the P4RT_TABLE updates as one batch.
  p4rt_table.notification_producer->send(kfv_updates);
  RETURN_IF_ERROR(GetAndProcessResponseNotificationWithoutRevertingState(
      *p4rt_table.notification_consumer, app_db_status));

  return absl::OkStatus();
}

}  // namespace sonic
}  // namespace p4rt_app
