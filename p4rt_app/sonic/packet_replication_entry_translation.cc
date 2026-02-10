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

#include "p4rt_app/sonic/packet_replication_entry_translation.h"

#include <algorithm>
#include <cstdint>
#include <iterator>
#include <string>
#include <utility>
#include <vector>

#include "absl/container/btree_map.h"
#include "absl/container/btree_set.h"
#include "absl/log/log.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "gutil/gutil/status.h"
#include "include/nlohmann/json.hpp"
#include "p4_pdpi/ir.pb.h"
#include "p4rt_app/sonic/app_db_to_pdpi_ir_translator.h"
#include "p4rt_app/sonic/redis_connections.h"
#include "swss/rediscommand.h"
#include "swss/schema.h"
#include "swss/table.h"

namespace p4rt_app {
namespace sonic {
namespace {

std::string_view TablePrefix() {
  static const auto* kTablePrefix = new std::string(
      absl::StrCat(APP_P4RT_REPLICATION_IP_MULTICAST_TABLE_NAME, ":"));
  return *kTablePrefix;
}

absl::StatusOr<std::string> StripTableName(absl::string_view app_db_key) {
  const absl::string_view kTablePrefix = TablePrefix();
  if (!absl::StartsWith(app_db_key, kTablePrefix)) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Invalid packet replication App DB key " << app_db_key;
  }
  return std::string{app_db_key.substr(kTablePrefix.size())};
}

std::string GetRedisPacketReplicationTableKey(
    const pdpi::IrPacketReplicationEngineEntry& entry) {
  // The final AppDb Key format is: <table_name>:<multicast_group_id>
  return absl::StrCat(TablePrefix(), IrMulticastGroupEntryToAppDbKey(
                                         entry.multicast_group_entry()));
}

std::vector<swss::FieldValueTuple> CreateFieldValues(
    const pdpi::IrPacketReplicationEngineEntry& entry) {
  nlohmann::json json_array = nlohmann::json::array();
  for (auto& replica : entry.multicast_group_entry().replicas()) {
    nlohmann::json json;
    json["multicast_replica_port"] = replica.port();
    json["multicast_replica_instance"] =
        absl::StrCat("0x", absl::Hex(replica.instance(), absl::kZeroPad4));
    json_array.push_back(json);
  }

  if (!entry.multicast_group_entry().metadata().empty()) {
    return {{"replicas", json_array.dump()},
            {"controller_metadata", entry.multicast_group_entry().metadata()}};
  } else {
    return {{"replicas", json_array.dump()}};
  }
}

void ComparePacketReplicationEntities(const pdpi::IrEntity& entity_app_db,
                                      const pdpi::IrEntity& entity_cache,
                                      std::vector<std::string>& failures) {
  const auto& group_entry_app_db =
      entity_app_db.packet_replication_engine_entry().multicast_group_entry();
  const auto& group_entry_cache =
      entity_cache.packet_replication_engine_entry().multicast_group_entry();

  // There's no need to check the multicast group ID, since the caller only
  // attempts to compare entities with equal multicast group IDs.

  if (group_entry_app_db.metadata() != group_entry_cache.metadata()) {
    failures.push_back(absl::StrCat("Packet replication metadata mismatch '",
                                    group_entry_app_db.metadata(), "' vs. '",
                                    group_entry_cache.metadata(), "'"));
  }

  absl::btree_set<std::string> port_instance_app_db;
  for (const auto& replica : group_entry_app_db.replicas()) {
    std::string pi = absl::StrCat(replica.port(), "_", replica.instance());
    port_instance_app_db.insert(pi);
  }

  absl::btree_set<std::string> port_instance_cache;
  for (const auto& replica : group_entry_cache.replicas()) {
    std::string pi = absl::StrCat(replica.port(), "_", replica.instance());
    port_instance_cache.insert(pi);
  }

  // Check difference between App DB and the cache.
  std::vector<std::string> differences;
  std::set_difference(port_instance_app_db.begin(), port_instance_app_db.end(),
                      port_instance_cache.begin(), port_instance_cache.end(),
                      std::inserter(differences, differences.begin()));

  for (const auto& difference : differences) {
    failures.push_back(absl::StrCat(
        "Packet replication cache is missing replica ", difference,
        " for group id ", group_entry_app_db.multicast_group_id()));
  }

  // Check difference between cache and App DB.
  differences.clear();
  std::set_difference(port_instance_cache.begin(), port_instance_cache.end(),
                      port_instance_app_db.begin(), port_instance_app_db.end(),
                      std::inserter(differences, differences.begin()));

  for (const auto& difference : differences) {
    failures.push_back(absl::StrCat("APP DB is missing replica ", difference,
                                    " for group id ",
                                    group_entry_app_db.multicast_group_id()));
  }
}

}  // namespace

absl::StatusOr<swss::KeyOpFieldsValuesTuple>
CreateAppDbPacketReplicationTableUpdate(
    p4::v1::Update::Type update_type,
    const pdpi::IrPacketReplicationEngineEntry& entry) {
  swss::KeyOpFieldsValuesTuple update;
  kfvKey(update) = GetRedisPacketReplicationTableKey(entry);
  switch (update_type) {
    case p4::v1::Update::INSERT:
    case p4::v1::Update::MODIFY:
      // Modify looks exactly the same as insert.
      // The Orchagent layer resolves differences.
      kfvOp(update) = SET_COMMAND;
      kfvFieldsValues(update) = CreateFieldValues(entry);
      break;
    case p4::v1::Update::DELETE:
      kfvOp(update) = DEL_COMMAND;
      break;
    default:
      return gutil::InvalidArgumentErrorBuilder()
             << "[P4RT App] Unsupported update type "
             << p4::v1::Update::Type_Name(update_type);
  }
  return update;
}

std::vector<std::string> GetAllPacketReplicationTableEntryKeys(
    P4rtTable& p4rt_table) {
  std::vector<std::string> pre_keys;
  for (const auto& key : p4rt_table.app_db->keys()) {
    if (absl::StartsWith(key, TablePrefix())) {
      pre_keys.push_back(key);
    }
  }
  return pre_keys;
}

absl::StatusOr<std::vector<pdpi::IrPacketReplicationEngineEntry>>
GetAllAppDbPacketReplicationTableEntries(P4rtTable& p4rt_table) {
  std::vector<pdpi::IrPacketReplicationEngineEntry> pre_entries;

  // Each key corresponds to a single multicast group, with all its replicas.
  auto keys = GetAllPacketReplicationTableEntryKeys(p4rt_table);
  for (const std::string& key : keys) {
    VLOG(1) << "Read packet replication engine entry " << key << " from App DB";
    ASSIGN_OR_RETURN(std::string multicast_group_id, StripTableName(key));

    pdpi::IrPacketReplicationEngineEntry pre_entry;
    auto* multicast_group_entry = pre_entry.mutable_multicast_group_entry();

    // Multicast Group ID.
    uint32_t group_id;
    if (absl::SimpleHexAtoi(multicast_group_id, &group_id)) {
      multicast_group_entry->set_multicast_group_id(group_id);
    } else {
      return gutil::InvalidArgumentErrorBuilder()
             << "Failed to parse multicast_group_id from App DB packet "
             << "replication entry key '" << key;
    }

    // Build replicas.
    for (const auto& [field, data] : p4rt_table.app_db->get(key)) {
      if (field == "replicas") {
        nlohmann::json json;
#ifdef __EXCEPTIONS
        try {
#endif
          json = nlohmann::json::parse(data);
#ifdef __EXCEPTIONS
        } catch (...) {
          return gutil::InternalErrorBuilder()
                 << "Could not parse JSON string: " << data;
        }
#endif

        for (const auto& json_replica : json) {
          std::string port_name;
          uint32_t instance;
          if (json_replica.find("multicast_replica_port") !=
              json_replica.end()) {
            port_name =
                json_replica.at("multicast_replica_port").get<std::string>();
          } else {
            return gutil::InvalidArgumentErrorBuilder()
                   << "JSON replica for multicast group ID "
                   << absl::StrCat("0x", absl::Hex(group_id))
                   << " is missing multicast_replica_port: " << json_replica;
          }
          if (json_replica.find("multicast_replica_instance") !=
              json_replica.end()) {
            std::string inst = json_replica.at("multicast_replica_instance")
                                   .get<std::string>();
            if (!absl::SimpleHexAtoi(inst, &instance)) {
              return gutil::InvalidArgumentErrorBuilder()
                     << "Failed to parse multicast_replica_instance in "
                     << "multicast group ID "
                     << absl::StrCat("0x", absl::Hex(group_id))
                     << " from JSON replica " << json_replica;
            }
          } else {
            return gutil::InvalidArgumentErrorBuilder()
                   << "JSON replica for multicast group ID "
                   << absl::StrCat("0x", absl::Hex(group_id))
                   << " is missing multicast_replica_instance: "
                   << json_replica;
          }
          auto* replica = multicast_group_entry->add_replicas();
          replica->set_port(port_name);
          replica->set_instance(instance);
        }
      } else if (field == "controller_metadata") {
        multicast_group_entry->set_metadata(data);
      }
    }
    pre_entries.push_back(pre_entry);
  }
  return pre_entries;
}

std::vector<std::string> ComparePacketReplicationTableEntries(
    const std::vector<pdpi::IrEntity>& entries_app_db,
    const std::vector<pdpi::IrEntity>& entries_cache) {
  std::vector<std::string> failures;

  // Multicast group ID -> IrEntity.
  absl::btree_map<uint32_t, pdpi::IrEntity> map_app_db;
  absl::btree_map<uint32_t, pdpi::IrEntity> map_cache;

  for (const auto& entry : entries_app_db) {
    map_app_db[entry.packet_replication_engine_entry()
                   .multicast_group_entry()
                   .multicast_group_id()] = entry;
  }

  for (const auto& entry : entries_cache) {
    map_cache[entry.packet_replication_engine_entry()
                  .multicast_group_entry()
                  .multicast_group_id()] = entry;
  }

  for (const auto& id_and_entry : map_app_db) {
    if (map_cache.find(id_and_entry.first) == map_cache.end()) {
      failures.push_back(
          absl::StrCat("Packet replication cache is missing multicast group ",
                       "ID ", id_and_entry.first));
      continue;
    }
    ComparePacketReplicationEntities(id_and_entry.second,
                                     map_cache[id_and_entry.first], failures);
  }

  for (const auto& id_and_entry : map_cache) {
    if (map_app_db.find(id_and_entry.first) == map_app_db.end()) {
      failures.push_back(absl::StrCat("APP DB is missing multicast group ID ",
                                      id_and_entry.first));
    }
    // There's no need to compare entities here, since all overlapping entities
    // were checked in the previous for loop.
  }

  return failures;
}

}  // namespace sonic
}  // namespace p4rt_app
