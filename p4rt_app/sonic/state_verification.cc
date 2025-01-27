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
#include "p4rt_app/sonic/state_verification.h"

#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "absl/container/btree_map.h"
#include "absl/log/log.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "gutil/gutil/status.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4rt_app/sonic/adapters/table_adapter.h"
#include "p4rt_app/sonic/app_db_manager.h"
#include "p4rt_app/sonic/app_db_to_pdpi_ir_translator.h"
#include "p4rt_app/sonic/packet_replication_entry_translation.h"
#include "p4rt_app/sonic/redis_connections.h"
#include "swss/schema.h"

namespace p4rt_app {
namespace sonic {
namespace {

// Helper function to format RedisDb entries in error messages.
//
// Output would look like:
// {{"field","value"},{"other_field","other_value"}}
std::string PrettyPrintEntry(
    const std::unordered_map<std::string, std::string>& map) {
  int index = 0;
  std::vector<std::string> pairs(map.size());
  for (const auto& [key, value] : map) {
    pairs[index] = absl::StrCat(key, ",", value);
    ++index;
  }

  return absl::StrCat("{{", absl::StrJoin(pairs, "},{"), "}}");
}

// Converts a list of 2 strings into a map. With the first value being the key,
// and the second being the data.
absl::StatusOr<std::unordered_map<std::string, std::string>> ListToMap(
    const std::vector<std::pair<std::string, std::string>>& list) {
  std::unordered_map<std::string, std::string> map;
  for (const auto& pair : list) {
    if (!map.insert({pair.first, pair.second}).second) {
      return gutil::InternalErrorBuilder()
             << "Detected a duplicate key '" << pair.first
             << "' for the table entry.";
    }
  }
  return map;
}

// A RedisTableEntry holds any data that could be read from a RedisDB table
// (e.g. AppDb, AppStateDb, etc.). Notice that Redis allows for duplicate
// fields, but our use case does not. If we detect duplicates, or any other
// problem,  the 'error' string will be populated. If the 'error' string is
// empty then the 'values' map is considered good.
struct RedisTableEntry {
  std::unordered_map<std::string, std::string> values;
  std::string errors;
};

// A RedisTable holds all entries for a given DB.
struct RedisTable {
  std::string db_name;

  // Use an absl::btree_map here to maintain order. This makes it easier to
  // quickly identify all the missing keys between 2 tables.
  absl::btree_map<std::string, RedisTableEntry> entries;
};

RedisTable ReadAllEntriesFromRedisTable(TableAdapter& table,
                                        absl::string_view db_name) {
  RedisTable result{.db_name = std::string{db_name}};
  for (const std::string& table_key : table.keys()) {
    RedisTableEntry table_entry;

    // Verify that there are no duplicate fields in the table entry.
    auto redis_values = ListToMap(table.get(table_key));
    if (!redis_values.ok()) {
      table_entry.errors =
          absl::StrCat(db_name, " has duplicate fields for key: ", table_key);
    } else {
      table_entry.values = *std::move(redis_values);
    }

    result.entries[table_key] = std::move(table_entry);
  }

  return result;
}

RedisTable TranslateP4rtIrEntitiesIntoRedisTable(
    const std::vector<pdpi::IrEntity>& ir_entities, absl::string_view db_name,
    const pdpi::IrP4Info& ir_p4_info) {
  RedisTable result{.db_name = std::string{db_name}};
  for (const auto& ir_entity : ir_entities) {
    RedisTableEntry table_entry;

    // If we fail to get the key we won't be able to add it as a table entry. In
    // this case, later checks should still fail because the value will appear
    // to be missing from the cache.

    if (ir_entity.entity_case() != pdpi::IrEntity::kTableEntry) {
      // This function is ony used in the context of P4RT table entries.
      continue;
    }
    auto table_key = GetRedisP4rtTableKey(ir_entity.table_entry(), ir_p4_info);
    if (!table_key.ok()) {
      LOG(ERROR) << db_name
                 << " could not get key for: " << ir_entity.ShortDebugString();
      continue;
    }

    auto app_db_values = IrTableEntryToAppDbValues(ir_entity.table_entry());
    if (!app_db_values.ok()) {
      table_entry.errors = absl::StrCat(
          db_name,
          " entry values could not be translated for key: ", *table_key);
      result.entries[*table_key] = std::move(table_entry);
      continue;
    }

    auto redis_values = ListToMap(*app_db_values);
    if (!redis_values.ok()) {
      table_entry.errors =
          absl::StrCat(db_name, " has duplicate fields for key: ", *table_key);
    } else {
      table_entry.values = *std::move(redis_values);
    }

    result.entries[*table_key] = std::move(table_entry);
  }
  return result;
}

std::string CompareTableEntries(absl::string_view key,
                                absl::string_view table_a_name,
                                const RedisTableEntry& entry_a,
                                absl::string_view table_b_name,
                                const RedisTableEntry& entry_b) {
  if (entry_a.values != entry_b.values) {
    return absl::StrFormat("Entries for '%s' do not match: %s=%s %s=%s", key,
                           table_a_name, PrettyPrintEntry(entry_a.values),
                           table_b_name, PrettyPrintEntry(entry_b.values));
  }
  return "";
}

std::vector<std::string> CompareTables(const RedisTable& table_a,
                                       const RedisTable& table_b) {
  std::vector<std::string> failures;

  // Iterate through each vector in parallel comparing the entries for equality.
  auto iter_a = table_a.entries.begin();
  auto iter_b = table_b.entries.begin();
  while (iter_a != table_a.entries.end() && iter_b != table_b.entries.end()) {
    if (iter_a->first > iter_b->first) {
      failures.push_back(
          absl::StrCat(table_a.db_name, " is missing key: ", iter_b->first));
      ++iter_b;
      continue;
    }
    if (iter_a->first < iter_b->first) {
      failures.push_back(
          absl::StrCat(table_b.db_name, " is missing key: ", iter_a->first));
      ++iter_a;
      continue;
    }

    // Verify that the 2 entries are valid.
    bool bad_entry_found = false;
    if (!iter_a->second.errors.empty()) {
      failures.push_back(iter_a->second.errors);
      bad_entry_found = true;
    }
    if (!iter_b->second.errors.empty()) {
      failures.push_back(iter_b->second.errors);
      bad_entry_found = true;
    }

    // If they both are valid we will compare them. Otherwise, we should have
    // already output a verification error.
    if (!bad_entry_found) {
      std::string error_message =
          CompareTableEntries(iter_a->first, table_a.db_name, iter_a->second,
                              table_b.db_name, iter_b->second);
      if (!error_message.empty()) {
        failures.push_back(error_message);
      }
    }
    ++iter_a;
    ++iter_b;
  }

  // Any extra keys in Table A must be missing from Table B.
  while (iter_a != table_a.entries.end()) {
    failures.push_back(
        absl::StrCat(table_b.db_name, " is missing key: ", iter_a->first));
    ++iter_a;
  }

  // Any extra keys in Table B must be missing from Table A.
  while (iter_b != table_b.entries.end()) {
    failures.push_back(
        absl::StrCat(table_a.db_name, " is missing key: ", iter_b->first));
    ++iter_b;
  }

  return failures;
}

}  // namespace

std::vector<std::string> VerifyAppStateDbAndAppDbEntries(
    TableAdapter& app_state_db, TableAdapter& app_db) {
  return CompareTables(
      ReadAllEntriesFromRedisTable(app_db, "AppDb"),
      ReadAllEntriesFromRedisTable(app_state_db, "AppStateDb"));
}

std::vector<std::string> VerifyP4rtTableWithCacheEntities(
    TableAdapter& app_db, const std::vector<pdpi::IrEntity>& ir_entities,
    const pdpi::IrP4Info& ir_p4_info) {
  std::vector<std::string> failures;

  RedisTable redis_db_entries = ReadAllEntriesFromRedisTable(app_db, "AppDb");

  // Remove any entries for ACL table definitions or packet replication.
  absl::erase_if(redis_db_entries.entries, [](const auto& iter) {
    return (absl::StartsWith(iter.first, "ACL_TABLE_DEFINITION_TABLE:") ||
            absl::StartsWith(iter.first, "TABLES_DEFINITION_TABLE:") ||
            absl::StartsWith(iter.first, APP_P4RT_REPLICATION_IP_MULTICAST_TABLE_NAME));
  });

  std::vector<std::string> comparison_failures = CompareTables(
      redis_db_entries, TranslateP4rtIrEntitiesIntoRedisTable(
                            ir_entities, "EntityCache", ir_p4_info));
  failures.insert(failures.end(), comparison_failures.begin(),
                  comparison_failures.end());
  return failures;
}

std::vector<std::string> VerifyPacketReplicationWithCacheEntities(
    P4rtTable& p4rt_table,
    const std::vector<pdpi::IrEntity>& cache_ir_entities) {
  std::vector<std::string> failures;

  auto redis_db_ir_entries =
      GetAllAppDbPacketReplicationTableEntries(p4rt_table);
  if (!redis_db_ir_entries.ok()) {
    failures.push_back(
        absl::StrCat("Unable to fetch packet replication entries: ",
                     redis_db_ir_entries.status().message()));
  }

  std::vector<pdpi::IrEntity> redis_db_ir_entities;
  for (auto& entry : *redis_db_ir_entries) {
    pdpi::IrEntity entity;
    *entity.mutable_packet_replication_engine_entry() = entry;
    redis_db_ir_entities.push_back(entity);
  }

  std::vector<std::string> comparison_failures =
      ComparePacketReplicationTableEntries(redis_db_ir_entities,
                                           cache_ir_entities);
  failures.insert(failures.end(), comparison_failures.begin(),
                  comparison_failures.end());
  return failures;
}

}  // namespace sonic
}  // namespace p4rt_app
