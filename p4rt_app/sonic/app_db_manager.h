/*
 * Copyright 2020 Google LLC
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
#ifndef PINS_P4RT_APP_SONIC_APP_DB_MANAGER_H_
#define PINS_P4RT_APP_SONIC_APP_DB_MANAGER_H_

#include <cstdint>
#include <optional>
#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "include/nlohmann/json.hpp"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/entity_keys.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4rt_app/sonic/packet_replication_entry_translation.h"
#include "p4rt_app/sonic/redis_connections.h"
#include "p4rt_app/sonic/swss_utils.h"
#include "swss/json.h"

namespace p4rt_app {
namespace sonic {

// The P4RT App will usually target the AppDb P4RT table for which it is the
// only entry owner. However, in certain cases we can target other shared
// RedisDb tables.
enum class AppDbTableType {
  UNKNOWN,
  P4RT,
  VRF_TABLE,
};

// Action profiles are used to model things like WCMP where we can have multiple
// actions with different weights. Resource accounting can be measured either
// against the total number of actions, or the sum total of all the action
// weights.
struct ActionProfileResources {
  std::string name;
  int32_t number_of_actions = 0;
  int64_t total_weight = 0;
};

// Each table resource usually only counts as 1 (i.e. one table entry), but
// depending on the table they may include an action profile (e.g. WCMP).
struct TableResources {
  std::string name;
  std::optional<ActionProfileResources> action_profile;
};

// AppDb entries can be handled in any order by P4RT, but for error reporting
// purposes we need to keep track of the RPC update index.
struct AppDbEntry {
  // A write request sends a list of Entities that need to be handled. The
  // rpc_index is the index into that list.
  int rpc_index = 0;

  // The IR translation of the PI request.
  pdpi::IrEntity entry;

  // Specifies if this request is an INSERT MODIFY or DELETE.
  p4::v1::Update::Type update_type;

  // Normalized PI entities. Note this will be semantically the same as the
  // original request, but does not have to be syntactically the same.
  p4::v1::Entity pi_entity;

  // A unique hash of the entries match fields. Used to identify duplicates and
  // any caching of entries.
  pdpi::EntityKey entity_key;

  // The net utilization change for table entries with group actions. If the
  // update_type is an insert then this value will simply be the resources for
  // the entry. If the update_type is a modify then this value is the difference
  // between the new and old entries. If the update_type is a delete then this
  // value is the resources of the old entry.
  // Note: This is only relevant at the moment for tables with action profiles.
  TableResources resource_utilization_change;

  // The SWSS OrchAgent that should handle this entry.
  AppDbTableType appdb_table = AppDbTableType::UNKNOWN;
};

// List of all updates that should be made to the AppDb.
struct AppDbUpdates {
  std::vector<AppDbEntry> entries;
  int total_rpc_updates = 0;
};

// Insert table definition
absl::Status AppendExtTableDefinition(nlohmann::json &tables,
                                      const pdpi::IrTableDefinition &ir_table);

// A definition set string in json format published to AppDb
absl::StatusOr<std::string>
PublishExtTablesDefinitionToAppDb(const nlohmann::json &tables_json,
                                  uint64_t cookie, P4rtTable &p4rt_table);

// Takes a list of AppDb updates (i.e. inserts, modifies, or deletes) and
// translates them so that they are consumable by the AppDb. It will also
// create, or remove, any VRF IDs as needed.
absl::Status UpdateAppDb(P4rtTable &p4rt_table, VrfTable &vrf_table,
                         const AppDbUpdates &updates,
                         const pdpi::IrP4Info &p4_info,
                         pdpi::IrWriteResponse *response);

// Returns all P4RT keys currently installed in the AppStateDb. This does not
// include any keys that are currently being handled by the lower layers (i.e.
// keys starting with _).
std::vector<std::string> GetAllP4TableEntryKeys(P4rtTable &p4rt_table);

// Returns the expected P4RT_TABLE key for a given IRTableEntry.
absl::StatusOr<std::string>
GetRedisP4rtTableKey(const pdpi::IrTableEntry &entry,
                     const pdpi::IrP4Info &p4_info);

// Reads a table entry from the P4RT_TABLE in the AppStateDb. Returns a failure
// if the entry does not exist, or cannot be translated into a pdpi::IrEntity.
// Note: this function will not be used to read packet replication entries from
// the P4RT_TABLE.
absl::StatusOr<pdpi::IrTableEntry>
ReadP4TableEntry(P4rtTable &p4rt_table, const pdpi::IrP4Info &p4info,
                 const std::string &key);

// Checks CounterDB for any counter data relating to the table entry and appends
// it to the ir_table_entry argument. The ir_table_entry is untouched if no
// counter data is found.
absl::Status AppendCounterDataForTableEntry(pdpi::IrTableEntry &ir_table_entry,
                                            P4rtTable &p4rt_table,
                                            const pdpi::IrP4Info &p4info);

// Returns the expected P4RT_TABLE key for a given IRTableEntry.
absl::StatusOr<std::string>
GetRedisP4rtTableKey(const pdpi::IrTableEntry &entry,
                     const pdpi::IrP4Info &p4_info);

} // namespace sonic
} // namespace p4rt_app

#endif // PINS_P4RT_APP_SONIC_APP_DB_MANAGER_H_
