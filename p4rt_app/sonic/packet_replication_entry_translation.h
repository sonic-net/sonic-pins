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
#ifndef PINS_P4RT_APP_SONIC_PACKET_REPLICATION_ENTRY_TRANSLATION_H_
#define PINS_P4RT_APP_SONIC_PACKET_REPLICATION_ENTRY_TRANSLATION_H_

#include <string>
#include <vector>

#include "absl/status/statusor.h"
#include "gutil/gutil/status.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4rt_app/sonic/redis_connections.h"
#include "swss/rediscommand.h"

namespace p4rt_app {
namespace sonic {

// Create an AppDB operation to update a packet replication engine entry.
absl::StatusOr<swss::KeyOpFieldsValuesTuple>
CreateAppDbPacketReplicationTableUpdate(
    p4::v1::Update::Type update_type,
    const pdpi::IrPacketReplicationEngineEntry& entry);

// Returns all packet replication entry keys currently installed in AppDb.
// Currently, this is only for table REPLICATION_IP_MULTICAST_TABLE.
std::vector<std::string>
GetAllPacketReplicationTableEntryKeys(P4rtTable &p4rt_table);

// Returns all the packet replication entries currently installed in
// the AppDb.
// Currently, this is only for table REPLICATION_IP_MULTICAST_TABLE.
absl::StatusOr<std::vector<pdpi::IrPacketReplicationEngineEntry>>
GetAllAppDbPacketReplicationTableEntries(P4rtTable &p4rt_table);

// Determines if the packet replication entries on both lists are equivalent.
// Returns a list of comparison failure messages, if any.
// There is no assumption that matching entries are found in the same index.
std::vector<std::string> ComparePacketReplicationTableEntries(
    const std::vector<pdpi::IrEntity> &entries_app_db,
    const std::vector<pdpi::IrEntity> &entries_cache);

} // namespace sonic
} // namespace p4rt_app

#endif // PINS_P4RT_APP_SONIC_PACKET_REPLICATION_ENTRY_TRANSLATION_H_
