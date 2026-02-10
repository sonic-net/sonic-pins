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
#ifndef PINS_P4RT_APP_SONIC_STATE_VERIFICATION_H_
#define PINS_P4RT_APP_SONIC_STATE_VERIFICATION_H_

#include <vector>

#include "absl/container/flat_hash_map.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4rt_app/sonic/adapters/table_adapter.h"
#include "p4rt_app/sonic/packet_replication_entry_translation.h"
#include "p4rt_app/sonic/redis_connections.h"

namespace p4rt_app {
namespace sonic {

// For a given table this function will query the AppStateDb for all entries.
// Then verify that each of those entries exists in the AppDb, and that the
// field/value pairs match with the data in the AppStateDb.
//
// On success an empty vector is returned. Otherwise, the vector will contain
// one message for every error found.
std::vector<std::string>
VerifyAppStateDbAndAppDbEntries(TableAdapter &app_state_db,
                                TableAdapter &app_db);

// Reads all the entries out of a P4RT table, and compares the values to a
// list of PI TableEntries. Non-P4RT table entries will be ignored.
//
// On success an empty vector is returned. Otherwise, the vector will contain
// one message for every error found.
std::vector<std::string>
VerifyP4rtTableWithCacheEntities(TableAdapter &app_db,
                                 const std::vector<pdpi::IrEntity> &ir_entities,
                                 const pdpi::IrP4Info &ir_p4_info);

// Reads all the packet replication entries out of the P4RT table and compares
// the values to a list of PI PacketReplicationEntries.
// On success, an empty vector is returned.  Otherwise, the vector will contain
// an error message for each problem found.
std::vector<std::string> VerifyPacketReplicationWithCacheEntities(
    P4rtTable &p4rt_table,
    const std::vector<pdpi::IrEntity> &cache_ir_entities);

} // namespace sonic
} // namespace p4rt_app

#endif // PINS_P4RT_APP_SONIC_STATE_VERIFICATION_H_
