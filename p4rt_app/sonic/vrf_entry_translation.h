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
#ifndef GOOGLE_P4RT_APP_SONIC_VRF_ENTRY_TRANSLATION_H_
#define GOOGLE_P4RT_APP_SONIC_VRF_ENTRY_TRANSLATION_H_

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "gutil/status.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "swss/consumernotifierinterface.h"
#include "swss/dbconnectorinterface.h"
#include "swss/producerstatetableinterface.h"

namespace p4rt_app {
namespace sonic {

// Takes a list of AppDb updates (i.e. inserts, modifies, or deletes) and
// translates them so that they are consumable by the AppDb. It will also
// create, or remove, any VRF IDs as needed.
absl::Status UpdateAppDbVrfTable(
    p4::v1::Update::Type update_type, int rpc_index,
    const pdpi::IrTableEntry& entry,
    swss::ProducerStateTableInterface& vrf_table,
    swss::ConsumerNotifierInterface& vrf_notification,
    swss::DBConnectorInterface& app_db_client,
    swss::DBConnectorInterface& state_db_client,
    pdpi::IrWriteResponse& response);

// Returns all the VRF_TABLE entries currently installed in the AppDb. This does
// not include any entries that are currently being handled by the lower layers
// (i.e. keys starting with _).
absl::StatusOr<std::vector<pdpi::IrTableEntry>> GetAllAppDbVrfTableEntries(
    swss::DBConnectorInterface& app_db_client);

}  // namespace sonic
}  // namespace p4rt_app

#endif  // GOOGLE_P4RT_APP_SONIC_VRF_ENTRY_TRANSLATION_H_
