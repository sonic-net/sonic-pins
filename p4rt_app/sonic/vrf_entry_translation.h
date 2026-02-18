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
#ifndef PINS_P4RT_APP_SONIC_VRF_ENTRY_TRANSLATION_H_
#define PINS_P4RT_APP_SONIC_VRF_ENTRY_TRANSLATION_H_

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "gutil/gutil/status.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4rt_app/sonic/redis_connections.h"

namespace p4rt_app {
namespace sonic {

// Takes a list of AppDb updates (i.e. inserts, modifies, or deletes) and
// translates them so that they are consumable by the AppDb. It will also
// create, or remove, any VRF IDs as needed.
absl::Status UpdateAppDbVrfTable(VrfTable &vrf_table,
                                 p4::v1::Update::Type update_type,
                                 int rpc_index, const pdpi::IrTableEntry &entry,
                                 pdpi::IrWriteResponse &response);

// Returns all the VRF_TABLE entries currently installed in the AppDb. This does
// not include any entries that are currently being handled by the lower layers
// (i.e. keys starting with _).
absl::StatusOr<std::vector<pdpi::IrTableEntry>>
GetAllAppDbVrfTableEntries(VrfTable &vrf_table);

} // namespace sonic
} // namespace p4rt_app

#endif // PINS_P4RT_APP_SONIC_VRF_ENTRY_TRANSLATION_H_
