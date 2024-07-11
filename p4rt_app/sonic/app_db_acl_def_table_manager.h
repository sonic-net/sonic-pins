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
#ifndef PINS_P4RT_APP_SONIC_APP_DB_ACL_DEF_TABLE_MANAGER_H_
#define PINS_P4RT_APP_SONIC_APP_DB_ACL_DEF_TABLE_MANAGER_H_

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "p4_pdpi/ir.pb.h"
#include "p4rt_app/sonic/redis_connections.h"

namespace p4rt_app {
namespace sonic {

// Verify an ACL table definition can be inserted into the AppDB ACL Table
// Definition Table.
absl::Status VerifyAclTableDefinition(const pdpi::IrTableDefinition& ir_table);

// Insert an ACL table definition entry into the AppDB ACL Table Definition
// Table, returns the key that was used.
absl::StatusOr<std::string> InsertAclTableDefinition(
    P4rtTable& p4rt_table, const pdpi::IrTableDefinition& ir_table);

// Remove an ACL table definition entry from the AppDB ACL Table Definition
// Table.
absl::Status RemoveAclTableDefinition(P4rtTable& p4rt_table,
                                      const pdpi::IrTableDefinition& ir_table);

}  // namespace sonic
}  // namespace p4rt_app

#endif  // PINS_P4RT_APP_SONIC_APP_DB_ACL_DEF_TABLE_MANAGER_H_
