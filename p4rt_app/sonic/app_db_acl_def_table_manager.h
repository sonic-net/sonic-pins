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

#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/types/span.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4rt_app/sonic/redis_connections.h"
#include "swss/rediscommand.h"

namespace p4rt_app {
namespace sonic {

// Insert an ACL table definition entry into the AppDB ACL Table Definition
// Table, returns the key that was used.
absl::StatusOr<std::string>
InsertAclTableDefinition(P4rtTable &p4rt_table,
                         const pdpi::IrTableDefinition &ir_table);

// Remove an ACL table definition entry from the AppDB ACL Table Definition
// Table.
absl::Status RemoveAclTableDefinition(P4rtTable &p4rt_table,
                                      const pdpi::IrTableDefinition &ir_table);

// Create and return the AppDB representation of an ACL table definition.
//
// Example AppDB Table
//  P4RT_ACL_TABLE_DEFINITION:P4RT_ACL_PUNT_TABLE
//    "stage" = "INGRESS"
//    "match/ether_type" = "SAI_ACL_ENTRY_ATTR_FIELD_ETHER_TYPE"
//    "match/ether_dst" = "SAI_ACL_ENTRY_ATTR_FIELD_DST_MAC"
//    "match/ipv6_dst" = "SAI_ACL_ENTRY_ATTR_FIELD_DST_IPV6"
//    "match/ipv6_next_header" = "SAI_ACL_ENTRY_ATTR_FIELD_IPV6_NEXT_HEADER"
//    "match/ttl" = "SAI_ACL_ENTRY_ATTR_FIELD_TTL"
//    "match/icmp_type" = "SAI_ACL_ENTRY_ATTR_FIELD_ICMP_TYPE"
//    "match/l4_dst_port" = "SAI_ACL_ENTRY_ATTR_FIELD_L4_DST_PORT"
//    "action/copy_and_set_tc" = JsonToString([
//      {"action": "SAI_PACKET_ACTION_COPY"},
//      {"action": "SAI_ACL_ENTRY_ATTR_ACTION_SET_TC", "param": "traffic_class"}
//    ])
//    "action/punt_and_set_tc" = JsonToString([
//      {"action": "SAI_PACKET_ACTION_PUNT"},
//      {"action": "SAI_ACL_ENTRY_ATTR_ACTION_SET_TC", "param": "traffic_class"}
//    ])
//    "meter/unit" = "BYTES"
//    "counter/unit" = "PACKETS"
//    "size" = "123"
//    "priority" = "234"
absl::StatusOr<swss::KeyOpFieldsValuesTuple> AppDbAclTableDefinition(
    const pdpi::IrTableDefinition& ir_table);

// Verify an ACL table definition can be inserted into the AppDB ACL Table
// Definition Table.
inline absl::Status VerifyAclTableDefinition(
    const pdpi::IrTableDefinition& ir_table) {
  return AppDbAclTableDefinition(ir_table).status();
}

}  // namespace sonic
}  // namespace p4rt_app

#endif // PINS_P4RT_APP_SONIC_APP_DB_ACL_DEF_TABLE_MANAGER_H_
