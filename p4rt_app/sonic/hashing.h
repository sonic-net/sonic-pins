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
#ifndef PINS_INFRA_P4RT_APP_SONIC_HASHING_H_
#define PINS_INFRA_P4RT_APP_SONIC_HASHING_H_

#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "p4_pdpi/ir.h"
#include "p4rt_app/sonic/redis_connections.h"
#include "swss/table.h"

namespace p4rt_app {
namespace sonic {

struct EcmpHashEntry {
  std::string hash_key;
  std::vector<swss::FieldValueTuple> hash_value;
};

// Returns true for Ipv4 hash key.
bool IsIpv4HashKey(absl::string_view key);
// Returns true for Ipv6 hash key.
bool IsIpv6HashKey(absl::string_view key);

// Generates the APP_DB format for hash field entries to be written to
// HASH_TABLE.
// sai_native_hash_field annotations.
// @sai_ecmp_hash(SAI_SWITCH_ATTR_ECMP_HASH_IPV4)
// @sai_native_hash_field(SAI_NATIVE_HASH_FIELD_SRC_IPV4)
// @sai_native_hash_field(SAI_NATIVE_HASH_FIELD_DST_IPV4)
// @sai_native_hash_field(SAI_NATIVE_HASH_FIELD_L4_SRC_PORT)
// @sai_native_hash_field(SAI_NATIVE_HASH_FIELD_L4_DST_PORT)
//
// “hash_ipv4_config” = {
//    “hash_field_list”: [“src_ip”, “dst_ip”, “l4_src_port”, “l4_dst_port”,
//                        “ip_protocol”],
//  }
absl::StatusOr<std::vector<EcmpHashEntry>> GenerateAppDbHashFieldEntries(
    const pdpi::IrP4Info& ir_p4info);

// Generates the APP_DB format for hash value entries to be written to
// SWITCH_TABLE.
// “switch”: {
//    “ecmp_hash_algorithm”: “crc32_lo”,  # SAI_HASH_ALGORITHM_CRC32_LO
//    “ecmp_hash_seed”: “10”,
//    "ecmp_hash_offset": "10"
// }
absl::StatusOr<std::vector<swss::FieldValueTuple>>
GenerateAppDbHashValueEntries(const pdpi::IrP4Info& ir_p4info);

// Programs the APP_DB entries (HASH_TABLE) that specifies which fields are
// used for ECMP hashing (IPv4, IPv6), this creates the hash objects to
// be used in the SWITCH_TABLE later.
absl::StatusOr<std::vector<std::string>> ProgramHashFieldTable(
    HashTable& hash_table, const pdpi::IrP4Info& ir_p4info);

// Programs the APP_DB enries (SWITCH_TABLE) with all ecmp hashing related
// fields in the switch table, like algorithm, seed, offset and the hash field
// object.
absl::Status ProgramSwitchTable(SwitchTable& switch_table,
                                const pdpi::IrP4Info& ir_p4info,
                                const std::vector<std::string>& hash_fields);

}  // namespace sonic
}  // namespace p4rt_app

#endif  // PINS_INFRA_P4RT_APP_SONIC_HASHING_H_
