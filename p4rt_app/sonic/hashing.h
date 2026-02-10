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
#ifndef PINS_P4RT_APP_SONIC_HASHING_H_
#define PINS_P4RT_APP_SONIC_HASHING_H_

#include <string>
#include <vector>

#include "absl/container/btree_map.h"
#include "absl/container/btree_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "absl/types/span.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4rt_app/sonic/redis_connections.h"
#include "swss/rediscommand.h"
#include "swss/table.h"

namespace p4rt_app {
namespace sonic {

using HashParamConfigs = absl::btree_map<std::string, std::string>;

// Struct containing an ECMP hash field config.
struct HashPacketFieldConfig {
  std::string key;
  absl::btree_set<std::string> fields;
  std::string switch_table_key;

  std::vector<swss::FieldValueTuple> AppDbContents() const;

  // String conversion for debug.
  // E.g. compute_ecmp_hash_ipv4 { "src_ip","dst_ip" }
  static void AbslFormatter(std::string *out,
                            const HashPacketFieldConfig &config) {
    absl::StrAppendFormat(out, "%s { %s }", config.key,
                          absl::StrJoin(config.fields, ", "));
  }
};

inline bool operator==(const HashPacketFieldConfig& lhs,
                        const HashPacketFieldConfig& rhs) {
   return lhs.key == rhs.key && lhs.switch_table_key == rhs.switch_table_key &&
          lhs.fields == rhs.fields;
}

inline bool operator!=(const HashPacketFieldConfig& lhs,
                        const HashPacketFieldConfig& rhs) {
   return !(lhs == rhs);
}

inline bool operator<(const HashPacketFieldConfig& lhs,
                       const HashPacketFieldConfig& rhs) {
   return lhs.key < rhs.key;
}

inline bool operator>(const HashPacketFieldConfig& lhs,
                       const HashPacketFieldConfig& rhs) {
   return lhs.key > rhs.key;
}

// Returns true for Ipv4 hash key.
bool IsIpv4HashKey(absl::string_view key);
// Returns true for Ipv6 hash key.
bool IsIpv6HashKey(absl::string_view key);

// Generates the APP_DB format for hash value entries to be written to
// SWITCH_TABLE.
// “switch”: {
//    “ecmp_hash_algorithm”: “crc32_lo”,  # SAI_HASH_ALGORITHM_CRC32_LO
//    “ecmp_hash_seed”: “10”,
//    "ecmp_hash_offset": "10"
// }
absl::StatusOr<std::vector<swss::FieldValueTuple>>
GenerateAppDbHashValueEntries(const pdpi::IrP4Info &ir_p4info);

// Generates a list of hash field configs from the IrP4Info. These configs can
// be written to APP_DB to set up the hash fields via ProgramHashFieldTable().
//
// Each config maps to a P4 Action which contains one @sai_native_hash_field
// annotation per hash field:
//
//   @sai_ecmp_hash(SAI_SWITCH_ATTR_ECMP_HASH_IPV4)
//   @sai_native_hash_field(SAI_NATIVE_HASH_FIELD_SRC_IPV4)
//   @sai_native_hash_field(SAI_NATIVE_HASH_FIELD_DST_IPV4)
//   @sai_native_hash_field(SAI_NATIVE_HASH_FIELD_L4_SRC_PORT)
//   @sai_native_hash_field(SAI_NATIVE_HASH_FIELD_L4_DST_PORT)
//   action compute_ecmp_hash_ipv4() { ... }
//
// Example output:
//  {
//    .key: "compute_ecmp_hash_ipv4",
//    .fields: {"src_ip", "dst_ip", "l4_src_prt", "l4_dst_port"},
//    .switch_table_key: "ecmp_hash_ipv4"
//  }
absl::StatusOr<absl::btree_set<HashPacketFieldConfig>>
ExtractHashPacketFieldConfigs(const pdpi::IrP4Info &ir_p4info);

// Generates a list of hash value configs from the IrP4Info. These configs can
// be written to the APP_DB to set up the hash fields via ProgramSwitchTable().
//
//   @sai_hash_algorithm(LAG_HASH_ALGORITHM)
//   @sai_hash_seed(LAG_HASH_SEED)
//   @sai_hash_offset(LAG_HASH_OFFSET)
//   action select_lag_hash_algorithm() { ... }
//
//   @sai_hash_algorithm(ECMP_HASH_ALGORITHM)
//   @sai_hash_seed(ECMP_HASH_SEED)
//   @sai_hash_offset(ECMP_HASH_OFFSET)
//   action select_ecmp_hash_algorithm() { ... }
//
// Example output:
//   {"ecmp_hash_algorithm", "crc_32lo"},
//   {"ecmp_hash_seed", "1"},
//   {"lag_hash_algorithm",  "crc_32"},
//   {"lag_hash_seed",  "10"},
//   {"lag_hash_offset", "20"},
absl::StatusOr<HashParamConfigs>
ExtractHashParamConfigs(const pdpi::IrP4Info &ir_p4info);

// Programs the APP_DB entries (HASH_TABLE) that specifies which fields are
// used for ECMP hashing (IPv4, IPv6), this creates the hash objects to
// be used in the SWITCH_TABLE later.
//
// Example entry:
//
//   “hash_ipv4_config” = {
//      “hash_field_list”: [“src_ip”, “dst_ip”, “l4_src_port”, “l4_dst_port”,
//                          “ip_protocol”],
absl::Status ProgramHashFieldTable(
     HashTable& hash_table,
     const absl::btree_set<HashPacketFieldConfig>& configs);

// Removes APP_DB HASH_TABLE entries previously added by
// ProgramHashFieldTable(). Any call to RemoveFromHashFieldTable() should be
// followed by a call to ProgramSwitchTable with the newly reduced config set.
absl::Status RemoveFromHashFieldTable(
    HashTable& hash_table, absl::Span<const std::string> config_keys);

// Programs the APP_DB enries (SWITCH_TABLE) with all ecmp hashing related
// fields in the switch table, like algorithm, seed, offset and the hash field
// object.
absl::Status ProgramSwitchTable(
    SwitchTable &switch_table, const HashParamConfigs &hash_params,
    const absl::btree_set<HashPacketFieldConfig> &hash_packet_fields);

} // namespace sonic
} // namespace p4rt_app

#endif // PINS_P4RT_APP_SONIC_HASHING_H_
