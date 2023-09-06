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
#include "p4rt_app/sonic/hashing.h"

#include "absl/container/btree_map.h"
#include "absl/container/flat_hash_map.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/str_join.h"
#include "glog/logging.h"
#include "google/rpc/code.pb.h"
#include "gutil/collections.h"
#include "gutil/status.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/utils/annotation_parser.h"
#include "p4rt_app/sonic/redis_connections.h"
#include "p4rt_app/sonic/response_handler.h"
#include "swss/json.h"
#include <nlohmann/json.hpp>
#include "swss/rediscommand.h"

namespace p4rt_app {
namespace sonic {
namespace {

// Hashing configurations will be marked with a 'sai_hash_algorithm' annotation.
bool ActionHasHashingConfig(const pdpi::IrActionDefinition& action_def) {
  return pdpi::GetAllAnnotationsAsArgList("sai_hash_algorithm",
                                          action_def.preamble().annotations())
      .ok();
}

// Hashing configurations can apply to multiple parts of the dataplane, and
// depending on the path we need to use different AppDb values.
enum class HashConfigType { kECMP, kLag };

absl::StatusOr<HashConfigType> GetHashConfigType(
    absl::string_view action_name) {
  if (action_name == "select_ecmp_hash_algorithm") return HashConfigType::kECMP;
  if (action_name == "select_lag_hash_algorithm") return HashConfigType::kLag;

  if (action_name == "compute_ecmp_hash_ipv6") return HashConfigType::kECMP;
  if (action_name == "compute_lag_hash_ipv6") return HashConfigType::kLag;

  if (action_name == "compute_ecmp_hash_ipv4") return HashConfigType::kECMP;
  if (action_name == "compute_lag_hash_ipv4") return HashConfigType::kLag;

  return gutil::InvalidArgumentErrorBuilder()
         << "Unsupported hash configuration '" << action_name << "'.";
}

// Map of supported SAI hashing algorithms. This is a reverse mapping of
// hash_algorithm_map in sonic-swss/orchagent/switchorch.cpp
const absl::flat_hash_map<std::string, std::string>&
GetAvailableHashAlgorithms() {
  static const auto* const kHashAlgorithms =
      new absl::flat_hash_map<std::string, std::string>{
          {"SAI_HASH_ALGORITHM_CRC", "crc"},
          {"SAI_HASH_ALGORITHM_XOR", "xor"},
          {"SAI_HASH_ALGORITHM_RANDOM", "random"},
          {"SAI_HASH_ALGORITHM_CRC_32LO", "crc_32lo"},
          {"SAI_HASH_ALGORITHM_CRC_32HI", "crc_32hi"},
          {"SAI_HASH_ALGORITHM_CRC_CCITT", "crc_ccitt"},
          {"SAI_HASH_ALGORITHM_CRC_XOR", "crc_xor"},
      };
  return *kHashAlgorithms;
}

absl::StatusOr<swss::FieldValueTuple> GetHashAlgorithm(
    HashConfigType hash_config, const std::string& algoritm) {
  auto iter = GetAvailableHashAlgorithms().find(algoritm);
  if (iter == GetAvailableHashAlgorithms().end()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "[P4RT App] Unsupported hash algorithm '" << algoritm << "'.";
  }

  std::string entry_name;
  switch (hash_config) {
    case HashConfigType::kECMP:
      entry_name = "ecmp_hash_algorithm";
      break;
    case HashConfigType::kLag:
      entry_name = "lag_hash_algorithm";
      break;
  }
  return swss::FieldValueTuple{entry_name, iter->second};
}

swss::FieldValueTuple GetHashSeed(HashConfigType hash_config,
                                  const std::string& seed) {
  std::string entry_name;
  switch (hash_config) {
    case HashConfigType::kECMP:
      entry_name = "ecmp_hash_seed";
      break;
    case HashConfigType::kLag:
      entry_name = "lag_hash_seed";
      break;
  }
  return swss::FieldValueTuple{entry_name, seed};
}

swss::FieldValueTuple GetHashOffset(HashConfigType hash_config,
                                    const std::string& offset) {
  std::string entry_name;
  switch (hash_config) {
    case HashConfigType::kECMP:
      entry_name = "ecmp_hash_offset";
      break;
    case HashConfigType::kLag:
      entry_name = "lag_hash_offset";
      break;
  }
  return swss::FieldValueTuple{entry_name, offset};
}

std::string GetIpv4Hash(HashConfigType hash_type) {
  switch (hash_type) {
    case HashConfigType::kECMP:
      return "ecmp_hash_ipv4";
    case HashConfigType::kLag:
      return "lag_hash_ipv4";
  }
  return "";
}

std::string GetIpv6Hash(HashConfigType hash_type) {
  switch (hash_type) {
    case HashConfigType::kECMP:
      return "ecmp_hash_ipv6";
    case HashConfigType::kLag:
      return "lag_hash_ipv6";
  }
  return "";
}

// Generate the JSON format for HASH_TABLE entries with sai_ecmp_hash and
// sai_native_hash_field annotations.
// @sai_ecmp_hash(SAI_SWITCH_ATTR_ECMP_HASH_IPV4)
// @sai_native_hash_field(SAI_NATIVE_HASH_FIELD_SRC_IPV4)
// @sai_native_hash_field(SAI_NATIVE_HASH_FIELD_DST_IPV4)
// @sai_native_hash_field(SAI_NATIVE_HASH_FIELD_L4_SRC_PORT)
// @sai_native_hash_field(SAI_NATIVE_HASH_FIELD_L4_DST_PORT)
//
// JSON:
// “HASH_TABLE:hash_ipv4_config” = {
//    “hash_field_list”: [“src_ip”, “dst_ip”, “l4_src_port”, “l4_dst_port”,
//                        “ip_protocol”],
// }
absl::StatusOr<nlohmann::json> GenerateJsonHashFieldEntries(
    const std::vector<std::vector<std::string>>& parse_results) {
  const absl::flat_hash_map<std::string, std::string> hash_fields_map = {
      {"SAI_NATIVE_HASH_FIELD_SRC_IPV4", "src_ip"},
      {"SAI_NATIVE_HASH_FIELD_DST_IPV4", "dst_ip"},
      {"SAI_NATIVE_HASH_FIELD_SRC_IPV6", "src_ip"},
      {"SAI_NATIVE_HASH_FIELD_DST_IPV6", "dst_ip"},
      {"SAI_NATIVE_HASH_FIELD_L4_SRC_PORT", "l4_src_port"},
      {"SAI_NATIVE_HASH_FIELD_L4_DST_PORT", "l4_dst_port"},
      {"SAI_NATIVE_HASH_FIELD_IPV6_FLOW_LABEL", "ipv6_flow_label"},
  };

  nlohmann::json json;

  for (const auto& fields : parse_results) {
    if (fields.size() != 1) {
      return gutil::InvalidArgumentErrorBuilder()
             << "Unexpected number of native hash field specified: "
             << "expected 1, actual " << fields.size();
    }
    ASSIGN_OR_RETURN(
        auto field_value, gutil::FindOrStatus(hash_fields_map, fields.at(0)),
        _ << "Unable to find hash field string for " << fields.at(0));
    json.push_back(field_value);
  }

  return json;
}

}  // namespace

bool IsIpv4HashKey(absl::string_view key) {
  return absl::StrContains(key, "ipv4");
}

bool IsIpv6HashKey(absl::string_view key) {
  return absl::StrContains(key, "ipv6");
}

// Generate the APP_DB format for hash field entries to be written to
// HASH_TABLE.
absl::StatusOr<std::vector<EcmpHashEntry>> GenerateAppDbHashFieldEntries(
    const pdpi::IrP4Info& ir_p4info) {
  std::vector<EcmpHashEntry> hash_entries;
  for (const auto& [action_name, action_def] : ir_p4info.actions_by_name()) {
    auto parse_results = pdpi::GetAllAnnotationsAsArgList(
        "sai_native_hash_field", action_def.preamble().annotations());
    if (!parse_results.ok()) continue;
    auto json = GenerateJsonHashFieldEntries(*parse_results);
    if (!json.ok()) {
      return gutil::InvalidArgumentErrorBuilder()
             << "Unable to generate hash field action annotation entries "
             << json.status();
    } else {
      hash_entries.push_back(EcmpHashEntry(
          {action_name, std::vector<swss::FieldValueTuple>(
                            {{"hash_field_list", (*json).dump()}})}));
    }
  }
  if (hash_entries.empty()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Missing hash field entries in P4Info file.";
  }
  return hash_entries;
}

absl::StatusOr<std::vector<swss::FieldValueTuple>>
GenerateAppDbHashValueEntries(const pdpi::IrP4Info& ir_p4info) {
  absl::flat_hash_set<std::string> hash_values_set;
  std::vector<swss::FieldValueTuple> hash_value_entries;

  // Go through all the actions from the IrP4Info and if they specify a hashing
  // configuration generate AppDb entries.
  for (const auto& [action_name, action_def] : ir_p4info.actions_by_name()) {
    if (!ActionHasHashingConfig(action_def)) continue;

    // We only support certain types of hashing configs so make sure the action
    // matches expectations.
    ASSIGN_OR_RETURN(HashConfigType hash_type, GetHashConfigType(action_name));

    // Expect to get all hashing value related annotations like algorithm,
    // offset, seed etc.
    bool has_algorithm = false;
    bool has_offset = false;
    bool has_seed = false;

    for (const auto& annotation :
         pdpi::GetAllAnnotations(action_def.preamble().annotations())) {
      swss::FieldValueTuple fv;
      if (annotation.label == "sai_hash_algorithm") {
        ASSIGN_OR_RETURN(fv, GetHashAlgorithm(hash_type, annotation.body),
                         _.SetAppend()
                             << " Found in action '" << action_name << "'.");
        has_algorithm = true;
      } else if (annotation.label == "sai_hash_seed") {
        fv = GetHashSeed(hash_type, annotation.body);
        has_seed = true;
      } else if (annotation.label == "sai_hash_offset") {
        fv = GetHashOffset(hash_type, annotation.body);
        has_offset = true;
      } else {
        return gutil::InvalidArgumentErrorBuilder()
               << "Unexpected hash configuration '" << annotation.label
               << "' in action '" << action_name << "'.";
      }
      // Do not allow duplicate configurations.
      auto [_, success] = hash_values_set.insert(fv.first);
      if (!success) {
        return gutil::InvalidArgumentErrorBuilder()
               << "Duplicate hash configurations are not allowed for '"
               << fv.first << "'.";
      }
      hash_value_entries.push_back(fv);
    }

    std::vector<std::string> missing;
    if (!has_algorithm) missing.push_back("algorithm");
    if (!has_offset) missing.push_back("offset");
    if (!has_seed) missing.push_back("seed");
    if (!missing.empty()) {
      return gutil::InvalidArgumentErrorBuilder()
             << "Hash configuration for '" << action_name
             << "' is missing: " << absl::StrJoin(missing, ", ");
    }
  }
  if (hash_value_entries.empty()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Could not find action with hashing algorithm in the P4Info.";
  }
  return hash_value_entries;
}

absl::StatusOr<std::vector<std::string>> ProgramHashFieldTable(
    HashTable& hash_table, const pdpi::IrP4Info& ir_p4info) {
  // Get the key, value pairs of Hash field APP_DB entries.
  ASSIGN_OR_RETURN(const auto entries,
                   GenerateAppDbHashFieldEntries(ir_p4info));

  // Write to APP_DB.
  pdpi::IrWriteResponse update_status;
  absl::btree_map<std::string, pdpi::IrUpdateStatus*> status_by_key;
  for (const auto& entry : entries) {
    hash_table.producer_state->set(entry.hash_key, entry.hash_value);
    status_by_key[entry.hash_key] = update_status.add_statuses();
  }

  // Wait for the OrchAgent's repsonse.
  pdpi::IrWriteResponse ir_write_response;
  RETURN_IF_ERROR(GetAndProcessResponseNotification(
      *hash_table.notifier, *hash_table.app_db, *hash_table.app_state_db,
      status_by_key, ResponseTimeMonitor::kNone));

  // Pickup the hash field keys that were written(and ack'ed) successfully by
  // OrchAgent.
  std::vector<std::string> hash_field_keys;
  for (const auto& [key, status] : status_by_key) {
    if (status->code() == google::rpc::Code::OK) {
      hash_field_keys.push_back(key);
    } else {
      return gutil::InternalErrorBuilder()
             << "Could not write key '" << key
             << "' into the AppDb HASH_TABLE: " << status->message();
    }
  }
  return hash_field_keys;
}

absl::Status ProgramSwitchTable(SwitchTable& switch_table,
                                const pdpi::IrP4Info& ir_p4info,
                                const std::vector<std::string>& hash_fields) {
  const std::string kSwitchTableEntryKey = "switch";
  std::vector<swss::FieldValueTuple> switch_table_attrs;

  // Get all the hash value related attributes like algorithm type, offset and
  // seed value etc.
  ASSIGN_OR_RETURN(switch_table_attrs,
                   GenerateAppDbHashValueEntries(ir_p4info));

  // Add the ecmp hash fields for Ipv4 & Ipv6.
  for (const auto& hash_field_key : hash_fields) {
    // We only support certain types of hashing configs so make sure the field
    // matches expectations.
    ASSIGN_OR_RETURN(HashConfigType hash_type,
                     GetHashConfigType(hash_field_key));

    if (IsIpv4HashKey(hash_field_key)) {
      switch_table_attrs.push_back(
          swss::FieldValueTuple({GetIpv4Hash(hash_type), hash_field_key}));
    } else if (IsIpv6HashKey(hash_field_key)) {
      switch_table_attrs.push_back(
          swss::FieldValueTuple({GetIpv6Hash(hash_type), hash_field_key}));
    } else {
      return gutil::InvalidArgumentErrorBuilder()
             << "Invalid hash field key: " << hash_field_key;
    }
  }

  // Write to switch table and process response.
  switch_table.producer_state->set(kSwitchTableEntryKey, switch_table_attrs);

  ASSIGN_OR_RETURN(pdpi::IrUpdateStatus status,
                   GetAndProcessResponseNotification(
                       *switch_table.notifier, *switch_table.app_db,
                       *switch_table.app_state_db, kSwitchTableEntryKey,
                       ResponseTimeMonitor::kNone));

  // Failing to program the switch table should never happen so we return an
  // internal error.
  if (status.code() != google::rpc::OK) {
    return gutil::InternalErrorBuilder()
           << "Could not write 'SWITCH_TABLE:" << kSwitchTableEntryKey
           << "' into the AppDb: " << status.message();
  }

  return absl::OkStatus();
}

}  // namespace sonic
}  // namespace p4rt_app
