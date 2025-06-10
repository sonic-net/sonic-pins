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

#include <string>
#include <utility>
#include <vector>

#include "absl/container/btree_map.h"
#include "absl/container/btree_set.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "absl/types/span.h"
#include "google/rpc/code.pb.h"
#include "gutil/gutil/status.h"
#include "include/nlohmann/json.hpp"
#include "p4_infra/p4_pdpi/annotation_parser.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4rt_app/sonic/redis_connections.h"
#include "p4rt_app/sonic/response_handler.h"
#include "swss/rediscommand.h"

namespace p4rt_app {
namespace sonic {
namespace {

static constexpr absl::string_view kHashFieldLabel = "sai_native_hash_field";

// Hashing configurations will be marked at least one hash config annotation.
// All hash config annotations have the form of: sai_hash_*
//   Examples: sai_hash_algorithm, sai_hash_offset, sai_hash_seed
bool ActionHasHashingConfig(const pdpi::IrActionDefinition& action_def) {
  for (const auto& annotation :
       pdpi::GetAllAnnotations(action_def.preamble().annotations())) {
    if (absl::StartsWith(annotation.label, "sai_hash_")) return true;
  }
  return false;
}

absl::StatusOr<std::string> SwitchTableHashPacketFieldConfigKey(
    absl::string_view hash_key) {
  static const auto* const kFieldKeyMap =
      new absl::flat_hash_map<std::string, std::string>({
          {"compute_ecmp_hash_ipv4", "ecmp_hash_ipv4"},
          {"compute_ecmp_hash_ipv6", "ecmp_hash_ipv6"},
          {"compute_lag_hash_ipv4", "lag_hash_ipv4"},
          {"compute_lag_hash_ipv6", "lag_hash_ipv6"},
      });
  auto result = kFieldKeyMap->find(hash_key);
  if (result == kFieldKeyMap->end()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Unsupported hash field configuration '" << hash_key << "'.";
  }
  return result->second;
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

absl::StatusOr<std::string> AppDbHashAlgorithm(absl::string_view p4_algorithm) {
  auto result = GetAvailableHashAlgorithms().find(p4_algorithm);
  if (result == GetAvailableHashAlgorithms().end()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "[P4RT App] Unsupported hash algorithm '" << p4_algorithm << "'.";
  }
  return result->second;
}

absl::StatusOr<std::string> AppDbFieldName(absl::string_view field) {
  static const auto* const kTranslationMap =
      new absl::flat_hash_map<std::string, std::string>({
          {"SAI_NATIVE_HASH_FIELD_SRC_IPV4", "src_ip"},
          {"SAI_NATIVE_HASH_FIELD_DST_IPV4", "dst_ip"},
          {"SAI_NATIVE_HASH_FIELD_SRC_IPV6", "src_ip"},
          {"SAI_NATIVE_HASH_FIELD_DST_IPV6", "dst_ip"},
          {"SAI_NATIVE_HASH_FIELD_L4_SRC_PORT", "l4_src_port"},
          {"SAI_NATIVE_HASH_FIELD_L4_DST_PORT", "l4_dst_port"},
          {"SAI_NATIVE_HASH_FIELD_IPV6_FLOW_LABEL", "ipv6_flow_label"},
      });
  auto result = kTranslationMap->find(field);
  if (result == kTranslationMap->end()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Cannot process unknown hash field: '" << field << "'";
  }
  return result->second;
}

// Generates a HashPacketFieldConfig from an action name and annotation arg
// list.
absl::StatusOr<HashPacketFieldConfig> HashPacketFieldConfigFromAction(
    absl::string_view action_name,
    std::vector<std::vector<std::string>> arg_lists) {
  HashPacketFieldConfig hash_field_config;
  hash_field_config.key = action_name;
  ASSIGN_OR_RETURN(hash_field_config.switch_table_key,
                   SwitchTableHashPacketFieldConfigKey(action_name));

  for (const auto& hash_args : arg_lists) {
    if (hash_args.size() != 1) {
      return gutil::InvalidArgumentErrorBuilder()
             << "@" << kHashFieldLabel
             << " annotations may only contain one argument. Found invalid "
             << "annotation body: '" << absl::StrJoin(hash_args, ", ") << "'";
    }
    ASSIGN_OR_RETURN(std::string hash_field, AppDbFieldName(hash_args.at(0)));
    hash_field_config.fields.insert(hash_field);
  }
  return hash_field_config;
}

// Inserts a new hash config into the config map.
//   If the config already exists, returns an error.
//   If the label is an unknown sai_hash_ label, returns an error.
//   If this label is not a sai_hash_ label, returns OK and does nothing.
absl::Status InsertHashParamConfig(absl::string_view label,
                                   absl::string_view hash_type,
                                   absl::string_view value,
                                   HashParamConfigs& configs) {
  if (!absl::StartsWith(label, "sai_hash_")) return absl::OkStatus();
  if (label != "sai_hash_seed" && label != "sai_hash_offset" &&
      label != "sai_hash_algorithm") {
    return gutil::InvalidArgumentErrorBuilder()
           << "Invalid sai_hash_* annotation '@" << label << "'";
  }
  if (!configs
           .insert({absl::StrCat(hash_type, label.substr(/*sai*/ 3)),
                    std::string(value)})
           .second) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Found duplicate '" << hash_type << "' hash config annotation '@"
           << label << "'";
  }
  return absl::OkStatus();
}

absl::Status UpdateHashParamConfigsFromAction(
    const pdpi::IrActionDefinition& action, HashParamConfigs& configs) {
  std::string full_action_name = action.preamble().name();
  std::string hash_type;
  if (absl::StrContainsIgnoreCase(full_action_name, "_lag_")) {
    hash_type = "lag";
  } else if (absl::StrContainsIgnoreCase(full_action_name, "_ecmp_")) {
    hash_type = "ecmp";
  } else {
    return gutil::InvalidArgumentErrorBuilder()
           << "Unsupported hash configuration '" << full_action_name
           << "' name refers to neither '_ecmp_' nor '_lag_'.";
  }
  for (const auto& annotation :
       pdpi::GetAllAnnotations(action.preamble().annotations())) {
    if (annotation.label == "sai_hash_algorithm") {
      ASSIGN_OR_RETURN(
          std::string algorithm, AppDbHashAlgorithm(annotation.body),
          _ << " in action '" << full_action_name << "' annotation '@"
            << annotation.label << "(" << annotation.body << ")'");
      RETURN_IF_ERROR(InsertHashParamConfig(annotation.label, hash_type,
                                            algorithm, configs))
          << " in action '" << full_action_name << "'";
    } else {
      RETURN_IF_ERROR(InsertHashParamConfig(annotation.label, hash_type,
                                            annotation.body, configs))
          << " in action '" << full_action_name << "'";
    }
  }
  return absl::OkStatus();
}

}  // namespace

bool IsIpv4HashKey(absl::string_view key) {
  return absl::StrContains(key, "ipv4");
}

bool IsIpv6HashKey(absl::string_view key) {
  return absl::StrContains(key, "ipv6");
}

std::vector<swss::FieldValueTuple> HashPacketFieldConfig::AppDbContents()
    const {
  nlohmann::json field_json;
  for (const auto& field : fields) field_json.push_back(field);
  return {{"hash_field_list", field_json.dump()}};
}

absl::StatusOr<absl::btree_set<HashPacketFieldConfig>>
ExtractHashPacketFieldConfigs(const pdpi::IrP4Info& ir_p4info) {
  absl::btree_set<HashPacketFieldConfig> hash_field_configs;
  for (const auto& [action_name, action_def] : ir_p4info.actions_by_name()) {
    auto arg_lists = pdpi::GetAllAnnotationsAsArgList(
        kHashFieldLabel, action_def.preamble().annotations());
    if (!arg_lists.ok() || arg_lists->empty()) continue;
    ASSIGN_OR_RETURN(auto config,
                     HashPacketFieldConfigFromAction(action_name, *arg_lists));
    hash_field_configs.insert(std::move(config));
  }
  return hash_field_configs;
}

absl::StatusOr<HashParamConfigs> ExtractHashParamConfigs(
    const pdpi::IrP4Info& ir_p4info) {
  HashParamConfigs configs;
  for (const auto& [name, action] : ir_p4info.actions_by_name()) {
    if (!ActionHasHashingConfig(action)) continue;
    RETURN_IF_ERROR(UpdateHashParamConfigsFromAction(action, configs));
  }
  return configs;
}

absl::Status ProgramHashFieldTable(
     HashTable& hash_table,
     const absl::btree_set<HashPacketFieldConfig>& configs) {
  if (configs.empty()) return absl::OkStatus();
  LOG(INFO) << "Apply hash fields: \n "
            << absl::StrJoin(configs, "\n  ",
                             HashPacketFieldConfig::AbslFormatter);

  // Write to APP_DB.
  pdpi::IrWriteResponse update_status;
  absl::btree_map<std::string, pdpi::IrUpdateStatus*> status_by_key;
  for (const auto& config : configs) {
    hash_table.producer_state->set(config.key, config.AppDbContents());
    status_by_key[config.key] = update_status.add_statuses();
  }

  // Wait for the OrchAgent's response.
  RETURN_IF_ERROR(GetAndProcessResponseNotification(
      *hash_table.notification_consumer, *hash_table.app_db,
      *hash_table.app_state_db, status_by_key));

  // Pickup the hash field keys that were written(and ack'ed) successfully by
  // OrchAgent.
  for (const auto& [key, status] : status_by_key) {
    if (status->code() != google::rpc::Code::OK) {
      return gutil::InternalErrorBuilder()
             << "Could not write key '" << key
             << "' into the AppDb HASH_TABLE: " << status->message();
    }
  }
  return absl::OkStatus();
}

absl::Status RemoveFromHashFieldTable(
     HashTable& hash_table, absl::Span<const std::string> config_keys) {
   if (config_keys.empty()) return absl::OkStatus();
   LOG(INFO) << "Removing hash fields: {" << absl::StrJoin(config_keys, ", ")
             << "}";
   pdpi::IrWriteResponse update_status;
   absl::btree_map<std::string, pdpi::IrUpdateStatus*> status_by_key;
   for (const auto& key : config_keys) {
     hash_table.producer_state->del(key);
     status_by_key[key] = update_status.add_statuses();
   }

   // Wait for the OrchAgent's response.
   RETURN_IF_ERROR(GetAndProcessResponseNotification(
       *hash_table.notification_consumer, *hash_table.app_db,
       *hash_table.app_state_db, status_by_key));

   for (const auto& [key, status] : status_by_key) {
     if (status->code() != google::rpc::Code::OK) {
       return gutil::InternalErrorBuilder()
              << "Could not delete key '" << key
              << "' from AppDb HASH_TABLE: " << status->message();
     }
   }
   return absl::OkStatus();
 }
absl::Status ProgramSwitchTable(
    SwitchTable& switch_table, const HashParamConfigs& hash_params,
    const absl::btree_set<HashPacketFieldConfig>& hash_packet_fields) {
  const std::string kSwitchTableEntryKey = "switch";

  std::vector<swss::FieldValueTuple> hash_tuples;
  for (const auto& [field, value] : hash_params) {
    hash_tuples.push_back({field, value});
  }
  for (const auto& field : hash_packet_fields) {
    hash_tuples.push_back({field.switch_table_key, field.key});
  }
  if (hash_tuples.empty()) return absl::OkStatus();

  LOG(INFO) << "Applying hash config: \n  "
            << absl::StrJoin(hash_tuples, "\n  ", absl::PairFormatter(": "));

  // Write to switch table and process response.
  switch_table.producer_state->set(kSwitchTableEntryKey, hash_tuples);

  ASSIGN_OR_RETURN(
      pdpi::IrUpdateStatus status,
      GetAndProcessResponseNotification(
          *switch_table.notification_consumer, *switch_table.app_db,
          *switch_table.app_state_db, kSwitchTableEntryKey));

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
