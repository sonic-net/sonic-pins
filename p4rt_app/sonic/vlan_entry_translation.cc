// Copyright 2025 Google LLC
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

#include "p4rt_app/sonic/vlan_entry_translation.h"

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "absl/log/log.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "gutil/gutil/status.h"
#include "p4_pdpi/ir.pb.h"
#include "p4rt_app/sonic/redis_connections.h"
#include "p4rt_app/sonic/response_handler.h"
#include "swss/rediscommand.h"
#include "swss/schema.h"
#include "swss/table.h"

namespace p4rt_app {
namespace sonic {
namespace {

constexpr absl::string_view kVlanPrefix = "Vlan";  // expected by SONiC
constexpr absl::string_view kVlanTableName = "vlan_table";
constexpr absl::string_view kVlanMemberTableName = "vlan_membership_table";
constexpr absl::string_view kActionMakeTaggedMemberName = "make_tagged_member";
constexpr absl::string_view kActionMakeUntaggedMemberName =
    "make_untagged_member";
constexpr absl::string_view kMatchPort = "port";
constexpr absl::string_view kMatchVlanId = "vlan_id";

std::vector<swss::FieldValueTuple> GetVlanValues(
    const pdpi::IrTableEntry& entry) {
  std::vector<swss::FieldValueTuple> result = {{"source", "P4"}};
  if (!entry.controller_metadata().empty()) {
    result.push_back(
        std::make_pair("controller_metadata", entry.controller_metadata()));
  }
  return result;
}

std::vector<swss::FieldValueTuple> GetVlanMemberValues(
    const pdpi::IrTableEntry& entry) {
  std::vector<swss::FieldValueTuple> result = {{"source", "P4"}};
  bool tagged = entry.action().name() == kActionMakeTaggedMemberName;
  result.push_back(
      std::make_pair("tagging_mode", tagged ? "tagged" : "untagged"));
  if (!entry.controller_metadata().empty()) {
    result.push_back(
        std::make_pair("controller_metadata", entry.controller_metadata()));
  }
  return result;
}

absl::StatusOr<std::string> StripVlanPrefixAndReturnHexString(
    const std::string& app_db_key) {
  if (!absl::StartsWith(app_db_key, kVlanPrefix)) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Invalid VLAN_TABLE App DB key: '" << app_db_key << "'. "
           << "Expecting " << kVlanPrefix << "<id>";
  }
  uint32_t vlan_id = 0;
  if (!absl::SimpleAtoi(app_db_key.substr(4), &vlan_id)) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Failed to convert AppDB key to vlan ID: " << app_db_key;
  }
  if (vlan_id > 4095) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Vlan ID is outside allowed range of [0:4095]: " << app_db_key;
  }
  return absl::StrFormat("0x%03x", vlan_id);
}

absl::StatusOr<std::pair<std::string, std::string>>
ExtractVlanIdAndPortIdFromMemberKey(const std::string& app_db_key) {
  const std::vector<std::string> split = absl::StrSplit(app_db_key, ':');
  if (split.size() != 2) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Failed to parse VLAN_MEMBER_TABLE AppDB key: " << app_db_key;
  }

  ASSIGN_OR_RETURN(std::string vlan_id_as_hex,
                   StripVlanPrefixAndReturnHexString(split[0]));
  return std::make_pair(vlan_id_as_hex, split[1]);
}

absl::StatusOr<std::string> GetVlanTableKey(const pdpi::IrTableEntry& entry) {
  for (const auto& match : entry.matches()) {
    if (match.name() != kMatchVlanId) continue;
    uint32_t id = 0;
    if (!absl::SimpleHexAtoi(match.exact().hex_str(), &id)) {
      return gutil::InvalidArgumentErrorBuilder()
             << "Failed to parse VLAN ID as a hex string "
             << match.exact().hex_str();
    }
    // Check we have a number in valid range.
    if (id > 4094 || id < 1) {
      return gutil::InvalidArgumentErrorBuilder()
             << "VLAN ID is not in allowed range of [1:4094]: "
             << match.exact().hex_str();
    }
    return absl::StrCat("Vlan", id);
  }
  return gutil::InvalidArgumentErrorBuilder()
         << "Could not find match field '" << kMatchVlanId
         << "' in VLAN_TABLE entry: " << entry.ShortDebugString();
}

absl::StatusOr<std::string> GetVlanMemberTableKey(
    const pdpi::IrTableEntry& entry) {
  std::string vlan;
  std::string port;

  for (const auto& match : entry.matches()) {
    if (match.name() == kMatchVlanId) {
      uint32_t id = 0;
      if (!absl::SimpleHexAtoi(match.exact().hex_str(), &id)) {
        return gutil::InvalidArgumentErrorBuilder()
               << "Failed to parse VLAN ID as a hex string "
               << match.exact().hex_str();
      }

      // Check we have a number in valid range.
      if (id > 4094 || id < 1) {
        return gutil::InvalidArgumentErrorBuilder()
               << "VLAN ID is not in allowed range of [1:4094]: "
               << match.exact().hex_str();
      }
      vlan = absl::StrCat("Vlan", id);
    } else if (match.name() == kMatchPort) {
      port = match.exact().str();
    }
  }

  if (vlan.empty() || port.empty()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Could not find match field '" << kMatchVlanId << "' and/or '"
           << kMatchPort
           << "' in VLAN_MEMBER_TABLE entry: " << entry.ShortDebugString();
  }

  return absl::StrCat(vlan, ":", port);
}

}  // namespace

absl::StatusOr<swss::KeyOpFieldsValuesTuple> CreateAppDbVlanUpdate(
    p4::v1::Update::Type update_type, const pdpi::IrTableEntry& entry) {
  swss::KeyOpFieldsValuesTuple tuple;
  ASSIGN_OR_RETURN(kfvKey(tuple), GetVlanTableKey(entry));
  switch (update_type) {
    case p4::v1::Update::INSERT: {
      kfvFieldsValues(tuple) = GetVlanValues(entry);
      kfvOp(tuple) = SET_COMMAND;
    } break;
    case p4::v1::Update::MODIFY:
      // There is actually nothing that can be modified.
      return gutil::InvalidArgumentErrorBuilder()
             << "Modifing VLAN_TABLE entries is not allowed.";
      break;
    case p4::v1::Update::DELETE:
      kfvOp(tuple) = DEL_COMMAND;
      break;
    default:
      return gutil::InvalidArgumentErrorBuilder()
             << "Unsupported update type: " << update_type;
  }
  return tuple;
}

absl::StatusOr<swss::KeyOpFieldsValuesTuple> CreateAppDbVlanMemberUpdate(
    p4::v1::Update::Type update_type, const pdpi::IrTableEntry& entry) {
  swss::KeyOpFieldsValuesTuple tuple;
  ASSIGN_OR_RETURN(kfvKey(tuple), GetVlanMemberTableKey(entry));
  switch (update_type) {
    case p4::v1::Update::INSERT:
    case p4::v1::Update::MODIFY: {
      kfvFieldsValues(tuple) = GetVlanMemberValues(entry);
      kfvOp(tuple) = SET_COMMAND;
    } break;
    case p4::v1::Update::DELETE:
      kfvOp(tuple) = DEL_COMMAND;
      break;
    default:
      return gutil::InvalidArgumentErrorBuilder()
             << "Unsupported update type: " << update_type;
  }
  return tuple;
}

absl::StatusOr<pdpi::IrUpdateStatus> PerformAppDbVlanUpdate(
    const VlanTable& vlan_table, const swss::KeyOpFieldsValuesTuple& update) {
  if (kfvOp(update) == SET_COMMAND) {
    vlan_table.producer_state->set(kfvKey(update), kfvFieldsValues(update));
  } else if (kfvOp(update) == DEL_COMMAND) {
    vlan_table.producer_state->del(kfvKey(update));
  } else {
    return gutil::InvalidArgumentErrorBuilder()
           << "[P4RT App] Invalid command for VLAN_TABLE update: "
           << kfvOp(update);
  }
  return GetAndProcessResponseNotification(
      *vlan_table.notification_consumer, *vlan_table.app_db,
      *vlan_table.app_state_db, kfvKey(update));
}

absl::StatusOr<pdpi::IrUpdateStatus> PerformAppDbVlanMemberUpdate(
    const VlanMemberTable& vlan_member_table,
    const swss::KeyOpFieldsValuesTuple& update) {
  if (kfvOp(update) == SET_COMMAND) {
    vlan_member_table.producer_state->set(kfvKey(update),
                                          kfvFieldsValues(update));
  } else if (kfvOp(update) == DEL_COMMAND) {
    vlan_member_table.producer_state->del(kfvKey(update));
  } else {
    return gutil::InvalidArgumentErrorBuilder()
           << "[P4RT App] Invalid command for VLAN_MEMBER_TABLE update: "
           << kfvOp(update);
  }
  return GetAndProcessResponseNotification(
      *vlan_member_table.notification_consumer, *vlan_member_table.app_db,
      *vlan_member_table.app_state_db, kfvKey(update));
}

absl::StatusOr<std::vector<pdpi::IrTableEntry>> GetAllAppDbVlanTableEntries(
    VlanTable& vlan_table) {
  std::vector<pdpi::IrTableEntry> vlan_entries;

  for (const std::string& key : vlan_table.app_db->keys()) {
    VLOG(1) << "Read AppDb entry: " << key;
    pdpi::IrTableEntry table_entry;

    table_entry.set_table_name(kVlanTableName);

    ASSIGN_OR_RETURN(std::string vlan_id_as_hex,
                     StripVlanPrefixAndReturnHexString(key));
    auto* match = table_entry.add_matches();
    match->set_name(kMatchVlanId);
    match->mutable_exact()->set_hex_str(vlan_id_as_hex);

    // Fixed action.
    table_entry.mutable_action()->set_name("no_action");

    bool source_p4 = false;
    for (const auto& [field, data] : vlan_table.app_db->get(key)) {
      if (field == "source" && data == "P4") {
        source_p4 = true;
      } else if (field == "controller_metadata") {
        table_entry.set_controller_metadata(data);
      }
    }

    if (!source_p4) {
      LOG(WARNING) << "Read AppDb entry with key '" << key
                   << "' was missing an indication the source was from P4.";
    }

    vlan_entries.push_back(table_entry);
  }

  return vlan_entries;
}

absl::StatusOr<std::vector<pdpi::IrTableEntry>>
GetAllAppDbVlanMemberTableEntries(VlanMemberTable& vlan_member_table) {
  std::vector<pdpi::IrTableEntry> vlan_member_entries;

  for (const std::string& key : vlan_member_table.app_db->keys()) {
    VLOG(1) << "Read AppDb entry: " << key;
    pdpi::IrTableEntry table_entry;

    table_entry.set_table_name(kVlanMemberTableName);

    ASSIGN_OR_RETURN(auto vlan_id_and_port_id,
                     ExtractVlanIdAndPortIdFromMemberKey(key));
    auto* match_vlan_id = table_entry.add_matches();
    match_vlan_id->set_name(kMatchVlanId);
    match_vlan_id->mutable_exact()->set_hex_str(vlan_id_and_port_id.first);

    auto* match_port_id = table_entry.add_matches();
    match_port_id->set_name(kMatchPort);
    match_port_id->mutable_exact()->set_str(vlan_id_and_port_id.second);

    bool tagged = false;
    bool source_p4 = false;
    for (const auto& [field, data] : vlan_member_table.app_db->get(key)) {
      if (field == "tagging_mode") {
        if (data == "tagged") {
          tagged = true;
        }
      } else if (field == "source") {
        if (data == "P4") {
          source_p4 = true;
        }
      } else if (field == "controller_metadata") {
        table_entry.set_controller_metadata(data);
      }
    }

    if (tagged) {
      table_entry.mutable_action()->set_name(kActionMakeTaggedMemberName);
    } else {
      table_entry.mutable_action()->set_name(kActionMakeUntaggedMemberName);
    }

    if (!source_p4) {
      LOG(WARNING) << "Read AppDb entry with key '" << key
                   << "' was missing an indication the source was from P4.";
    }

    vlan_member_entries.push_back(table_entry);
  }

  return vlan_member_entries;
}

}  // namespace sonic
}  // namespace p4rt_app
