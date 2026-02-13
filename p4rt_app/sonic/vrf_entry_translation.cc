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

#include "p4rt_app/sonic/vrf_entry_translation.h"

#include <string>

#include "absl/container/btree_map.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/str_join.h"
#include "absl/strings/str_split.h"
#include "google/rpc/code.pb.h"
#include "gutil/status.h"
#include "p4_pdpi/ir.pb.h"
#include "p4rt_app/sonic/redis_connections.h"
#include "p4rt_app/sonic/response_handler.h"
#include "p4rt_app/utils/status_utility.h"
#include "swss/rediscommand.h"

namespace p4rt_app {
namespace sonic {
namespace {

// Today VRF is only used for matching.
std::vector<swss::FieldValueTuple> GetVrfValues() {
  return std::vector<swss::FieldValueTuple>{
      std::make_pair("v4", "true"),
      std::make_pair("v6", "true"),
      std::make_pair("sync_mode", "true"),
  };
}

absl::StatusOr<std::string> GetVrfTableKey(const pdpi::IrTableEntry& entry) {
  const std::string kVrfIdMatchField = "vrf_id";

  for (const auto& match : entry.matches()) {
    if (match.name() != kVrfIdMatchField) continue;

    // We are not allowed to touch SONiC's default VRF which is represented as
    // an empty string.
    if (match.exact().str().empty()) {
      return gutil::InvalidArgumentErrorBuilder()
             << "Operations on the Default VRF '" << match.exact().str()
             << "' are not allowed.";
    }
    return match.exact().str();
  }
  return gutil::InvalidArgumentErrorBuilder()
         << "Could not find match field '" << kVrfIdMatchField
         << "' in VRF_TABLE entry.";
}

absl::StatusOr<std::string> InsertVrfTableEntry(
    VrfTable& vrf_table, const pdpi::IrTableEntry& entry) {
  VLOG(2) << "Insert PDPI IR entry: " << entry.ShortDebugString();
  ASSIGN_OR_RETURN(std::string key, GetVrfTableKey(entry));

  // Check that key does not already exist in the table.
  if (vrf_table.app_db->exists(key)) {
    LOG(WARNING) << "Could not insert duplicate VRF_TABLE entry: " << key;
    return gutil::AlreadyExistsErrorBuilder()
           << "[P4RT App] Table entry with key '" << key
           << "' already exist in '" << entry.table_name() << "'.";
  }

  VLOG(1) << "Insert VRF_TABLE entry: " << key;
  vrf_table.producer_state->set(key, GetVrfValues());
  return key;
}

absl::StatusOr<std::string> DeleteVrfTableEntry(
    VrfTable& vrf_table, const pdpi::IrTableEntry& entry) {
  VLOG(2) << "Delete PDPI IR entry: " << entry.ShortDebugString();
  ASSIGN_OR_RETURN(std::string key, GetVrfTableKey(entry));

  // Check that key exists in the table.
  if (!vrf_table.app_db->exists(key)) {
    LOG(WARNING) << "Could not delete missing VRF_TABLE entry: " << key;
    return gutil::NotFoundErrorBuilder()
           << "[P4RT App] Table entry with key '" << key
           << "' does not exist in '" << entry.table_name() << "'.";
  }

  VLOG(1) << "Delete VRF_TABLE entry: " << key;
  vrf_table.producer_state->del(key);
  return key;
}

}  // namespace

absl::Status UpdateAppDbVrfTable(VrfTable& vrf_table,
                                 p4::v1::Update::Type update_type,
                                 int rpc_index, const pdpi::IrTableEntry& entry,
                                 pdpi::IrWriteResponse& response) {
  absl::StatusOr<std::string> update_key;
  switch (update_type) {
    case p4::v1::Update::INSERT:
      update_key = InsertVrfTableEntry(vrf_table, entry);
      break;
    case p4::v1::Update::MODIFY:
      update_key = gutil::InvalidArgumentErrorBuilder()
                   << "Modifing VRF_TABLE entries is not allowed.";
      break;
    case p4::v1::Update::DELETE:
      update_key = DeleteVrfTableEntry(vrf_table, entry);
      break;
    default:
      update_key = gutil::InvalidArgumentErrorBuilder()
                   << "Unsupported update type: " << update_type;
  }

  if (update_key.ok()) {
    ASSIGN_OR_RETURN(*response.mutable_statuses(rpc_index),
                     GetAndProcessResponseNotification(
                         *vrf_table.notification_consumer, *vrf_table.app_db,
                         *vrf_table.app_state_db, *update_key));
  } else {
    LOG(WARNING) << "Could not update in AppDb: " << update_key.status();
    *response.mutable_statuses(rpc_index) =
        GetIrUpdateStatus(update_key.status());
  }

  return absl::OkStatus();
}

absl::StatusOr<std::vector<pdpi::IrTableEntry>> GetAllAppDbVrfTableEntries(
    VrfTable& vrf_table) {
  std::vector<pdpi::IrTableEntry> vrf_entries;

  for (const std::string& key : vrf_table.app_db->keys()) {
    VLOG(1) << "Read AppDb entry: " << key;
    pdpi::IrTableEntry table_entry;

    // Fixed table name.
    table_entry.set_table_name("vrf_table");

    // Fixed match field name.
    auto* match = table_entry.add_matches();
    match->set_name("vrf_id");
    match->mutable_exact()->set_str(key);

    // Fixed action.
    table_entry.mutable_action()->set_name("no_action");

    vrf_entries.push_back(table_entry);
  }

  return vrf_entries;
}

}  // namespace sonic
}  // namespace p4rt_app
