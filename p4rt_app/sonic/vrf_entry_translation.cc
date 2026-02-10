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
#include <utility>
#include <vector>

#include "absl/log/log.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/str_join.h"
#include "absl/strings/str_split.h"
#include "google/rpc/code.pb.h"
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

}  // namespace

absl::StatusOr<swss::KeyOpFieldsValuesTuple> CreateAppDbVrfUpdate(
    p4::v1::Update::Type update_type, const pdpi::IrTableEntry& entry) {
  swss::KeyOpFieldsValuesTuple tuple;
  ASSIGN_OR_RETURN(kfvKey(tuple), GetVrfTableKey(entry));
  switch (update_type) {
    case p4::v1::Update::INSERT: {
      kfvFieldsValues(tuple) = GetVrfValues();
      kfvOp(tuple) = SET_COMMAND;
    } break;
    case p4::v1::Update::MODIFY:
      return gutil::InvalidArgumentErrorBuilder()
             << "Modifing VRF_TABLE entries is not allowed.";
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

absl::StatusOr<pdpi::IrUpdateStatus> PerformAppDbVrfUpdate(
    const VrfTable& vrf_table, const swss::KeyOpFieldsValuesTuple& update) {
  if (kfvOp(update) == SET_COMMAND) {
    vrf_table.producer_state->set(kfvKey(update), kfvFieldsValues(update));
  } else if (kfvOp(update) == DEL_COMMAND) {
    vrf_table.producer_state->del(kfvKey(update));
  } else {
    return gutil::InvalidArgumentErrorBuilder()
           << "[P4RT App] Invalid command for VRF_TABLE update: "
           << kfvOp(update);
  }
  return GetAndProcessResponseNotification(
      *vrf_table.notification_consumer, *vrf_table.app_db,
      *vrf_table.app_state_db, kfvKey(update));
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
