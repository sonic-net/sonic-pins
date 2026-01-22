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
#include "p4rt_app/sonic/adapters/fake_sonic_db_table.h"

#include <queue>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_join.h"
#include "absl/synchronization/mutex.h"

namespace p4rt_app {
namespace sonic {

void FakeSonicDbTable::InsertTableEntry(const std::string &key,
                                        const SonicDbEntryList &values) {
  VLOG(1) << absl::StreamFormat("'%s' insert table entry: %s",
                                debug_table_name_, key);
  absl::WriterMutexLock lock(&entries_mutex_);
  auto &entry = entries_[key];
  entry = {};
  for (const auto &[field, data] : values) {
    entry.insert_or_assign(field, data);
  }
}

void FakeSonicDbTable::DeleteTableEntry(const std::string &key) {
  VLOG(1) << absl::StreamFormat("'%s' delete table entry: %s",
                                debug_table_name_, key);
  absl::WriterMutexLock lock(&entries_mutex_);
  if (auto iter = entries_.find(key); iter != entries_.end()) {
    entries_.erase(iter);
  }
}

void FakeSonicDbTable::SetResponseForKey(const std::string &key,
                                         const std::string &code,
                                         const std::string &message) {
  VLOG(1) << absl::StreamFormat("'%s' set response for key '%s': %s:%s",
                                debug_table_name_, key, code, message);
  responses_[key] = ResponseInfo{.code = code, .message = message};
}

bool FakeSonicDbTable::PushNotification(const std::string &key) {
  VLOG(1) << absl::StreamFormat("'%s' push notification: %s", debug_table_name_,
                                key);
  notifications_.push(key);
  if (!UpdateAppStateDb(key)) {
    VLOG(2) << absl::StreamFormat("'%s' will not update StateDB entry for '%s'",
                                  debug_table_name_, key);
    return false;
  }

  // If the key exists Insert into the StateDb, otherwise delete.
  absl::WriterMutexLock lock(&entries_mutex_);
  auto entry_iter = entries_.find(key);
  if (entry_iter != entries_.end()) {
    InsertStateDbTableEntry(key, entry_iter->second);
  } else {
    DeleteStateDbTableEntry(key);
  }
  return true;
}

bool FakeSonicDbTable::PushNotification(const std::string &key,
                                        const std::string &op,
                                        const SonicDbEntryMap &values) {
  VLOG(1) << absl::StreamFormat("'%s' push notification: %s, %s",
                                debug_table_name_, op, key);
  notifications_.push(key);
  if (!UpdateAppStateDb(key)) {
    VLOG(2) << absl::StreamFormat("'%s' will not update StateDB entry for '%s'",
                                  debug_table_name_, key);
    return false;
  }

  if (op == "SET") {
    InsertStateDbTableEntry(key, values);
  } else {
    DeleteStateDbTableEntry(key);
  }
  return true;
}

absl::Status FakeSonicDbTable::GetNextNotification(std::string &op,
                                                   std::string &data,
                                                   SonicDbEntryList &values) {
  if (notifications_.empty()) {
    return absl::DeadlineExceededError("No active notification to send");
  }

  VLOG(1) << absl::StreamFormat("'%s' get notification: %s", debug_table_name_,
                                notifications_.front());
  data = notifications_.front();
  notifications_.pop();

  // If the user has overwritten the default response with custom values we will
  // use those. Otherwise, we default to success.
  if (auto response_iter = responses_.find(data);
      response_iter != responses_.end()) {
    op = response_iter->second.code;
    values.push_back({"err_str", response_iter->second.message});
  } else {
    op = "SWSS_RC_SUCCESS";
    values.push_back({"err_str", "SWSS_RC_SUCCESS"});
  }
  return absl::OkStatus();
}

absl::StatusOr<SonicDbEntryMap> FakeSonicDbTable::ReadTableEntry(
    const std::string &key) const {
  VLOG(1) << absl::StreamFormat("'%s' read table entry: %s", debug_table_name_,
                                key);
  {
    absl::ReaderMutexLock lock(&entries_mutex_);
    if (auto entry = entries_.find(key); entry != entries_.end()) {
      return entry->second;
    }
  }
  return absl::Status(absl::StatusCode::kNotFound,
                      absl::StrCat("AppDb missing: ", key));
}

std::vector<std::string> FakeSonicDbTable::GetAllKeys() const {
  std::vector<std::string> result;
  VLOG(1) << absl::StreamFormat("'%s' get all keys.", debug_table_name_);
  {
    absl::ReaderMutexLock lock(&entries_mutex_);
    for (const auto &entry : entries_) {
      result.push_back(entry.first);
    }
  }
  VLOG(2) << absl::StreamFormat("'%s' found  keys: %s", debug_table_name_,
                                absl::StrJoin(result, ", "));
  return result;
}

void FakeSonicDbTable::DebugState() const {
  absl::ReaderMutexLock lock(&entries_mutex_);
  for (const auto &[key, values] : entries_) {
    LOG(INFO) << "AppDb entry: " << key;
    for (const auto &[field, data] : values) {
      LOG(INFO) << "  " << field << " " << data;
    }
  }
}

void FakeSonicDbTable::InsertStateDbTableEntry(const std::string &key,
                                               const SonicDbEntryMap &values) {
  // If the StateDB is not set then we do not try to update.
  if (state_db_ == nullptr) return;

  // Convert the map values to a list.
  SonicDbEntryList list;
  for (const auto &[first, second] : values) {
    list.push_back({first, second});
  }

  // OrchAgent should clear the existing entry to remove any unused fileds, and
  // reinsert.
  VLOG(2) << "Updating StateDB entry with new values.";
  state_db_->DeleteTableEntry(key);
  state_db_->InsertTableEntry(key, list);
}

void FakeSonicDbTable::DeleteStateDbTableEntry(const std::string &key) {
  // If the StateDB is not set then we do not try to update.
  if (state_db_ == nullptr) return;

  // OrchAgent should clear the existing entry to remove any unused fileds, and
  // reinsert.
  VLOG(2) << "Removing StateDB entry.";
  state_db_->DeleteTableEntry(key);
}

// Update the AppStateDb only if the user has not overriden the respose, or if
// they explicitly set that response to succeed.
bool FakeSonicDbTable::UpdateAppStateDb(const std::string &key) {
  auto response_iter = responses_.find(key);
  return response_iter == responses_.end() ||
         response_iter->second.code == "SWSS_RC_SUCCESS";
}

}  // namespace sonic
}  // namespace p4rt_app
