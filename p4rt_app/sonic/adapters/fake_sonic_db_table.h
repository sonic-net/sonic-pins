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
#ifndef GOOGLE_P4RT_APP_SONIC_ADAPTERS_FAKE_SONIC_DB_TABLE_H_
#define GOOGLE_P4RT_APP_SONIC_ADAPTERS_FAKE_SONIC_DB_TABLE_H_

#include <queue>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/status/statusor.h"

namespace p4rt_app {
namespace sonic {

// When interacting with the Redis database through a SONiC interface we
// typically use the swss:FieldValueTuple (i.e. pair<string, string>). To keep
// the Fakes independent we redefine the alias.
using SonicDbKeyValue = std::pair<std::string, std::string>;

// The Redis database entries arrive to the table like a list of key value
// pairs.
using SonicDbEntryList = std::vector<SonicDbKeyValue>;

// Store the Redis database entries as a map. We use an unordered_map here to
// stay consistent with the SONiC API.
using SonicDbEntryMap = std::unordered_map<std::string, std::string>;

// Fakes how the OrchAgent updates AppDb tables. When an entry is inserted the
// Orchagent will respond with a notification of success or failure.
//
// This class is NOT thread-safe.
class FakeSonicDbTable {
 public:
  FakeSonicDbTable() : state_db_(nullptr) {}

  // The state_db can be recursivly called. It is the responsibility of the
  // end-user to ensure not loops are created when constructing
  // FakeSonicDbTables.
  FakeSonicDbTable(FakeSonicDbTable *state_db) : state_db_(state_db) {}

  void InsertTableEntry(const std::string &key, const SonicDbEntryList &values);
  void DeleteTableEntry(const std::string &key);

  void SetResponseForKey(const std::string &key, const std::string &code,
                         const std::string &message);

  void PushNotification(const std::string &key);
  void GetNextNotification(std::string &op, std::string &data,
                           SonicDbEntryList &values);

  absl::StatusOr<SonicDbEntryMap> ReadTableEntry(const std::string &key) const;

  std::vector<std::string> GetAllKeys() const;

  // Method should only be used for debug purposes.
  void DebugState() const;

 private:
  struct ResponseInfo {
    std::string code;
    std::string message;
  };

  void InsertStateDbTableEntry(const std::string &key,
                               const SonicDbEntryMap &values);
  void DeleteStateDbTableEntry(const std::string &key);

  // Current list of DB entries stored in the table.
  absl::flat_hash_map<std::string, SonicDbEntryMap> entries_;

  // List of notifications the OrchAgent would have generated. One notification
  // is created per insert, and one is removed per notification check.
  std::queue<std::string> notifications_;

  // By default all notifications will return success. To fake an error case we
  // need to set the expected response for an AppDb key.
  absl::flat_hash_map<std::string, ResponseInfo> responses_;

  // If a StateDb is set then entries will automatically be added on
  // successful inserts, and removed on successful deletes.
  FakeSonicDbTable *state_db_;
};

}  // namespace sonic
}  // namespace p4rt_app

#endif  // GOOGLE_P4RT_APP_SONIC_ADAPTERS_FAKE_SONIC_DB_TABLE_H_
