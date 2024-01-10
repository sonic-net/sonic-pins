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
#include "p4rt_app/sonic/adapters/fake_zmq_producer_state_table_adapter.h"

#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "p4rt_app/sonic/adapters/fake_sonic_db_table.h"
#include "swss/rediscommand.h"
#include "swss/schema.h"
#include "swss/table.h"

namespace p4rt_app {
namespace sonic {

FakeZmqProducerStateTableAdapter::FakeZmqProducerStateTableAdapter(
    FakeSonicDbTable* sonic_db_table)
    : sonic_db_table_(*sonic_db_table) {}

void FakeZmqProducerStateTableAdapter::send(
    const std::vector<swss::KeyOpFieldsValuesTuple>& kcos) {
  for (const auto& kfv : kcos) {
    SonicDbEntryMap entry_map;
    SonicDbEntryList entry_list;
    for (const auto& [field, value] : kfvFieldsValues(kfv)) {
      entry_map[field] = value;
      entry_list.push_back(std::make_pair(field, value));
    }

    // Only if the request succeeds should we update AppDb state.
    if (sonic_db_table_.PushNotification(kfvKey(kfv), kfvOp(kfv), entry_map)) {
      // Notifications to the OA can only "SET" or "DEL" an entry. So "SET" is
      // used for both inserting and modifying an entry. Therefore, we always
      // delete the current entry and only then re-insert it on "SET".
      sonic_db_table_.DeleteTableEntry(kfvKey(kfv));
      if (kfvOp(kfv) == "SET") {
        sonic_db_table_.InsertTableEntry(kfvKey(kfv), entry_list);
      }
    }
  }
}

bool FakeZmqProducerStateTableAdapter::wait(
    std::string& db, std::string& table_name,
    std::vector<std::shared_ptr<swss::KeyOpFieldsValuesTuple>>& kcos) {
  // db & table_name is fixed now since only p4rt tables use zmq.
  db = "APPL_DB";
  table_name = APP_P4RT_TABLE_NAME;
  std::string op, key;
  SonicDbEntryList values;
  while (sonic_db_table_.GetNextNotification(op, key, values).code() !=
         absl::StatusCode::kDeadlineExceeded) {
    // Zmq response consists of key, op(empty) and field value tuples of
    // <status, error_message>. Replace the field in values tuple(originally has
    // `err_str`) with the actual response code string.
    values[0].first = op;
    kcos.push_back(std::make_shared<swss::KeyOpFieldsValuesTuple>(
        key, "", std::vector<std::pair<std::string, std::string>>(values)));
    values.clear();
  }
  if (kcos.empty()) {
    return false;
  }

  return true;
}

}  // namespace sonic
}  // namespace p4rt_app
