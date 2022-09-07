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
#include "p4rt_app/sonic/adapters/fake_notification_producer_adapter.h"

#include <utility>
#include <vector>

#include "p4rt_app/sonic/adapters/fake_sonic_db_table.h"
#include "swss/rediscommand.h"
#include "swss/table.h"

namespace p4rt_app {
namespace sonic {

FakeNotificationProducerAdapter::FakeNotificationProducerAdapter(
    FakeSonicDbTable* sonic_db_table)
    : sonic_db_table_(*sonic_db_table) {}

void FakeNotificationProducerAdapter::send(
    const std::vector<swss::KeyOpFieldsValuesTuple>& updates) {
  for (const auto& kfv : updates) {
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

}  // namespace sonic
}  // namespace p4rt_app
