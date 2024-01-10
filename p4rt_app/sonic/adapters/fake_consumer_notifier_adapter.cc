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
#include "p4rt_app/sonic/adapters/fake_consumer_notifier_adapter.h"

#include <stdint.h>

#include <string>

#include "absl/log/log.h"
#include "p4rt_app/sonic/adapters/fake_sonic_db_table.h"

namespace p4rt_app {
namespace sonic {

FakeConsumerNotifierAdapter::FakeConsumerNotifierAdapter(
    FakeSonicDbTable *sonic_db_table)
    : sonic_db_table_(sonic_db_table) {
  LOG_IF(FATAL, sonic_db_table == nullptr)
      << "FakeSonicDbTable cannot be nullptr.";
}

bool FakeConsumerNotifierAdapter::WaitForNotificationAndPop(
    std::string &op, std::string &data, SonicDbEntryList &values,
    int64_t timeout_ms) {
  return sonic_db_table_->GetNextNotification(op, data, values).ok();
}

void FakeConsumerNotifierAdapter::DrainNotifications() {
  std::string op, data;
  SonicDbEntryList values;
  while (sonic_db_table_->GetNextNotification(op, data, values).ok()) {
  }
}

}  // namespace sonic
}  // namespace p4rt_app
