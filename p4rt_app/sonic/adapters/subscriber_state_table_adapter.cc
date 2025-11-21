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
#include "p4rt_app/sonic/adapters/subscriber_state_table_adapter.h"

#include <cstdint>
#include <memory>
#include <string>
#include <vector>

#include "absl/log/log.h"
#include "swss/dbconnector.h"
#include "swss/rediscommand.h"
#include "swss/select.h"
#include "swss/selectable.h"
#include "swss/subscriberstatetable.h"
#include "swss/table.h"

namespace p4rt_app {
namespace sonic {

SubscriberStateTableAdapter::SubscriberStateTableAdapter(
    swss::DBConnector *db, const std::string &table_name)
    : subscriber_state_table_(
          std::make_unique<swss::SubscriberStateTable>(db, table_name)) {}

bool SubscriberStateTableAdapter::WaitForNotificationAndPop(
    std::string &key, std::string &op,
    std::vector<swss::FieldValueTuple> &values, int64_t timeout_ms) {
  LOG_IF(FATAL, subscriber_state_table_ == nullptr)  // Crash OK
      << "subscriber_state_table cannot be nullptr.";

  swss::Select s;
  s.addSelectable(subscriber_state_table_.get());
  swss::Selectable *sel;

  int error = s.select(&sel, timeout_ms);
  if (error != swss::Select::OBJECT) {
    return false;
  }

  swss::KeyOpFieldsValuesTuple kopfvs;
  subscriber_state_table_->pop(kopfvs);
  key = kfvKey(kopfvs);
  op = kfvOp(kopfvs);
  values = kfvFieldsValues(kopfvs);
  return true;
}

}  // namespace sonic
}  // namespace p4rt_app
