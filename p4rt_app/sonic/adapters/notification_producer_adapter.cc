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
#include "p4rt_app/sonic/adapters/notification_producer_adapter.h"

#include <memory>
#include <string>
#include <vector>

#include "swss/dbconnector.h"
#include "swss/notificationproducer.h"
#include "swss/json.h" 
#include "swss/rediscommand.h"
#include "swss/table.h"

namespace p4rt_app {
namespace sonic {

NotificationProducerAdapter::NotificationProducerAdapter(
    swss::DBConnector* db, const std::string& channel)
    : notification_producer_(
          std::make_unique<swss::NotificationProducer>(db, channel)) {}

void NotificationProducerAdapter::send_with_op_key(
    const std::string& op, const std::string& key,
    std::vector<swss::FieldValueTuple>& fv) {
  notification_producer_->send(op, key, fv);
}

}  // namespace sonic
}  // namespace p4rt_app
