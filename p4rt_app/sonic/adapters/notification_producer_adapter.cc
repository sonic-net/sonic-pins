// Copyright 2022 Google LLC
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

#include "swss/dbconnector.h"
#include "swss/notificationproducer.h"

namespace p4rt_app {
namespace sonic {

NotificationProducerAdapter::NotificationProducerAdapter(
    swss::DBConnector* db, const std::string& channel)
    : notification_producer_(
          std::make_unique<swss::NotificationProducer>(db, channel)) {}

void NotificationProducerAdapter::experimental_send(
     const std::vector<swss::KeyOpFieldsValuesTuple>& values)
{   
     std::vector<swss::FieldValueTuple> new_values;
     for (const auto &value: values) {
         if (kfvOp(value) == SET_COMMAND) {
          new_values.push_back(swss::FieldValueTuple{kfvKey(value), swss::JSon::buildJson(kfvFieldsValues(value))});
         } else {
             new_values.push_back(swss::FieldValueTuple{kfvKey(value), ""});
         }
     }
     notification_producer_->send("", "", new_values);
}

}  // namespace sonic
}  // namespace p4rt_app
