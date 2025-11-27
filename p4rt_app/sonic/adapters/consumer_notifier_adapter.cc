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
#include "p4rt_app/sonic/adapters/consumer_notifier_adapter.h"

#include <stdint.h>

#include <memory>
#include <string>
#include <vector>

#include "absl/log/log.h"
#include "swss/dbconnector.h"
#include "swss/notificationconsumer.h"
#include "swss/select.h"
#include "swss/selectable.h"
#include "swss/table.h"

namespace p4rt_app {
namespace sonic {

ConsumerNotifierAdapter::ConsumerNotifierAdapter(
    const std::string &notifier_channel_name, swss::DBConnector *db_connector) {
  notifier_channel_name_ = std::string{notifier_channel_name};
  notification_consumer_ = std::make_unique<swss::NotificationConsumer>(
      db_connector, notifier_channel_name_);
}

bool ConsumerNotifierAdapter::WaitForNotificationAndPop(
    std::string &op, std::string &data,
    std::vector<swss::FieldValueTuple> &values, int64_t timeout_ms) {
  LOG_IF(FATAL, notification_consumer_ == nullptr)
      << "notification_consumer_ cannot be nullptr.";
  int message_available = notification_consumer_->peek();
  if (message_available == -1) {
    return false;
  }

  // Wait for notification only when the queue is empty.
  if (message_available == 0) {
    swss::Select s;
    s.addSelectable(notification_consumer_.get());
    swss::Selectable *sel;

    int error = s.select(&sel, timeout_ms);
    if (error != swss::Select::OBJECT) {
      return false;
    }
  }
  notification_consumer_->pop(op, data, values);
  return true;
}

void ConsumerNotifierAdapter::DrainNotifications() {
  std::string op, data;
  std::vector<swss::FieldValueTuple> values;
  while (notification_consumer_->peek() > 0) {
    notification_consumer_->pop(op, data, values);
  }
}

}  // namespace sonic
}  // namespace p4rt_app
