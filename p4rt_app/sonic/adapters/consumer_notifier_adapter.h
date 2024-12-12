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
#ifndef PINS_P4RT_APP_SONIC_ADAPTERS_CONSUMER_NOTIFIER_ADAPTER_H_
#define PINS_P4RT_APP_SONIC_ADAPTERS_CONSUMER_NOTIFIER_ADAPTER_H_

#include <stdint.h>

#include <memory>
#include <string>
#include <vector>

#include "swss/dbconnector.h"
#include "swss/notificationconsumer.h"
#include "swss/table.h"

namespace p4rt_app {
namespace sonic {

class ConsumerNotifierAdapter {
public:
  ConsumerNotifierAdapter(const std::string &notifier_channel_name,
                          swss::DBConnector *db_connector);
  virtual ~ConsumerNotifierAdapter() = default;

  virtual bool
  WaitForNotificationAndPop(std::string &op, std::string &data,
                            std::vector<swss::FieldValueTuple> &values,
                            int64_t timeout_ms = 60000LL);

protected:
  // Test only constructor for Mock and Fake classes.
  ConsumerNotifierAdapter() = default;

private:
  std::unique_ptr<swss::NotificationConsumer> notification_consumer_;
  std::string notifier_channel_name_;
};

} // namespace sonic
} // namespace p4rt_app

#endif // PINS_P4RT_APP_SONIC_ADAPTERS_CONSUMER_NOTIFIER_ADAPTER_H_
