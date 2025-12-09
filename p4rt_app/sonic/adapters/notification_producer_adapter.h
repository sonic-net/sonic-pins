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
#ifndef PINS_P4RT_APP_SONIC_ADAPTERS_NOTIFICATION_PRODUCER_ADAPTER_H_
#define PINS_P4RT_APP_SONIC_ADAPTERS_NOTIFICATION_PRODUCER_ADAPTER_H_

#include <memory>
#include <string>
#include <vector>

#include "swss/dbconnector.h"
#include "swss/notificationproducer.h"
#include "swss/rediscommand.h"

namespace p4rt_app {
namespace sonic {

class NotificationProducerAdapter {
public:
  explicit NotificationProducerAdapter(swss::DBConnector *db,
                                       const std::string &channel);
  virtual ~NotificationProducerAdapter() = default;

  virtual void send_with_op_key(const std::string& op, const std::string& key,
                                std::vector<swss::FieldValueTuple>& fv);

 protected:
  // Test only constructor used to construct Mock & Fake classes.
  NotificationProducerAdapter() = default;

private:
  std::unique_ptr<swss::NotificationProducer> notification_producer_;
};

} // namespace sonic
} // namespace p4rt_app

#endif // PINS_P4RT_APP_SONIC_ADAPTERS_NOTIFICATION_PRODUCER_ADAPTER_H_
