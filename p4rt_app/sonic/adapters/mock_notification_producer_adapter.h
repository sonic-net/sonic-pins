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
#ifndef PINS_P4RT_APP_SONIC_ADAPTERS_MOCK_NOTIFICATION_PRODUCER_ADAPTER_H_
#define PINS_P4RT_APP_SONIC_ADAPTERS_MOCK_NOTIFICATION_PRODUCER_ADAPTER_H_

#include <string>
#include <vector>

#include "p4rt_app/sonic/adapters/notification_producer_adapter.h"
#include "swss/rediscommand.h"
#include "gmock/gmock.h"

namespace p4rt_app {
namespace sonic {

class MockNotificationProducerAdapter : public NotificationProducerAdapter {
 public:
  MOCK_METHOD(void, send_with_op_key,
              (const std::string &op, const std::string &key,
               std::vector<swss::FieldValueTuple> &fv),
              (override));
};

} // namespace sonic
} // namespace p4rt_app

#endif // PINS_P4RT_APP_SONIC_ADAPTERS_MOCK_NOTIFICATION_PRODUCER_ADAPTER_H_
