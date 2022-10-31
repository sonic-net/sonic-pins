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
#ifndef GOOGLE_P4RT_APP_SONIC_ADAPTERS_MOCK_CONSUMER_NOTIFIER_ADAPTER_H_
#define GOOGLE_P4RT_APP_SONIC_ADAPTERS_MOCK_CONSUMER_NOTIFIER_ADAPTER_H_

#include <stdint.h>

#include <string>
#include <vector>

#include "gmock/gmock.h"
#include "p4rt_app/sonic/adapters/consumer_notifier_adapter.h"
#include "swss/table.h"

namespace p4rt_app {
namespace sonic {

class MockConsumerNotifierAdapter final : public ConsumerNotifierAdapter {
 public:
  MOCK_METHOD(bool, WaitForNotificationAndPop,
              (std::string & op, std::string &data,
               std::vector<swss::FieldValueTuple> &values, int64_t timeout_ms),
              (override));
};

}  // namespace sonic
}  // namespace p4rt_app

#endif  // GOOGLE_P4RT_APP_SONIC_ADAPTERS_MOCK_CONSUMER_NOTIFIER_ADAPTER_H_
