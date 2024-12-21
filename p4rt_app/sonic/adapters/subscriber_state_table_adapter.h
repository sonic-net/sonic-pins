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
#ifndef PINS_P4RT_APP_SONIC_ADAPTERS_SUBSCRIBER_STATE_TABLE_ADAPTER_H_
#define PINS_P4RT_APP_SONIC_ADAPTERS_SUBSCRIBER_STATE_TABLE_ADAPTER_H_

#include <cstdint>
#include <memory>
#include <string>
#include <vector>

#include "swss/dbconnector.h"
#include "swss/rediscommand.h"
#include "swss/subscriberstatetable.h"

namespace p4rt_app {
namespace sonic {

// Acts as a proxy to invoke swss common SubscriberStateTable class methods.
// This provides the flexibility to define the constructors needed for mocks
// and fakes.
class SubscriberStateTableAdapter {
public:
  explicit SubscriberStateTableAdapter(swss::DBConnector *db,
                                       const std::string &table_name);
  virtual ~SubscriberStateTableAdapter() = default;

  virtual bool
  WaitForNotificationAndPop(std::string &key, std::string &op,
                            std::vector<swss::FieldValueTuple> &values,
                            int64_t timeout_ms);

protected:
  // Test only constructor used to construct Mock & Fake classes.
  SubscriberStateTableAdapter() = default;

private:
  std::unique_ptr<swss::SubscriberStateTable> subscriber_state_table_;
};

} // namespace sonic
} // namespace p4rt_app

#endif // PINS_P4RT_APP_SONIC_ADAPTERS_SUBSCRIBER_STATE_TABLE_ADAPTER_H_
