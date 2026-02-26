// Copyright 2025 Google LLC
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
#ifndef PINS_P4RT_APP_SONIC_ADAPTERS_MOCK_ZMQ_PRODUCER_STATE_TABLE_ADAPTER_H_
#define PINS_P4RT_APP_SONIC_ADAPTERS_MOCK_ZMQ_PRODUCER_STATE_TABLE_ADAPTER_H_

#include <memory>
#include <string>
#include <vector>

#include "gmock/gmock.h"
#include "p4rt_app/sonic/adapters/zmq_producer_state_table_adapter.h"
#include "swss/table.h"

namespace p4rt_app {
namespace sonic {

class MockZmqProducerStateTableAdapter final
    : public ZmqProducerStateTableAdapter {
 public:
  MOCK_METHOD(void, send,
              (const std::vector<swss::KeyOpFieldsValuesTuple>& kcos),
              (override));

  MOCK_METHOD(
      bool, wait,
      (std::string & db, std::string& table_name,
       std::vector<std::shared_ptr<swss::KeyOpFieldsValuesTuple>>& kcos),
      (override));
};

}  // namespace sonic
}  // namespace p4rt_app

#endif  // PINS_P4RT_APP_SONIC_ADAPTERS_MOCK_ZMQ_PRODUCER_STATE_TABLE_ADAPTER_H_
