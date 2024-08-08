// Copyright 2020 Google LLC
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
#ifndef PINS_P4RT_APP_SONIC_ADAPTERS_MOCK_DB_CONNECTOR_ADAPTER_H_
#define PINS_P4RT_APP_SONIC_ADAPTERS_MOCK_DB_CONNECTOR_ADAPTER_H_

#include <stdint.h>

#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "gmock/gmock.h"
#include "p4rt_app/sonic/adapters/db_connector_adapter.h"

namespace p4rt_app {
namespace sonic {

class MockDBConnectorAdapter final : public DBConnectorAdapter {
 public:
  MOCK_METHOD(int64_t, del, (const std::string& key), (override));

  MOCK_METHOD(bool, exists, (const std::string& key), (override));

  MOCK_METHOD((std::unordered_map<std::string, std::string>), hgetall,
              (const std::string& glob), (override));

  MOCK_METHOD((std::vector<std::string>), keys, (const std::string& glob),
              (override));

  MOCK_METHOD(void, hmset,
              (const std::string& key,
               (const std::vector<std::pair<std::string, std::string>>)&values),
              (override));

  MOCK_METHOD(void, batch_del, (const std::vector<std::string>& keys),
              (override));
};

}  // namespace sonic
}  // namespace p4rt_app

#endif  // PINS_P4RT_APP_SONIC_ADAPTERS_MOCK_DB_CONNECTOR_ADAPTER_H_
