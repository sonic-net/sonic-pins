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
#ifndef PINS_P4RT_APP_SONIC_ADAPTERS_MOCK_TABLE_ADAPTER_H_
#define PINS_P4RT_APP_SONIC_ADAPTERS_MOCK_TABLE_ADAPTER_H_

#include <string>
#include <utility>
#include <vector>

#include "gmock/gmock.h"
#include "p4rt_app/sonic/adapters/table_adapter.h"

namespace p4rt_app {
namespace sonic {

class MockTableAdapter : public TableAdapter {
 public:
  MOCK_METHOD(bool, exists, (const std::string& key), (override));

  MOCK_METHOD((std::vector<std::string>), keys, (), (override));

  MOCK_METHOD((std::vector<std::pair<std::string, std::string>>), get,
              (const std::string& key), (override));

  MOCK_METHOD(
      void, set,
      (const std::string& key,
       (const std::vector<std::pair<std::string, std::string>>& values)),
      (override));

  MOCK_METHOD(void, del, (const std::string& key), (override));

  MOCK_METHOD(void, batch_del, (const std::vector<std::string>& keys),
              (override));

  MOCK_METHOD(std::string, getTablePrefix, (), (const, override));
};

}  // namespace sonic
}  // namespace p4rt_app

#endif  // PINS_P4RT_APP_SONIC_ADAPTERS_MOCK_TABLE_ADAPTER_H_
