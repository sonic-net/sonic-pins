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
#ifndef PINS_P4RT_APP_SONIC_ADAPTERS_FAKE_TABLE_ADAPTER_H_
#define PINS_P4RT_APP_SONIC_ADAPTERS_FAKE_TABLE_ADAPTER_H_

#include <string>
#include <utility>
#include <vector>

#include "p4rt_app/sonic/adapters/fake_sonic_db_table.h"
#include "p4rt_app/sonic/adapters/table_adapter.h"
#include "swss/rediscommand.h"

namespace p4rt_app {
namespace sonic {

// Fake the behavior of SONiC's Table class.
//
// The Table is able to read/write/modify entries in a given SONiC table without
// notifiying the OrchAgent.
class FakeTableAdapter final : public TableAdapter {
 public:
  explicit FakeTableAdapter(FakeSonicDbTable* sonic_db_table,
                            const std::string& table_name,
                            const std::string& table_delimiter = ":");

  bool exists(const std::string& key) override;
  std::vector<std::string> keys() override;

  std::vector<std::pair<std::string, std::string>> get(
      const std::string& key) override;
  void set(
      const std::string& key,
      const std::vector<std::pair<std::string, std::string>>& values) override;

  void batch_set(
      const std::vector<swss::KeyOpFieldsValuesTuple>& values) override;

  void del(const std::string& key) override;
  void batch_del(const std::vector<std::string>& keys) override;

  std::string getTablePrefix() const override;

 private:
  FakeSonicDbTable* sonic_db_table_;  // Not owned.

  std::string table_name_;
  std::string table_delimiter_;
};

}  // namespace sonic
}  // namespace p4rt_app

#endif  // PINS_P4RT_APP_SONIC_ADAPTERS_FAKE_TABLE_ADAPTER_H_
