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
#ifndef PINS_P4RT_APP_SONIC_ADAPTERS_FAKE_DB_CONNECTOR_ADAPTER_H_
#define PINS_P4RT_APP_SONIC_ADAPTERS_FAKE_DB_CONNECTOR_ADAPTER_H_

#include <stdint.h>

#include <string>
#include <unordered_map>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "p4rt_app/sonic/adapters/db_connector_adapter.h"
#include "p4rt_app/sonic/adapters/fake_sonic_db_table.h"
#include "swss/table.h"

namespace p4rt_app {
namespace sonic {

// Fake the behavior of SONiC's DBConnector class.
//
// The DBConnector is able to read and modify any table (e.g. P4RT or VRF_TABLE)
// in a redis DB (e.g. AppDb, ConfigDb, AsicDb, etc.).
class FakeDBConnectorAdapter final : public DBConnectorAdapter {
 public:
  FakeDBConnectorAdapter() = default;

  // Not copyable or moveable.
  FakeDBConnectorAdapter(const FakeDBConnectorAdapter&) = delete;
  FakeDBConnectorAdapter& operator=(const FakeDBConnectorAdapter&) = delete;

  // Allows access to a fake SONiC Redis DB table.
  void AddSonicDbTable(const std::string& table_name, FakeSonicDbTable* table);

  // Faked methods.
  std::vector<std::string> keys(const std::string& glob) override;
  std::unordered_map<std::string, std::string> hgetall(
      const std::string& key) override;
  bool exists(const std::string& key) override;
  int64_t del(const std::string& key) override;
  void hmset(const std::string& key,
             const std::vector<swss::FieldValueTuple>& values) override;
  void batch_del(const std::vector<std::string>& keys) override;

 private:
  // The DBConnector interface has access to all tables (e.g. P4RT, or
  // VRF_TABLE) in a redis DB (e.g. AppDb). To fake this behavior we maintain a
  // map of any faked tables the client should have access to.
  //
  // key: name of the SONiC DB table (i.e. P4RT)
  // val: faked table holding all installed entries.
  absl::flat_hash_map<std::string, FakeSonicDbTable*>
      sonic_db_tables_;  // No ownership.
};

}  // namespace sonic
}  // namespace p4rt_app

#endif  // PINS_P4RT_APP_SONIC_ADAPTERS_FAKE_DB_CONNECTOR_ADAPTER_H_
