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
#ifndef PINS_P4RT_APP_SONIC_ADAPTERS_TABLE_ADAPTER_H_
#define PINS_P4RT_APP_SONIC_ADAPTERS_TABLE_ADAPTER_H_

#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "swss/dbconnector.h"
#include "swss/table.h"

namespace p4rt_app {
namespace sonic {

// The TableAdapter class abstracts away any SONiC specific naming for redisDB
// entries, and allows the code to simply focus on the key values. For example,
// if we wanted to read a PORT_TABLE entry from AppDb and StateDb in redis they
// would look like:
//   AppDb:    PORT_TABLE:Ethernet0
//   StateDb:  PORT_TABLE|Ethernet0
//
// Notice how the delineator for AppDb is ':', but StateDb uses '|' for the same
// entry. The TableAdapter automatically handles this formatting for us. So if
// we wanted to read data about Ethernet0 we only need to call:
//   auto data = table_adapter.get("Ethernet0");
class TableAdapter {
public:
  explicit TableAdapter(swss::DBConnector *db_connector,
                        const std::string &table_name);
  virtual ~TableAdapter() = default;

  virtual bool exists(const std::string &key);
  virtual std::vector<std::string> keys();

  virtual std::vector<std::pair<std::string, std::string>>
  get(const std::string &key);
  virtual void
  set(const std::string &key,
      const std::vector<std::pair<std::string, std::string>> &values);
  virtual void
  batch_set(const std::vector<swss::KeyOpFieldsValuesTuple> &values);

  virtual void del(const std::string &key);
  virtual void batch_del(const std::vector<std::string> &keys);

  virtual std::string getTablePrefix() const;

protected:
  // Test only constructor used to construct Mock & Fake classes.
  TableAdapter() = default;

private:
  swss::DBConnector *db_connector_; // Not owned
  std::unique_ptr<swss::Table> table_;
};

} // namespace sonic
} // namespace p4rt_app

#endif // PINS_P4RT_APP_SONIC_ADAPTERS_TABLE_ADAPTER_H_
