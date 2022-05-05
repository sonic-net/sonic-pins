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
#ifndef GOOGLE_P4RT_APP_SONIC_ADAPTERS_DB_CONNECTOR_ADAPTER_H_
#define GOOGLE_P4RT_APP_SONIC_ADAPTERS_DB_CONNECTOR_ADAPTER_H_

#include <stdint.h>

#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "swss/dbconnector.h"

namespace p4rt_app {
namespace sonic {

class DBConnectorAdapter {
 public:
  explicit DBConnectorAdapter(swss::DBConnector* db_connector);
  virtual ~DBConnectorAdapter() = default;

  virtual int64_t del(const std::string& key);

  virtual bool exists(const std::string& key);

  virtual std::unordered_map<std::string, std::string> hgetall(
      const std::string& glob);

  virtual std::vector<std::string> keys(const std::string& glob);

  virtual void hmset(
      const std::string& key,
      const std::vector<std::pair<std::string, std::string>>& values);

  virtual void batch_del(const std::vector<std::string>& keys);

 protected:
  // Test only constructor for Mock and Fake classes.
  DBConnectorAdapter() = default;

 private:
  swss::DBConnector* db_connector_;  // not owned.
};

}  // namespace sonic
}  // namespace p4rt_app

#endif  // GOOGLE_P4RT_APP_SONIC_ADAPTERS_DB_CONNECTOR_ADAPTER_H_
