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
#include "p4rt_app/sonic/adapters/db_connector_adapter.h"

#include <stdint.h>

#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "absl/log/log.h"
#include "swss/dbconnector.h"

namespace p4rt_app {
namespace sonic {

DBConnectorAdapter::DBConnectorAdapter(swss::DBConnector* db_connector)
    : db_connector_(db_connector) {}

int64_t DBConnectorAdapter::del(const std::string& key) {
  LOG_IF(FATAL, db_connector_ == nullptr) << "db_connector_ cannot be nullptr.";
  return db_connector_->del(key);
}

bool DBConnectorAdapter::exists(const std::string& key) {
  LOG_IF(FATAL, db_connector_ == nullptr) << "db_connector_ cannot be nullptr.";
  return db_connector_->exists(key);
}

std::unordered_map<std::string, std::string> DBConnectorAdapter::hgetall(
    const std::string& glob) {
  LOG_IF(FATAL, db_connector_ == nullptr) << "db_connector_ cannot be nullptr.";
  return db_connector_->hgetall(glob);
}

std::vector<std::string> DBConnectorAdapter::keys(const std::string& glob) {
  LOG_IF(FATAL, db_connector_ == nullptr) << "db_connector_ cannot be nullptr.";
  return db_connector_->keys(glob);
}

void DBConnectorAdapter::hmset(
    const std::string& key,
    const std::vector<std::pair<std::string, std::string>>& values) {
  LOG_IF(FATAL, db_connector_ == nullptr) << "db_connector_ cannot be nullptr.";
  db_connector_->hmset(key, values.begin(), values.end());
}

void DBConnectorAdapter::batch_del(const std::vector<std::string>& keys) {
  LOG_IF(FATAL, db_connector_ == nullptr) << "db_connector_ cannot be nullptr.";
  db_connector_->del(keys);
}

}  // namespace sonic
}  // namespace p4rt_app
