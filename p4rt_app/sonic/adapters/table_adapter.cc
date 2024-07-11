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
#include "p4rt_app/sonic/adapters/table_adapter.h"

#include <memory>
#include <string>
#include <vector>

#include "absl/strings/str_cat.h"
#include "swss/dbconnector.h"
#include "swss/table.h"

namespace p4rt_app {
namespace sonic {

TableAdapter::TableAdapter(swss::DBConnector* db_connector,
                           const std::string& table_name)
    : db_connector_(db_connector),
      table_(std::make_unique<swss::Table>(db_connector, table_name)) {}

bool TableAdapter::exists(const std::string& key) {
  return db_connector_->exists(absl::StrCat(getTablePrefix(), key));
}

std::vector<std::string> TableAdapter::keys() {
  std::vector<std::string> result;
  table_->getKeys(result);
  return result;
}

std::vector<std::pair<std::string, std::string>> TableAdapter::get(
    const std::string& key) {
  std::vector<std::pair<std::string, std::string>> result;
  table_->get(key, result);
  return result;
}

void TableAdapter::set(
    const std::string& key,
    const std::vector<std::pair<std::string, std::string>>& values) {
  table_->set(key, values);
}

void TableAdapter::del(const std::string& key) { table_->del(key); }

void TableAdapter::batch_del(const std::vector<std::string>& keys) {
  std::vector<std::string> redis_keys(keys.size());
  for (int i = 0; i < keys.size(); ++i) {
    redis_keys[i] = absl::StrCat(getTablePrefix(), keys[i]);
  }

  db_connector_->del(redis_keys);
}

std::string TableAdapter::getTablePrefix() const {
  return absl::StrCat(table_->getTableName(), table_->getTableNameSeparator());
}

}  // namespace sonic
}  // namespace p4rt_app
