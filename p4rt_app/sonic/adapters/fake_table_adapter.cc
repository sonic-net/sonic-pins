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
#include "p4rt_app/sonic/adapters/fake_table_adapter.h"

#include <string>
#include <utility>
#include <vector>

#include "absl/strings/str_cat.h"
#include "glog/logging.h"
#include "p4rt_app/sonic/adapters/fake_sonic_db_table.h"
#include "p4rt_app/sonic/adapters/table_adapter.h"

namespace p4rt_app {
namespace sonic {

FakeTableAdapter::FakeTableAdapter(FakeSonicDbTable* sonic_db_table,
                                   const std::string& table_name,
                                   const std::string& table_delimiter)
    : sonic_db_table_(sonic_db_table),
      table_name_(table_name),
      table_delimiter_(table_delimiter) {}

bool FakeTableAdapter::exists(const std::string& key) {
  VLOG(1) << "Checking if key exists: " << key;
  return sonic_db_table_->ReadTableEntry(key).ok();
}

std::vector<std::string> FakeTableAdapter::keys() {
  VLOG(2) << "Getting all keys.";
  return sonic_db_table_->GetAllKeys();
}

std::vector<std::pair<std::string, std::string>> FakeTableAdapter::get(
    const std::string& key) {
  std::vector<std::pair<std::string, std::string>> result;
  auto table_entry = sonic_db_table_->ReadTableEntry(key);
  if (table_entry.ok()) {
    // Convert the result to a vector.
    for (const auto& [key, value] : *table_entry) {
      result.push_back(std::make_pair(key, value));
    }
  } else {
    VLOG(1) << "WARNING: Could not find table entry: " << key;
  }
  return result;
}

void FakeTableAdapter::set(
    const std::string& key,
    const std::vector<std::pair<std::string, std::string>>& values) {
  sonic_db_table_->InsertTableEntry(key, values);
}

void FakeTableAdapter::del(const std::string& key) {
  sonic_db_table_->DeleteTableEntry(key);
}

void FakeTableAdapter ::batch_del(const std::vector<std::string>& keys) {
  for (const auto& key : keys) {
    FakeTableAdapter::del(key);
  }
}

std::string FakeTableAdapter::getTablePrefix() const {
  return absl::StrCat(table_name_, table_delimiter_);
}

}  // namespace sonic
}  // namespace p4rt_app
