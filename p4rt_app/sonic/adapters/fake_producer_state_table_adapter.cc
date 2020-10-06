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
#include "p4rt_app/sonic/adapters/fake_producer_state_table_adapter.h"

#include <string>
#include <vector>

#include "glog/logging.h"
#include "p4rt_app/sonic/adapters/fake_sonic_db_table.h"
#include "swss/table.h"

namespace p4rt_app {
namespace sonic {

FakeProducerStateTableAdapter::FakeProducerStateTableAdapter(
    FakeSonicDbTable *sonic_db_table)
    : sonic_db_table_(sonic_db_table) {
  LOG_IF(FATAL, sonic_db_table == nullptr)
      << "FakeSonicDbTable cannot be nullptr.";
}

void FakeProducerStateTableAdapter::set(
    const std::string &key, const std::vector<swss::FieldValueTuple> &values) {
  VLOG(1) << "Insert table entry: " << key;
  sonic_db_table_->InsertTableEntry(key, values);
  sonic_db_table_->PushNotification(key);
}

void FakeProducerStateTableAdapter::del(const std::string &key) {
  VLOG(1) << "Delete table entry: " << key;
  sonic_db_table_->DeleteTableEntry(key);
  sonic_db_table_->PushNotification(key);
}

void FakeProducerStateTableAdapter::batch_set(
    const std::vector<swss::KeyOpFieldsValuesTuple> &key_values) {
  for (const auto &[key, op, values] : key_values) {
    FakeProducerStateTableAdapter::set(key, values);
  }
}

void FakeProducerStateTableAdapter::batch_del(
    const std::vector<std::string> &keys) {
  for (const auto &key : keys) {
    FakeProducerStateTableAdapter::del(key);
  }
}

}  // namespace sonic
}  // namespace p4rt_app
