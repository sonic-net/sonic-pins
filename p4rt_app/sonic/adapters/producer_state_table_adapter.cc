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
#include "p4rt_app/sonic/adapters/producer_state_table_adapter.h"

#include <memory>
#include <string>
#include <vector>

#include "absl/log/log.h"
#include "swss/dbconnector.h"
#include "swss/producerstatetable.h"
#include "swss/table.h"

namespace p4rt_app {
namespace sonic {

ProducerStateTableAdapter::ProducerStateTableAdapter(
    swss::DBConnector* db, const std::string& table_name)
    : producer_state_table_(
          std::make_unique<swss::ProducerStateTable>(db, table_name)) {}

void ProducerStateTableAdapter::set(
    const std::string& key, const std::vector<swss::FieldValueTuple>& values) {
  LOG_IF(FATAL, producer_state_table_ == nullptr)
      << "producer_state_table_ cannot be nullptr.";
  producer_state_table_->set(key, values);
}

void ProducerStateTableAdapter::del(const std::string& key) {
  LOG_IF(FATAL, producer_state_table_ == nullptr)
      << "producer_state_table_ cannot be nullptr.";
  producer_state_table_->del(key);
}

void ProducerStateTableAdapter::batch_set(
    const std::vector<swss::KeyOpFieldsValuesTuple>& values) {
  LOG_IF(FATAL, producer_state_table_ == nullptr)
      << "producer_state_table_ cannot be nullptr.";
  producer_state_table_->set(values);
}

void ProducerStateTableAdapter::batch_del(
    const std::vector<std::string>& keys) {
  LOG_IF(FATAL, producer_state_table_ == nullptr)
      << "producer_state_table_ cannot be nullptr.";
  producer_state_table_->del(keys);
}

}  // namespace sonic
}  // namespace p4rt_app
