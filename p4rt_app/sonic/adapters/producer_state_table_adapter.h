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
#ifndef GOOGLE_P4RT_APP_SONIC_ADAPTERS_PRODUCER_STATE_TABLE_ADAPTER_H_
#define GOOGLE_P4RT_APP_SONIC_ADAPTERS_PRODUCER_STATE_TABLE_ADAPTER_H_

#include <memory>
#include <string>
#include <vector>

#include "swss/dbconnector.h"
#include "swss/producerstatetable.h"
#include "swss/table.h"

namespace p4rt_app {
namespace sonic {

class ProducerStateTableAdapter {
 public:
  explicit ProducerStateTableAdapter(swss::DBConnector* db,
                                     const std::string& table_name);
  virtual ~ProducerStateTableAdapter() = default;

  virtual void set(const std::string& key,
                   const std::vector<swss::FieldValueTuple>& values);

  virtual void del(const std::string& key);

  virtual void batch_set(
      const std::vector<swss::KeyOpFieldsValuesTuple>& values);

  virtual void batch_del(const std::vector<std::string>& keys);

 protected:
  // Test only constructor used to construct Mock & Fake classes.
  ProducerStateTableAdapter() = default;

 private:
  std::unique_ptr<swss::ProducerStateTable> producer_state_table_;
};

}  // namespace sonic
}  // namespace p4rt_app

#endif  // GOOGLE_P4RT_APP_SONIC_ADAPTERS_PRODUCER_STATE_TABLE_ADAPTER_H_
