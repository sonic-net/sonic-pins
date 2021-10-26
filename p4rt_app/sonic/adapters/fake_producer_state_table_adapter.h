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
#ifndef GOOGLE_P4RT_APP_SONIC_ADAPTERS_FAKE_PRODUCER_STATE_TABLE_ADAPTER_H_
#define GOOGLE_P4RT_APP_SONIC_ADAPTERS_FAKE_PRODUCER_STATE_TABLE_ADAPTER_H_

#include <string>
#include <vector>

#include "p4rt_app/sonic/adapters/fake_sonic_db_table.h"
#include "p4rt_app/sonic/adapters/producer_state_table_adapter.h"
#include "swss/table.h"

namespace p4rt_app {
namespace sonic {

// Fake the OrchAgent write path behavior for table entries in a SONiC DB.
class FakeProducerStateTableAdapter final : public ProducerStateTableAdapter {
 public:
  FakeProducerStateTableAdapter(const std::string &table_name,
                                FakeSonicDbTable *sonic_db_table);

  // Not copyable or moveable.
  FakeProducerStateTableAdapter(const FakeProducerStateTableAdapter &) = delete;
  FakeProducerStateTableAdapter &operator=(
      const FakeProducerStateTableAdapter &) = delete;

  // Faked methods.
  void set(const std::string &key,
           const std::vector<swss::FieldValueTuple> &values) override;
  void del(const std::string &key) override;

  std::string get_table_name() const override { return table_name_; }

 private:
  const std::string table_name_;

  // The SONiC table maintains a list of all installed table entries created by
  // this fake.
  FakeSonicDbTable *sonic_db_table_;  // No ownership.
};

}  // namespace sonic
}  // namespace p4rt_app

#endif  // GOOGLE_P4RT_APP_SONIC_ADAPTERS_FAKE_PRODUCER_STATE_TABLE_ADAPTER_H_
