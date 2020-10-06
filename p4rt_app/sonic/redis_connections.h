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
#ifndef GOOGLE_P4RT_APP_SONIC_REDIS_CONNECTIONS_H_
#define GOOGLE_P4RT_APP_SONIC_REDIS_CONNECTIONS_H_

#include <algorithm>
#include <memory>
#include <utility>

#include "p4rt_app/sonic/adapters/consumer_notifier_adapter.h"
#include "p4rt_app/sonic/adapters/producer_state_table_adapter.h"
#include "p4rt_app/sonic/adapters/table_adapter.h"

namespace p4rt_app {
namespace sonic {

// The P4RT app needs to:
//   * Write P4RT_TABLE entries into the AppDb.
//   * Read P4RT_TABLE entries out out of the AppStateDb and CountersDb.
//   * Support failed updates through the response path.
//   * Support state verification between the AppDb and AppStateDb.
struct P4rtTable {
  std::unique_ptr<ProducerStateTableAdapter> producer_state;
  std::unique_ptr<ConsumerNotifierAdapter> notifier;
  std::unique_ptr<TableAdapter> app_db;
  std::unique_ptr<TableAdapter> app_state_db;
  std::unique_ptr<TableAdapter> counter_db;
};

}  // namespace sonic
}  // namespace p4rt_app

#endif  // GOOGLE_P4RT_APP_SONIC_REDIS_CONNECTIONS_H_
