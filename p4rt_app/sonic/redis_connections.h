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
#ifndef PINS_P4RT_APP_SONIC_REDIS_CONNECTIONS_H_
#define PINS_P4RT_APP_SONIC_REDIS_CONNECTIONS_H_

#include <algorithm>
#include <memory>
#include <utility>

#include "p4rt_app/sonic/adapters/consumer_notifier_adapter.h"
#include "p4rt_app/sonic/adapters/producer_state_table_adapter.h"
#include "p4rt_app/sonic/adapters/table_adapter.h"
#include "p4rt_app/sonic/adapters/zmq_producer_state_table_adapter.h"

namespace p4rt_app {
namespace sonic {

// The P4RT app needs to:
//   * Write P4RT_TABLE entries into a zmq message channel.
//   * Read P4RT_TABLE entries out of the AppDb and CountersDb.
struct P4rtTable {
  std::unique_ptr<ZmqProducerStateTableAdapter> producer;
  std::unique_ptr<TableAdapter> app_db;
  std::unique_ptr<TableAdapter> counter_db;
};

// The P4RT app needs to:
//   * Write VRF_TABLE entries into the AppDb.
//   * Read VRF_TABLE entries out of the AppStateDb.
//   * Support failed updates through the response path.
//   * Support state verification between the AppDb and AppStateDb.
struct VrfTable {
  std::unique_ptr<ProducerStateTableAdapter> producer_state;
  std::unique_ptr<ConsumerNotifierAdapter> notification_consumer;
  std::unique_ptr<TableAdapter> app_db;
  std::unique_ptr<TableAdapter> app_state_db;
};

// The P4RT app needs to:
//   * Write VLAN_TABLE_P4 entries into the AppDb.
//   * Read VLAN_TABLE_P4 entries out of the AppStateDb.
//   * Support failed updates through the response path.
//   * Support state verification between the AppDb and AppStateDb.
struct VlanTable {
  std::unique_ptr<ProducerStateTableAdapter> producer_state;
  std::unique_ptr<ConsumerNotifierAdapter> notification_consumer;
  std::unique_ptr<TableAdapter> app_db;
  std::unique_ptr<TableAdapter> app_state_db;
};

// The P4RT app needs to:
//   * Write VLAN_MEMBER_TABLE_P4 entries into the AppDb.
//   * Read VLAN_MEMBER_TABLE_P4 entries out of the AppStateDb.
//   * Support failed updates through the response path.
//   * Support state verification between the AppDb and AppStateDb.
struct VlanMemberTable {
  std::unique_ptr<ProducerStateTableAdapter> producer_state;
  std::unique_ptr<ConsumerNotifierAdapter> notification_consumer;
  std::unique_ptr<TableAdapter> app_db;
  std::unique_ptr<TableAdapter> app_state_db;
};

// The P4RT app needs to:
//   * Write HASH_TABLE entries into the AppDb.
//   * Support failed updates through the response path.
//   * Support state verification between the AppDb and AppStateDb.
struct HashTable {
  std::unique_ptr<ProducerStateTableAdapter> producer_state;
  std::unique_ptr<ConsumerNotifierAdapter> notification_consumer;
  std::unique_ptr<TableAdapter> app_db;
  std::unique_ptr<TableAdapter> app_state_db;
};

// The P4RT app needs to:
//   * Write SWITCH_TABLE entries into the AppDb.
//   * Support failed updates through the response path.
//   * Support state verification between the AppDb and AppStateDb.
struct SwitchTable {
  std::unique_ptr<ProducerStateTableAdapter> producer_state;
  std::unique_ptr<ConsumerNotifierAdapter> notification_consumer;
  std::unique_ptr<TableAdapter> app_db;
  std::unique_ptr<TableAdapter> app_state_db;
};

// The P4RT app needs to:
//   * Write P4RT_PORT_ID_TABLE entries to the AppDb and AppStateDb.
struct PortTable {
  std::unique_ptr<TableAdapter> app_db;
  std::unique_ptr<TableAdapter> app_state_db;
};

// The P4RT app needs to:
//   * Write HOST_STATS entries into the StateDB.
struct HostStatsTable {
  std::unique_ptr<TableAdapter> state_db;
};

// The P4RT app needs to:
//   * Read SWITCH_CAPABILITY entries from the StateDB.
struct SwitchCapabilityTable {
  std::unique_ptr<TableAdapter> state_db;
};

} // namespace sonic
} // namespace p4rt_app

#endif // PINS_P4RT_APP_SONIC_REDIS_CONNECTIONS_H_
