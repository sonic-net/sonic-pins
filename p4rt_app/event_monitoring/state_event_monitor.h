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
#ifndef PINS_P4RT_APP_EVENT_MONITORING_STATE_EVENT_MONITOR_H_
#define PINS_P4RT_APP_EVENT_MONITORING_STATE_EVENT_MONITOR_H_

#include <deque>
#include <memory>

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/time/time.h"
#include "swss/dbconnector.h"
#include "swss/rediscommand.h"
#include "swss/select.h"
#include "swss/subscriberstatetable.h"

namespace p4rt_app {
namespace sonic {

// StateEventHandler is an interface that can be registered with a
// StateEventMonitor. The interface should be assoicated with a table name in
// the redis DB monitored by the StateEventMonitor. For example if we wanted to
// handle events relating to PORT_TABLE changes in the APPL_STATE_DB we would
// write something like:
//
//    swss::DBConnector db("APPL_STATE_DB", /*timeout=*/0);
//    StateEventMonitor monitor(db);
//
//    PortTableEventHandler handler;  // derives from StateEventHandler.
//    monitor.RegisterTableHandler("PORT_TABLE", handler);
//
// Whenver the PORT_TABLE in APPL_STATE_DB is updated the StateEventMonitor will
// call the HandleEvent.
class StateEventHandler {
 public:
  virtual absl::Status HandleEvent(
      const std::string& operation, const std::string& key,
      const std::vector<std::pair<std::string, std::string>>& values) = 0;

 protected:
  StateEventHandler() = default;
  virtual ~StateEventHandler() = default;
};

// StateEventMonitor can monitor changes to specific tables in a Redis DB. A
// single monitor can watch multiple table (e.g. PORT_TABLE, INTF_TABLE) in a
// Redis DB, but not multiple Redis DBs (e.g. CONFIG_DB, STATE_DB). A unique
// monitor is needed per DB.
//
// Waiting for events is a blocking call, but all tables are monitored in
// parallel. So if any table entry changes the monitor will react.
class StateEventMonitor {
 public:
  StateEventMonitor(swss::DBConnector& db);
  virtual ~StateEventMonitor() = default;

  // Not copyable or movable.
  StateEventMonitor(const StateEventMonitor&) = delete;
  StateEventMonitor& operator=(const StateEventMonitor&) = delete;

  // Add a new table that should be monitored for changes in the DB. Only one
  // handler can exist per table, and this method will return an AlreadyExists
  // error if a duplicate is passed.
  absl::Status RegisterTableHandler(const std::string& table_name,
                                    StateEventHandler& handler);

  // Blocks indefinitely until an event, or set of events occur on any of the
  // monitored table.
  absl::Status WaitForNextEventAndHandle();

 private:
  // When an event is detected we will check the `subscriber_table` for any new
  // events, and then call it's `event_handler`.
  struct TableHandler {
    std::unique_ptr<swss::SubscriberStateTable> subscriber_table;
    StateEventHandler& event_handler;
  };

  // The Redis DB we are monitoring (e.g. CONFIG_DB, STATE_DB, etc.).
  swss::DBConnector& redis_db_;

  // The swss::Select container can monitor multiple swss::Selectable objects
  // like the swss::SubscriberStateTable. When any of it's monitored events
  // changes the container will wake up.
  swss::Select selector_;

  // Monitor multiple tables within the redis_db_.
  absl::flat_hash_map<std::string, TableHandler> monitored_tables_by_name_;
};

}  // namespace sonic
}  // namespace p4rt_app

#endif  // PINS_P4RT_APP_EVENT_MONITORING_STATE_EVENT_MONITOR_H_
