/*
 * Copyright 2020 Google LLC
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
#ifndef GOOGLE_P4RT_APP_SONIC_RESPONSE_HANDLER_H_
#define GOOGLE_P4RT_APP_SONIC_RESPONSE_HANDLER_H_

#include <string>

#include "absl/container/btree_map.h"
#include "absl/status/status.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/utils/ir.h"
#include "p4rt_app/sonic/adapters/consumer_notifier_adapter.h"
#include "p4rt_app/sonic/adapters/table_adapter.h"
#include "p4rt_app/utils/event_execution_time_monitor.h"

namespace p4rt_app {
namespace sonic {

enum class ResponseTimeMonitor {
  kNone,
  kP4rtTableWrite,
};

// Given a mapping of keys to IR statuses this function will wait for an
// OrchAgent response for every key, and update that key's status in the
// mapping. If this function sees a response for every key it will return OK,
// but if the OrchAgent fails to respond to every key, or responds with an
// unexpected key value then this function will return a failure.
//
// NOTE: On failue the key_to_status_map should not be trusted.
absl::Status GetAndProcessResponseNotification(
    ConsumerNotifierAdapter& notification_interface, TableAdapter& app_db_table,
    TableAdapter& state_db_table,
    absl::btree_map<std::string, pdpi::IrUpdateStatus*>& key_to_status_map,
    ResponseTimeMonitor event_monitor);

// Given a single key this function will wait for a response from the OrchAgent.
// If there is no response or that response doesn't match the given key this
// function will return an absl::Status failure. Otherwise, it will return the
// OrchAgent's status.
absl::StatusOr<pdpi::IrUpdateStatus> GetAndProcessResponseNotification(
    ConsumerNotifierAdapter& notification_interface, TableAdapter& app_db_table,
    TableAdapter& state_db_table, const std::string& key,
    ResponseTimeMonitor event_monitor);

}  // namespace sonic
}  // namespace p4rt_app

#endif  // GOOGLE_P4RT_APP_SONIC_RESPONSE_HANDLER_H_
