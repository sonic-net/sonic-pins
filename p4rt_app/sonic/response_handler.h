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

#include "absl/container/btree_map.h"
#include "absl/status/status.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/utils/ir.h"
#include "swss/consumernotifierinterface.h"
#include "swss/dbconnectorinterface.h"

namespace p4rt_app {
namespace sonic {

// Given a mapping of keys to IR statuses this function will wait for an
// OrchAgent response for every key, and update that key's status in the
// mapping. If this function sees a response for every key it will return OK,
// but if the OrchAgent fails to respond to every key, or responds with an
// unexpected key value then this function will return a failure.
//
// NOTE: On failue the key_to_status_map should not be trusted.
absl::Status GetAndProcessResponseNotification(
    const std::string& table_name,
    swss::ConsumerNotifierInterface& notification_interface,
    swss::DBConnectorInterface& app_db_client,
    swss::DBConnectorInterface& state_db_client,
    absl::btree_map<std::string, pdpi::IrUpdateStatus*>& key_to_status_map);

// Given a single key this function will wait for a response from the OrchAgent.
// If there is no response or that response doesn't match the given key this
// function will return an absl::Status failure. Otherwise, it will return the
// OrchAgent's status.
absl::StatusOr<pdpi::IrUpdateStatus> GetAndProcessResponseNotification(
    const std::string& table_name,
    swss::ConsumerNotifierInterface& notification_interface,
    swss::DBConnectorInterface& app_db_client,
    swss::DBConnectorInterface& state_db_client, const std::string& key);

}  // namespace sonic
}  // namespace p4rt_app

#endif  // GOOGLE_P4RT_APP_SONIC_RESPONSE_HANDLER_H_
