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
#include "p4rt_app/event_monitoring/config_db_port_table_event.h"

#include <string>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/match.h"
#include "glog/logging.h"
#include "gutil/status.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "p4rt_app/sonic/adapters/table_adapter.h"
#include "p4rt_app/sonic/redis_connections.h"
#include "swss/schema.h"

namespace p4rt_app {
namespace {

const char kPortIdField[] = "id";

absl::Status RemovePortIdFromP4rtAndRedis(P4RuntimeImpl& p4runtime,
                                          sonic::PortTable& port_table,
                                          const std::string& port_name) {
  RETURN_IF_ERROR(p4runtime.RemovePortTranslation(port_name));
  port_table.app_db->del(port_name);
  port_table.app_state_db->del(port_name);
  return absl::OkStatus();
}

absl::Status InsertPortIdFromP4rtAndRedis(P4RuntimeImpl& p4runtime,
                                          sonic::PortTable& port_table,
                                          const std::string& port_name,
                                          const std::string& port_id) {
  // Port ID 0 is reserved for ports that are modeled, but should not be used by
  // P4RT. If we see ID = 0 we should still update redis so gNMI can converge.
  if (port_id == "0") {
    // Handle the edge case where an existing port has an ID, but then gets
    // updated to be 0.
    RETURN_IF_ERROR(
        RemovePortIdFromP4rtAndRedis(p4runtime, port_table, port_name));
  } else {
    RETURN_IF_ERROR(p4runtime.AddPortTranslation(port_name, port_id));
  }
  port_table.app_db->set(port_name, {{kPortIdField, port_id}});
  port_table.app_state_db->set(port_name, {{kPortIdField, port_id}});
  return absl::OkStatus();
}

}  // namespace

absl::Status ConfigDbPortTableEventHandler::HandleEvent(
    const std::string& operation, const std::string& key,
    const std::vector<std::pair<std::string, std::string>>& values) {
  // P4RT can ignore managment ports, and only focus on front-panel port that
  // start with `Ethernet` or `PortChannel`.
  if (!absl::StartsWith(key, "Ethernet") &&
      !absl::StartsWith(key, "PortChannel")) {
    return absl::OkStatus();
  }

  std::string port_id;
  for (const auto& [field, value] : values) {
    if (field == kPortIdField) {
      port_id = value;
    }
  }

  if (port_id.empty()) {
    LOG(WARNING) << "Port '" << key << "' does not have an ID field.";
    RETURN_IF_ERROR(
        RemovePortIdFromP4rtAndRedis(p4runtime_, *port_table_, key));
  } else if (operation == DEL_COMMAND) {
    RETURN_IF_ERROR(
        RemovePortIdFromP4rtAndRedis(p4runtime_, *port_table_, key));
  } else if (operation == SET_COMMAND) {
    RETURN_IF_ERROR(
        InsertPortIdFromP4rtAndRedis(p4runtime_, *port_table_, key, port_id));
  } else {
    return gutil::InvalidArgumentErrorBuilder()
           << "unexpected event: " << operation << " on " << key;
  }

  return absl::OkStatus();
}

}  // namespace p4rt_app
