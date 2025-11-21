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
#include "p4rt_app/event_monitoring/config_db_node_cfg_table_event.h"

#include <string>
#include <utility>
#include <vector>

#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/strings/numbers.h"
#include "swss/schema.h"

namespace p4rt_app {

ConfigDbNodeCfgTableEventHandler::ConfigDbNodeCfgTableEventHandler(
    P4RuntimeImpl* p4runtime)
    : p4runtime_(*p4runtime) {
  // do nothing.
}

absl::Status ConfigDbNodeCfgTableEventHandler::HandleEvent(
    const std::string& operation, const std::string& key,
    const std::vector<std::pair<std::string, std::string>>& values) {
  if (key != "integrated_circuit0") {
    return absl::OkStatus();
  }

  // The P4RT device ID is configured by setting the 'node-id' field.
  std::string node_id;
  for (const auto& [field, value] : values) {
    if (field == "node-id") {
      node_id = value;
    }
  }

  // Zero is the default for proto3, and is treated as if the device ID is not
  // set.
  uint64_t device_id = 0;
  if (operation == SET_COMMAND) {
    if (!absl::SimpleAtoi(node_id, &device_id)) {
      LOG(ERROR) << "Could not translate node-id '" << node_id
                 << "' into an uint64_t value.";
      device_id = 0;
    }
  }
  return p4runtime_.UpdateDeviceId(device_id);
}

}  // namespace p4rt_app
