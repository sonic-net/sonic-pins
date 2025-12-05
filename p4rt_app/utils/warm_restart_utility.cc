// Copyright 2025 Google LLC
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
#include "p4rt_app/utils/warm_restart_utility.h"

#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "absl/strings/match.h"
#include "absl/strings/numbers.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "glog/logging.h"
#include "p4rt_app/sonic/adapters/table_adapter.h"
#include "p4rt_app/sonic/adapters/warm_boot_state_adapter.h"
#include "swss/schema.h"
#include "swss/warm_restart.h"

#define SEND_TO_INGRESS_PORT_NAME            "SEND_TO_INGRESS"

namespace p4rt_app {
bool WarmRestartUtil::IsWarmStart() {
  return warm_boot_state_adapter_->IsWarmStart();
}

bool WarmRestartUtil::IsOrchAgentWarmBootReconciled(absl::Duration timeout) {
  const absl::Time deadline = absl::Now() + timeout;
  swss::WarmStart::WarmStartState oa_wb_state =
      swss::WarmStart::WarmStartState::WSUNKNOWN;
  while (absl::Now() < deadline) {
    oa_wb_state = warm_boot_state_adapter_->GetOrchAgentWarmBootState();
    if (oa_wb_state == swss::WarmStart::WarmStartState::RECONCILED) {
      return oa_wb_state == swss::WarmStart::WarmStartState::RECONCILED;
    }
    absl::SleepFor(absl::Seconds(1));
  }
  return false;
}

std::vector<std::pair<std::string, std::string>>
WarmRestartUtil::GetPortIdsFromConfigDb() {
  std::vector<std::pair<std::string, std::string>> port_ids;
  for (const auto& table : {port_table_config_db_, cpu_port_table_config_db_,
                            port_channel_table_config_db_}) {
    for (const std::string& key : table->keys()) {
      for (const auto& [field, value] : table->get(key)) {
        if (field == "id") {
          if (!value.empty()) {
            port_ids.push_back(std::make_pair(key, value));
          }
          break;
        }
      }
    }
  }
  return port_ids;
}

std::vector<std::pair<std::string, std::string>>
WarmRestartUtil::GetCpuQueueIdsFromConfigDb() {
  return queue_config_db_->get("CPU");
}

std::vector<std::pair<std::string, std::string>>
WarmRestartUtil::GetFrontPanelQueueIdsFromConfigDb() {
  return queue_config_db_->get("FRONT_PANEL");
}

std::optional<int> WarmRestartUtil::GetDeviceIdFromConfigDb() {
  for (const auto& [field, value] :
       node_cfg_config_db_->get("integrated_circuit0")) {
    if (field == "node-id") {
      int device_id;
      if (absl::SimpleAtoi(value, &device_id)) {
        return device_id;
      }
    }
  }

  LOG(WARNING) << "Failed to read 'node-id' from ConfigDB. ";
  return std::nullopt;
}

std::vector<std::string> WarmRestartUtil::GetPortsFromConfigDb() {
  std::vector<std::string> ports;

  for (const std::string& key : port_table_config_db_->keys()) {
    if (absl::StartsWith(key, "Ethernet")) ports.push_back(key);
  }

  for (const std::string& key : send_to_ingress_port_config_db_->keys()) {
    if (absl::StartsWith(key, SEND_TO_INGRESS_PORT_NAME)) ports.push_back(key);
  }

  return ports;
}

}  // namespace p4rt_app
