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

#include <string>
#include <utility>
#include <vector>

#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "swss/warm_restart.h"

namespace p4rt_app {
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

}  // namespace p4rt_app
