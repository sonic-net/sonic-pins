/*
 * Copyright 2025 Google LLC
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

#ifndef PINS_P4RT_APP_UTILS_WARM_RESTART_UTILITY_H_
#define PINS_P4RT_APP_UTILS_WARM_RESTART_UTILITY_H_

#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "absl/status/statusor.h"
#include "absl/time/time.h"
#include "p4rt_app/sonic/adapters/table_adapter.h"
#include "p4rt_app/sonic/adapters/warm_boot_state_adapter.h"
#include "swss/dbconnector.h"

namespace p4rt_app {
// Utility class for WarmRestart support.
// During warm restart boot up phase, WarmRestartUtil provides
// helper functions to wrap DB interactions.
class WarmRestartUtil {
 public:
  WarmRestartUtil(
      std::unique_ptr<sonic::WarmBootStateAdapter> warm_boot_state_adapter,
      std::shared_ptr<sonic::TableAdapter> port_table_config_db,
      std::shared_ptr<sonic::TableAdapter> cpu_port_table_config_db,
      std::shared_ptr<sonic::TableAdapter> port_channel_table_config_db,
      std::unique_ptr<sonic::TableAdapter> queue_config_db,
      std::unique_ptr<sonic::TableAdapter> node_cfg_config_db,
      std::unique_ptr<sonic::TableAdapter> send_to_ingress_port_config_db)
      : warm_boot_state_adapter_(std::move(warm_boot_state_adapter)),
        port_table_config_db_(std::move(port_table_config_db)),
        cpu_port_table_config_db_(std::move(cpu_port_table_config_db)),
        port_channel_table_config_db_(std::move(port_channel_table_config_db)),
        queue_config_db_(std::move(queue_config_db)),
        node_cfg_config_db_(std::move(node_cfg_config_db)),
        send_to_ingress_port_config_db_(
            std::move(send_to_ingress_port_config_db)) {}
  ~WarmRestartUtil() = default;

  // Check if P4RT is in warm start process.
  bool IsWarmStart();

  // Check OA reconciliation state in DB.
  // Poll OA reconciliation state until timeout, exit loop if OA warm restart
  // state is FAILED or RECONCILED. Return true if OA is RECONCILED.
  bool IsOrchAgentWarmBootReconciled(absl::Duration timeout = absl::Minutes(1));

  // Query all port ids from Config DB, to rebuild
  // P4RuntimeImpl.port_translation_map_ during reconciliation.
  std::vector<std::pair<std::string, std::string>> GetPortIdsFromConfigDb();

  // Query all CPU queue ids from Config DB, to rebuild
  // P4RuntimeImpl.cpu_queue_translator_ during reconciliation.
  std::vector<std::pair<std::string, std::string>> GetCpuQueueIdsFromConfigDb();

  // Query all FRONT_PANEL queue ids from Config DB, to rebuild
  // P4RuntimeImpl.front_panel_queue_translator_ during reconciliation.
  std::vector<std::pair<std::string, std::string>>
  GetFrontPanelQueueIdsFromConfigDb();

  // Query the device id from Config DB, to update device id during
  // reconciliation.
  std::optional<int> GetDeviceIdFromConfigDb();

  // Query all ports from Config DB, to rebuild packetio_impl_->port_to_socket_
  // during reconciliation.
  std::vector<std::string> GetPortsFromConfigDb();

 private:
  std::unique_ptr<sonic::WarmBootStateAdapter> warm_boot_state_adapter_;
  // CONFIG DB tables to query ports and (key, port_id) pairs.
  std::shared_ptr<sonic::TableAdapter> port_table_config_db_;
  std::shared_ptr<sonic::TableAdapter> cpu_port_table_config_db_;
  std::shared_ptr<sonic::TableAdapter> port_channel_table_config_db_;
  // CONFIG DB table to query CPU queues.
  std::unique_ptr<sonic::TableAdapter> queue_config_db_;
  // CONFIG DB table to query device id.
  std::unique_ptr<sonic::TableAdapter> node_cfg_config_db_;
  // CONFIG DB table to query SEND_TO_INGRESS_PORT.
  std::unique_ptr<sonic::TableAdapter> send_to_ingress_port_config_db_;
};

}  // namespace p4rt_app

#endif  // PINS_P4RT_APP_UTILS_WARM_RESTART_UTILITY_H_
