// Copyright 2024 Google LLC
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
#ifndef PINS_P4RT_APP_EVENT_MONITORING_CONFIG_DB_CPU_QUEUE_TABLE_EVENT_H_
#define PINS_P4RT_APP_EVENT_MONITORING_CONFIG_DB_CPU_QUEUE_TABLE_EVENT_H_

#include <string>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "p4rt_app/event_monitoring/state_event_monitor.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"

namespace p4rt_app {

class ConfigDbCpuQueueTableEventHandler : public sonic::StateEventHandler {
 public:
  explicit ConfigDbCpuQueueTableEventHandler(P4RuntimeImpl* p4runtime)
      : p4runtime_(*p4runtime) {}

  absl::Status HandleEvent(
      const std::string& operation, const std::string& key,
      const std::vector<std::pair<std::string, std::string>>& values) final;

 private:
  P4RuntimeImpl& p4runtime_;
};

}  // namespace p4rt_app

#endif  // PINS_P4RT_APP_EVENT_MONITORING_CONFIG_DB_CPU_QUEUE_TABLE_EVENT_H_
