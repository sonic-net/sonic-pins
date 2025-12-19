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
#include "p4rt_app/event_monitoring/config_db_queue_table_event.h"

#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "gutil/status.h"
#include "p4rt_app/p4runtime/queue_translator.h"
#include "swss/schema.h"

namespace p4rt_app {

absl::Status ConfigDbQueueTableEventHandler::HandleEvent(
    const std::string& operation, const std::string& key,
    const std::vector<std::pair<std::string, std::string>>& values) {
  if (key == "CPU" || key == "FRONT_PANEL") {
    QueueType queue_type =
        key == "CPU" ? QueueType::kCpu : QueueType::kFrontPanel;
    if (operation == DEL_COMMAND) {
      p4runtime_.AssignQueueTranslator(queue_type, QueueTranslator::Empty());
    } else {
      ASSIGN_OR_RETURN(
          auto translator, QueueTranslator::Create(values),
          _ << "Unable to create queue translator for table " << key);
      p4runtime_.AssignQueueTranslator(queue_type, std::move(translator));
    }
  }
  // Ignore Queue mappings for other keys.
  return absl::OkStatus();
}

}  // namespace p4rt_app

