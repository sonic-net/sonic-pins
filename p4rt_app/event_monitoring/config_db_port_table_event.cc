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

#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/strings/match.h"
#include "gutil/status.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "swss/schema.h"

namespace p4rt_app {

absl::Status ConfigDbPortTableEventHandler::HandleEvent(
    const std::string& operation, const std::string& key,
    const std::vector<std::pair<std::string, std::string>>& values) {
  std::string port_id;
  for (const auto& [field, value] : values) {
    if (field == "id") {
      port_id = value;
      break;
    }
  }

  if (port_id.empty()) {
    LOG(WARNING) << "Port '" << key
                 << "' does not have an ID field. Removing translation.";
    RETURN_IF_ERROR(p4runtime_.RemovePortTranslation(key));
  } else if (operation == DEL_COMMAND) {
    RETURN_IF_ERROR(p4runtime_.RemovePortTranslation(key));
  } else if (operation == SET_COMMAND) {
    RETURN_IF_ERROR(p4runtime_.AddPortTranslation(key, port_id));
  } else {
    return gutil::InvalidArgumentErrorBuilder()
           << "unexpected event: " << operation << " on " << key;
  }

  return absl::OkStatus();
}

}  // namespace p4rt_app
