// Copyright 2021 Google LLC
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
#include "p4rt_app/event_monitoring/app_state_db_port_table_event.h"

#include <string>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "swss/schema.h"

namespace p4rt_app {

absl::Status AppStateDbPortTableEventHandler::HandleEvent(
    const std::string& operation, const std::string& key,
    const std::vector<std::pair<std::string, std::string>>& values) {
  // P4RT can ignore managment ports, and only focus on front-panel port that
  // start with `Ethernet`.
  if (!absl::StartsWith(key, "Ethernet")) {
    return absl::OkStatus();
  }

  if (operation == SET_COMMAND) {
    return p4runtime_.AddPacketIoPort(key);
  } else if (operation == DEL_COMMAND) {
    return p4runtime_.RemovePacketIoPort(key);
  }

  return absl::InvalidArgumentError(
      absl::StrCat("Unhandled SWSS operand '", operation, "'"));
}

}  // namespace p4rt_app
