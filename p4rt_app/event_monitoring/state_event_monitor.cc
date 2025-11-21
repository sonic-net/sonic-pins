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
#include "p4rt_app/event_monitoring/state_event_monitor.h"

#include <deque>
#include <memory>
#include <utility>

#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "gutil/status.h"
#include "swss/rediscommand.h"
#include "swss/select.h"
#include "swss/selectable.h"
#include "swss/subscriberstatetable.h"

namespace p4rt_app {
namespace sonic {
namespace {

absl::StatusOr<swss::Selectable*> WaitForSubscribeEvent(
    swss::Select& select, absl::string_view db_name) {
  // Wait indefinitely for an event.
  swss::Selectable* selectable = nullptr;
  int error_code = select.select(&selectable);

  // Translate swss::Select error code to absl::Status.
  switch (error_code) {
    case swss::Select::OBJECT:
      return selectable;
    case swss::Select::ERROR:
      return gutil::UnknownErrorBuilder()
             << absl::StreamFormat("Waiting for event from '%s'.", db_name);
    case swss::Select::TIMEOUT:
      return gutil::DeadlineExceededErrorBuilder()
             << absl::StreamFormat("Waiting for event from '%s'.", db_name);
  }

  return gutil::InternalErrorBuilder() << absl::StreamFormat(
             "Unexpected error code '%d' encountered while waiting for an "
             "event from '%s'.",
             error_code, db_name);
}

}  // namespace

StateEventMonitor::StateEventMonitor(swss::DBConnector& db) : redis_db_(db) {
  // do nothing.
}

absl::Status StateEventMonitor::RegisterTableHandler(
    absl::string_view table_name, std::unique_ptr<StateEventHandler> handler) {
  auto [iter, success] = monitored_tables_by_name_.emplace(
      table_name,
      TableHandler{
          .subscriber_table = std::make_unique<swss::SubscriberStateTable>(
              &redis_db_, std::string(table_name)),
          .event_handler = std::move(handler),
      });

  if (!success) {
    return gutil::AlreadyExistsErrorBuilder()
           << "Could not add event monitor for " << table_name << " in "
           << redis_db_.getDbName();
  }
  LOG(INFO) << "Adding event monitor for " << table_name << " in "
            << redis_db_.getDbName();
  selector_.addSelectable(iter->second.subscriber_table.get());
  return absl::OkStatus();
}

absl::Status StateEventMonitor::WaitForNextEventAndHandle() {
  swss::Selectable* selectable = nullptr;
  ASSIGN_OR_RETURN(selectable,
                   WaitForSubscribeEvent(selector_, redis_db_.getDbName()));

  for (auto& [table_name, handler] : monitored_tables_by_name_) {
    // Only pop events for the selectable that raised the event.
    if (selectable != handler.subscriber_table.get()) {
      continue;
    }

    std::deque<swss::KeyOpFieldsValuesTuple> events;
    handler.subscriber_table->pops(events);
    for (const auto& event : events) {
      absl::Status status = handler.event_handler->HandleEvent(
          kfvOp(event), kfvKey(event), kfvFieldsValues(event));
      if (!status.ok()) {
        LOG(ERROR) << "Could not handle " << table_name << " change in "
                   << redis_db_.getDbName() << ": " << status;
      }
    }

    return absl::OkStatus();
  }

  return gutil::InternalErrorBuilder()
         << "Detected an event for " << redis_db_.getDbName()
         << ", but it was not handled?";
}

}  // namespace sonic
}  // namespace p4rt_app
