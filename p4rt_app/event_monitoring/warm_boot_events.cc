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

#include "p4rt_app/event_monitoring/warm_boot_events.h"

#include <string>
#include <thread>  // NOLINT
#include <vector>

#include "absl/status/status.h"
#include "absl/log/log.h"
#include "absl/time/time.h"
#include "gutil/gutil/status.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "p4rt_app/sonic/adapters/consumer_notifier_adapter.h"
#include "swss/rediscommand.h"
#include "swss/warm_restart.h"

namespace p4rt_app {

WarmBootEventHandler::WarmBootEventHandler(
    P4RuntimeImpl& p4runtime,
    sonic::ConsumerNotifierAdapter& notification_channel)
    : p4runtime_(p4runtime), notification_channel_(notification_channel) {}

absl::Status WarmBootEventHandler::WaitForEventAndHandleWarmBootOperations() {
  constexpr absl::Duration timeout = absl::InfiniteDuration();

  // The key would represent the type of notification - "freeze", "unfreeze",
  // "checkpoint". P4RT doesn’t need notification for “checkpoint”, so the P4RT
  // warm-boot event handler only needs to handle “freeze” and “unfreeze”
  // notifications:
  std::string key;

  // Not used by P4RT warm-boot notifications.
  std::string op;
  std::vector<swss::FieldValueTuple> field_values;
  if (!notification_channel_.WaitForNotificationAndPop(
          key, op, field_values, absl::ToInt64Milliseconds(timeout))) {
    return gutil::UnknownErrorBuilder()
           << "Warm-boot events failed waiting for a notification.";
  }
}

void WarmBootEventHandler::Start() {
  // There should only ever be one active thread.
  if (!event_thread_.joinable()) {
    event_thread_ =
        std::thread(&WarmBootEventHandler::ContinuallyMonitorForEvents, this);
  }
}

void WarmBootEventHandler::Stop() {
  stopping_.Notify();

  // Only join the thread if it has been started.
  if (event_thread_.joinable()) {
    event_thread_.join();
    LOG(INFO) << "Stop monitoring warm-boot events.";
  }
}

void WarmBootEventHandler::ContinuallyMonitorForEvents() {
  LOG(INFO) << "Start monitoring warm-boot events.";
  while (!stopping_.HasBeenNotified()) {
    absl::Status status = WaitForEventAndHandleWarmBootOperations();
    if (!status.ok()) {
      LOG(ERROR) << "Issue processing warm-boot notification: " << status;
    }
  }
}

}  // namespace p4rt_app
