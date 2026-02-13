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
#include "p4rt_app/event_monitoring/debug_data_dump_events.h"

#include <string>
#include <thread>  // NOLINT
#include <vector>

#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/synchronization/mutex.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "gutil/io.h"
#include "gutil/status.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "p4rt_app/sonic/adapters/consumer_notifier_adapter.h"
#include "p4rt_app/sonic/adapters/notification_producer_adapter.h"
#include "swss/rediscommand.h"

namespace p4rt_app {

constexpr char kP4rtComponentName[] = "p4rt";

DebugDataDumpEventHandler::DebugDataDumpEventHandler(
    P4RuntimeImpl& p4runtime,
    sonic::ConsumerNotifierAdapter& notification_channel,
    sonic::NotificationProducerAdapter& response_channel)
    : p4runtime_(p4runtime),
      notification_channel_(notification_channel),
      response_channel_(response_channel) {}

absl::Status DebugDataDumpEventHandler::WaitForEventAndDumpDebugData() {
  absl::MutexLock l(&event_lock_);

  // The component that is requested to dump debug data.
  std::string component;

  // The artifact directory path to dump debug data to. Each request will come
  // with a unique artifact directory.
  std::string path;

  // We expect one field value pair to specify the log level to be dumped. The
  // field should be "level:" and the value can be "alert", "critical" or "all".
  std::vector<swss::FieldValueTuple> field_values;
  if (!notification_channel_.WaitForNotificationAndPop(
          component, path, field_values,
          absl::ToInt64Milliseconds(absl::InfiniteDuration()))) {
    return gutil::UnknownErrorBuilder()
           << "Debug data dump events failed/timed-out waiting for a "
           << "notification.";
  }

  // We only need to dump debug data when asked about the P4RT App component.
  if (component != kP4rtComponentName) {
    return absl::OkStatus();
  }

  // The default log level is "alert".
  std::string log_level = "alert";
  if (!field_values.empty()) log_level = field_values[0].second;

  absl::Status status = p4runtime_.DumpDebugData(path, log_level);

  field_values.clear();
  if (!status.ok()) {
    field_values.push_back(swss::FieldValueTuple{"status", "fail"});
    field_values.push_back(swss::FieldValueTuple{"err_str", status.message()});
  } else {
    field_values.push_back(swss::FieldValueTuple{"status", "success"});
    field_values.push_back(swss::FieldValueTuple{"err_str", ""});
  }

  response_channel_.send_with_op_key(component, path, field_values);

  return status;
}

void DebugDataDumpEventHandler::Start() {
  // There should only ever be one active thread.
  if (!event_thread_.joinable()) {
    event_thread_ = std::thread(
        &DebugDataDumpEventHandler::ContinuallyMonitorForEvents, this);
  }
}

void DebugDataDumpEventHandler::Stop() {
  stopping_.Notify();

  // Only join the thread if it has been started.
  if (event_thread_.joinable()) {
    event_thread_.join();
    LOG(INFO) << "Stop monitoring debug data dump events.";
  }
}

void DebugDataDumpEventHandler::ContinuallyMonitorForEvents() {
  LOG(INFO) << "Start monitoring debug data dump events.";
  while (!stopping_.HasBeenNotified()) {
    absl::Status status = WaitForEventAndDumpDebugData();
    if (!status.ok()) {
      LOG(ERROR) << "Issue dumping P4RT App's debug data: " << status;
    }
  }
}

}  // namespace p4rt_app
