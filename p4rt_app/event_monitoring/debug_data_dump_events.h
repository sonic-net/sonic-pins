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
#ifndef PINS_INFRA_P4RT_APP_EVENT_MONITORING_DEBUG_DATA_DUMP_EVENT_H_
#define PINS_INFRA_P4RT_APP_EVENT_MONITORING_DEBUG_DATA_DUMP_EVENT_H_

#include <thread> // NOLINT

#include "absl/base/thread_annotations.h"
#include "absl/status/status.h"
#include "absl/synchronization/mutex.h"
#include "absl/synchronization/notification.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "p4rt_app/sonic/adapters/consumer_notifier_adapter.h"
#include "p4rt_app/sonic/adapters/notification_producer_adapter.h"

namespace p4rt_app {

class DebugDataDumpEventHandler {
public:
  explicit DebugDataDumpEventHandler(
      P4RuntimeImpl &p4runtime,
      sonic::ConsumerNotifierAdapter &notification_channel,
      sonic::NotificationProducerAdapter &response_channel);

  // Waits on a notification from RedisDB to dump debug data for the P4RT App.
  // If the notification is for another component then we do nothing and exit
  // cleanly.
  absl::Status WaitForEventAndDumpDebugData() ABSL_LOCKS_EXCLUDED(event_lock_);

  // Spawns a thread that will continually listen for notifications and respond.
  // Once started the thread will continue until stopped.
  void Start();
  void Stop();

private:
  // SWSS DB connections are not thread safe so we should only handle one event
  // at a time.
  absl::Mutex event_lock_;

  // P4Runtime service from which we will collect debug data.
  P4RuntimeImpl &p4runtime_;

  // SWSS notification channel that should be listening to events on the
  // DEBUG_DATA_REQ_CHANNEL.
  sonic::ConsumerNotifierAdapter &
      notification_channel_ ABSL_GUARDED_BY(event_lock_);

  // Send response to DEBUG_DATA_RESP_CHANNEL.
  sonic::NotificationProducerAdapter &
      response_channel_ ABSL_GUARDED_BY(event_lock_);

  // Event thread that can be started to continually monitor for events. Once
  // the destructor is called we can notify the thread to stop monitoring
  // events.
  absl::Notification stopping_;
  std::thread event_thread_;

  void ContinuallyMonitorForEvents();
};

} // namespace p4rt_app

#endif // PINS_INFRA_P4RT_APP_EVENT_MONITORING_DEBUG_DATA_DUMP_EVENT_H_
