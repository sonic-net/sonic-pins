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
#ifndef PINS_P4RT_APP_EVENT_MONITORING_STATE_VERIFICATION_EVENT_H_
#define PINS_P4RT_APP_EVENT_MONITORING_STATE_VERIFICATION_EVENT_H_

#include <thread> // NOLINT

#include "absl/base/thread_annotations.h"
#include "absl/status/status.h"
#include "absl/synchronization/mutex.h"
#include "absl/synchronization/notification.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "p4rt_app/sonic/adapters/consumer_notifier_adapter.h"
#include "p4rt_app/sonic/adapters/table_adapter.h"

namespace p4rt_app {

class StateVerificationEvents {
public:
  explicit StateVerificationEvents(
      P4RuntimeImpl &p4runtime,
      sonic::ConsumerNotifierAdapter &notification_channel,
      sonic::TableAdapter &response_channel);

  // Waits on a notification from RedisDB to verify state for the P4RT App. If
  // the notification is for another component then we do nothing and exit
  // cleanly.
  absl::Status WaitForEventAndVerifyP4Runtime()
      ABSL_LOCKS_EXCLUDED(event_lock_);

  // Spawns a thread that will continually listen for notifications and respond.
  // Once started the thread will continue unil stopped.
  void Start();
  void Stop();

private:
  // SWSS DB connections are not thread safe so we should only handle one event
  // at a time.
  absl::Mutex event_lock_;

  // P4Runtime service where we will verify state.
  P4RuntimeImpl &p4runtime_;

  // SWSS notification channel that should be listening to events on the
  // VERIFY_STATE_REQ_CHANNEL in the StateDb.
  sonic::ConsumerNotifierAdapter &
      notification_channel_ ABSL_GUARDED_BY(event_lock_);

  // When updating StateDb we should be manually writing into
  // VERIFY_STATE_RESP_TABLE.
  sonic::TableAdapter &response_channel_ ABSL_GUARDED_BY(event_lock_);

  // Event thread that can be started to continually monitor for events. Once
  // the destructor is called we can notify the thread to stop monitoring
  // events.
  absl::Notification stopping_;
  std::thread event_thread_;

  void ContinuallyMonitorForEvents();
};

} // namespace p4rt_app

#endif // PINS_P4RT_APP_EVENT_MONITORING_STATE_VERIFICATION_EVENT_H_
