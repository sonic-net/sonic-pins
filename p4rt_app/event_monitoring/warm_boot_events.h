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
#ifndef PINS_P4RT_APP_EVENT_MONITORING_WARM_BOOT_EVENTS_H_
#define PINS_P4RT_APP_EVENT_MONITORING_WARM_BOOT_EVENTS_H_

#include <thread>  // NOLINT

#include "absl/base/thread_annotations.h"
#include "absl/status/status.h"
#include "absl/synchronization/mutex.h"
#include "absl/synchronization/notification.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "p4rt_app/sonic/adapters/consumer_notifier_adapter.h"

namespace p4rt_app {

class WarmBootEventHandler {
 public:
  explicit WarmBootEventHandler(
      P4RuntimeImpl& p4runtime,
      sonic::ConsumerNotifierAdapter& notification_channel);

  // Waits on warm-boot notifications.
  absl::Status WaitForEventAndHandleWarmBootOperations();

  // Spawns a thread that will continually listen for notifications and respond.
  // Once started the thread will continue until stopped.
  void Start();
  void Stop();

 private:
  // P4Runtime service in which the freeze/unfreeze handlers are implemented.
  P4RuntimeImpl& p4runtime_;

  // Notification channel that should be listening to events on the
  // warm-boot notification channel.
  sonic::ConsumerNotifierAdapter& notification_channel_;

  // Event thread that can be started to continually monitor for events. Once
  // the destructor is called we can notify the thread to stop monitoring
  // events.
  absl::Notification stopping_;
  std::thread event_thread_;

  void ContinuallyMonitorForEvents();
};

}  // namespace p4rt_app

#endif  // PINS_P4RT_APP_EVENT_MONITORING_WARM_BOOT_EVENTS_H_
