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
#ifndef GOOGLE_P4RT_APP_UTILS_EVENT_EXECUTION_TIME_MONITOR_H_
#define GOOGLE_P4RT_APP_UTILS_EVENT_EXECUTION_TIME_MONITOR_H_

#include <cstdint>
#include <optional>

#include "absl/status/status.h"
#include "absl/time/time.h"

namespace p4rt_app {

// The EventExecutionTimerMonitor can be use to get an average exection time for
// certain events. This class is intended to be used in one of the following
// maners:
//
// usecase 1:
//     EventExecutionTimeMonitor monitor;
//     monitor.Start();
//       ...
//     monitor.Stop();
//     monitor.IncrementEventCount(number_of_events);
//
// usecase 2:
//     EventExecutionTimeMonitor monitor;
//       ...
//     monitor.IncrementEventCountWithDuration(number_of_events, duration);
class EventExecutionTimeMonitor {
 public:
  explicit EventExecutionTimeMonitor(const std::string& event_name,
                                     int64_t log_threshold);

  absl::Status Start();
  absl::Status Stop();

  absl::Status IncrementEventCount(int64_t number_of_events);

  absl::Status IncrementEventCountWithDuration(int64_t number_of_events,
                                               absl::Duration duration);

 private:
  void AppendDuration(absl::Duration duration);
  void Reset();

  const std::string event_name_;
  const int64_t log_threshold_;

  int64_t number_of_increments_;
  int64_t number_of_events_;

  std::optional<absl::Time> start_time_;
  std::optional<absl::Duration> duration_;
};

}  // namespace p4rt_app

#endif  // GOOGLE_P4RT_APP_UTILS_EVENT_EXECUTION_TIME_MONITOR_H_
