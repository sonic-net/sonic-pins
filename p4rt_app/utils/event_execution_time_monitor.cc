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
#include "p4rt_app/utils/event_execution_time_monitor.h"

#include "absl/status/status.h"
#include "absl/strings/str_format.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "glog/logging.h"

namespace p4rt_app {

EventExecutionTimeMonitor::EventExecutionTimeMonitor(
    const std::string& event_name, int64_t log_threshold)
    : event_name_(event_name), log_threshold_(log_threshold) {
  Reset();
}

absl::Status EventExecutionTimeMonitor::Start() {
  if (start_time_.has_value()) {
    return absl::FailedPreconditionError(
        absl::StrFormat("A timer is already running for %s.", event_name_));
  }

  start_time_ = absl::Now();
  return absl::OkStatus();
}

absl::Status EventExecutionTimeMonitor::Stop() {
  absl::Time stop_time = absl::Now();

  if (!start_time_.has_value()) {
    return absl::FailedPreconditionError(
        absl::StrFormat("A timer was never started for %s.", event_name_));
  }
  AppendDuration(stop_time - *start_time_);
  start_time_.reset();
  return absl::OkStatus();
}

absl::Status EventExecutionTimeMonitor::IncrementEventCount(
    int64_t number_of_events) {
  if (!duration_.has_value()) {
    return absl::FailedPreconditionError(absl::StrFormat(
        "Cannot increment event count for %s when nothing has been timed.",
        event_name_));
  }
  number_of_increments_++;
  number_of_events_ += number_of_events;

  if (number_of_events_ >= log_threshold_) {
    LOG(INFO) << absl::StreamFormat("%lld (calls %lld) %s op took: %d ms",
                                    number_of_events_, number_of_increments_,
                                    event_name_,
                                    absl::ToInt64Milliseconds(*duration_));
    Reset();
  }

  return absl::OkStatus();
}

absl::Status EventExecutionTimeMonitor::IncrementEventCountWithDuration(
    int64_t number_of_events, absl::Duration duration) {
  AppendDuration(duration);
  return IncrementEventCount(number_of_events);
}

void EventExecutionTimeMonitor::AppendDuration(absl::Duration duration) {
  if (duration_.has_value()) {
    *duration_ += duration;
  } else {
    duration_ = duration;
  }
}

void EventExecutionTimeMonitor::Reset() {
  number_of_increments_ = 0;
  number_of_events_ = 0;
  start_time_.reset();
  duration_.reset();
}

}  // namespace p4rt_app
