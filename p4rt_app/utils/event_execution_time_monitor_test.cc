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
#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"

namespace p4rt_app {
namespace {

using ::gutil::StatusIs;

TEST(EventExecutionTimeMonitorTest, CanMonitorSingleEvent) {
  EventExecutionTimeMonitor monitor("test", 1);

  EXPECT_OK(monitor.Start());
  EXPECT_OK(monitor.Stop());
  EXPECT_OK(monitor.IncrementEventCount(1));
}

TEST(EventExecutionTimeMonitorTest, CanMonitorMultipleEvents) {
  EventExecutionTimeMonitor monitor("test", 1);

  EXPECT_OK(monitor.Start());
  EXPECT_OK(monitor.Stop());
  EXPECT_OK(monitor.IncrementEventCount(1));

  EXPECT_OK(monitor.Start());
  EXPECT_OK(monitor.Stop());
  EXPECT_OK(monitor.IncrementEventCount(1));
}

TEST(EventExecutionTimeMonitorTest, CanIncrementEventsWithDuration) {
  EventExecutionTimeMonitor monitor("test", 2);

  EXPECT_OK(monitor.IncrementEventCountWithDuration(1, absl::Seconds(1)));
  EXPECT_OK(monitor.IncrementEventCountWithDuration(1, absl::Milliseconds(23)));
}

TEST(EventExecutionTimeMonitorTest, CannotStartTwoTimers) {
  EventExecutionTimeMonitor monitor("test", 1);

  EXPECT_OK(monitor.Start());
  EXPECT_THAT(monitor.Start(), StatusIs(absl::StatusCode::kFailedPrecondition));
}

TEST(EventExecutionTimeMonitorTest, CannotStopTimerWithoutStarting) {
  EventExecutionTimeMonitor monitor("test", 1);

  EXPECT_THAT(monitor.Stop(), StatusIs(absl::StatusCode::kFailedPrecondition));
}

TEST(EventExecutionTimeMonitorTest, CannotIncrementMonitorWithoutStarting) {
  EventExecutionTimeMonitor monitor("test", 1);

  EXPECT_THAT(monitor.IncrementEventCount(1),
              StatusIs(absl::StatusCode::kFailedPrecondition));
}

TEST(EventExecutionTimeMonitorTest, CannotIncrementMonitorWithoutStopping) {
  EventExecutionTimeMonitor monitor("test", 1);

  EXPECT_OK(monitor.Start());
  EXPECT_THAT(monitor.IncrementEventCount(1),
              StatusIs(absl::StatusCode::kFailedPrecondition));
}

}  // namespace
}  // namespace p4rt_app
