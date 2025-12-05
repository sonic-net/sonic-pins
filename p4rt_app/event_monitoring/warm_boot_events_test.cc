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

#include <cstdint>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/synchronization/notification.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status_matchers.h"
#include "p4rt_app/p4runtime/mock_p4runtime_impl.h"
#include "p4rt_app/sonic/adapters/mock_consumer_notifier_adapter.h"
#include "swss/rediscommand.h"
#include "swss/warm_restart.h"

namespace p4rt_app {
namespace {

using ::gutil::StatusIs;
using ::testing::DoAll;
using ::testing::Eq;
using ::testing::HasSubstr;
using ::testing::Return;
using ::testing::SetArgReferee;

class WarmBootEventHandlerTest : public testing::Test {
 protected:
  WarmBootEventHandlerTest()
      : warm_boot_events_(
            WarmBootEventHandler(mock_p4runtime_, mock_consumer_notifier_)) {}

  WarmBootEventHandler warm_boot_events_;

  MockP4RuntimeImpl mock_p4runtime_;
  sonic::MockConsumerNotifierAdapter mock_consumer_notifier_;
};

TEST_F(WarmBootEventHandlerTest, EventThreadStartStop) {
  // This test will spawn a thread inside the WarmBootEventHandlerTest
  // object which is stopped when the object is destroyed. To ensure we run
  // through the loop at least once we block on a notification.
  absl::Notification was_run;

  // We expect the wait call to be made at least once, but could be called again
  // while waiting for the thread to be stopped.
  EXPECT_CALL(mock_consumer_notifier_, WaitForNotificationAndPop)
      .WillOnce([&was_run](std::string& key, std::string& op,
                           std::vector<swss::FieldValueTuple>& fv,
                           int64_t timeout) {
        was_run.Notify();
        return false;
      })
      .WillRepeatedly(Return(false));

  // Spawn the thread, and wait for it to do work before finishing the test.
  warm_boot_events_.Start();
  was_run.WaitForNotification();
  warm_boot_events_.Stop();

  // Confirm that the event loop thread is stopped.
  EXPECT_CALL(mock_consumer_notifier_, WaitForNotificationAndPop).Times(0);
}
}  // namespace
}  // namespace p4rt_app
