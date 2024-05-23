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

#include <cstdint>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/synchronization/notification.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/io.h"
#include "gutil/status_matchers.h"
#include "p4rt_app/p4runtime/mock_p4runtime_impl.h"
#include "p4rt_app/sonic/adapters/mock_consumer_notifier_adapter.h"
#include "p4rt_app/sonic/adapters/mock_notification_producer_adapter.h"
#include "swss/rediscommand.h"

namespace p4rt_app {
namespace {

using ::gutil::StatusIs;
using ::testing::DoAll;
using ::testing::Eq;
using ::testing::HasSubstr;
using ::testing::Return;
using ::testing::SetArgReferee;

class DebugDataDumpEventHandlerTest : public testing::Test {
 protected:
  DebugDataDumpEventHandlerTest()
      : debug_data_dump_(
            DebugDataDumpEventHandler(mock_p4runtime_, mock_consumer_notifier_,
                                      mock_notification_producer_)) {}

  DebugDataDumpEventHandler debug_data_dump_;

  MockP4RuntimeImpl mock_p4runtime_;
  sonic::MockConsumerNotifierAdapter mock_consumer_notifier_;
  sonic::MockNotificationProducerAdapter mock_notification_producer_;
};

TEST_F(DebugDataDumpEventHandlerTest, DumpDebugDataSuccess) {
  EXPECT_CALL(mock_consumer_notifier_, WaitForNotificationAndPop)
      .WillOnce(DoAll(SetArgReferee<0>("p4rt"), SetArgReferee<1>("path"),
                      SetArgReferee<2>(std::vector<swss::FieldValueTuple>{
                          swss::FieldValueTuple{"level", "alert"}}),
                      Return(true)));
  EXPECT_CALL(mock_p4runtime_, DumpDebugData(Eq("path"), Eq("alert")))
      .WillOnce(Return(absl::OkStatus()));
  auto fv = std::vector<swss::FieldValueTuple>{
      {"status", "success"},
      {"err_str", ""},
  };
  EXPECT_CALL(mock_notification_producer_, send_with_op_key("p4rt", "path", fv))
      .Times(1);

  EXPECT_OK(debug_data_dump_.WaitForEventAndDumpDebugData());
}

TEST_F(DebugDataDumpEventHandlerTest, DumpDebugDataDefaultLogLevelIsAlert) {
  EXPECT_CALL(mock_consumer_notifier_, WaitForNotificationAndPop)
      .WillOnce(DoAll(SetArgReferee<0>("p4rt"), SetArgReferee<1>("path"),
                      SetArgReferee<2>(std::vector<swss::FieldValueTuple>{}),
                      Return(true)));
  EXPECT_CALL(mock_p4runtime_, DumpDebugData(Eq("path"), Eq("alert")))
      .WillOnce(Return(absl::OkStatus()));
  auto fv = std::vector<swss::FieldValueTuple>{
      {"status", "success"},
      {"err_str", ""},
  };
  EXPECT_CALL(mock_notification_producer_, send_with_op_key("p4rt", "path", fv))
      .Times(1);

  EXPECT_OK(debug_data_dump_.WaitForEventAndDumpDebugData());
}

TEST_F(DebugDataDumpEventHandlerTest, DumpDebugDataFails) {
  EXPECT_CALL(mock_consumer_notifier_, WaitForNotificationAndPop)
      .WillOnce(DoAll(SetArgReferee<0>("p4rt"), SetArgReferee<1>("path"),
                      SetArgReferee<2>(std::vector<swss::FieldValueTuple>{
                          swss::FieldValueTuple{"level", "alert"}}),
                      Return(true)));
  EXPECT_CALL(mock_p4runtime_, DumpDebugData(Eq("path"), Eq("alert")))
      .WillOnce(Return(absl::UnknownError("Dump debug data fails.")));
  auto fv = std::vector<swss::FieldValueTuple>{
      {"status", "fail"},
      {"err_str", "Dump debug data fails."},
  };
  EXPECT_CALL(mock_notification_producer_, send_with_op_key("p4rt", "path", fv))
      .Times(1);

  EXPECT_THAT(debug_data_dump_.WaitForEventAndDumpDebugData(),
              StatusIs(absl::StatusCode::kUnknown,
                       HasSubstr("Dump debug data fails.")));
}

TEST_F(DebugDataDumpEventHandlerTest,
       DoNotDumpDebugDataWhenNotificationIsForDifferentComponent) {
  // Instead of getting a notification for p4rt, we get a notification for swss.
  EXPECT_CALL(mock_consumer_notifier_, WaitForNotificationAndPop)
      .WillOnce(DoAll(SetArgReferee<0>("swss:swss"), Return(true)));
  EXPECT_CALL(mock_p4runtime_, DumpDebugData).Times(0);
  EXPECT_CALL(mock_notification_producer_, send_with_op_key).Times(0);

  EXPECT_OK(debug_data_dump_.WaitForEventAndDumpDebugData());
}

TEST_F(DebugDataDumpEventHandlerTest, DoNotDumpDebugDataWhenNotificationFails) {
  EXPECT_CALL(mock_consumer_notifier_, WaitForNotificationAndPop)
      .WillOnce(DoAll(SetArgReferee<0>("p4rt"), Return(false)));
  EXPECT_CALL(mock_p4runtime_, DumpDebugData).Times(0);
  EXPECT_CALL(mock_notification_producer_, send_with_op_key).Times(0);

  EXPECT_THAT(debug_data_dump_.WaitForEventAndDumpDebugData(),
              StatusIs(absl::StatusCode::kUnknown,
                       HasSubstr("Debug data dump events failed/timed-out "
                                 "waiting for a notification.")));
}

TEST_F(DebugDataDumpEventHandlerTest, EventThreadStartStop) {
  // This test will spawn a thread inside the DebugDataDumpEventHandlerTest
  // object which is stopped when the object is destroyed. To ensure we run
  // through the loop at least once we block on a notification.
  absl::Notification was_run;

  // We expect the wait call to be made at least once, but could be called again
  // while waiting for the thread to be stopped.
  EXPECT_CALL(mock_consumer_notifier_, WaitForNotificationAndPop)
      .WillOnce([&was_run](std::string& op, std::string& key,
                           std::vector<swss::FieldValueTuple>& fv,
                           int64_t timeout) {
        was_run.Notify();
        return false;
      })
      .WillRepeatedly(Return(false));

  // Spawn the thread, and wait for it to do work before finishing the test.
  debug_data_dump_.Start();
  was_run.WaitForNotification();
  debug_data_dump_.Stop();
}

}  // namespace
}  // namespace p4rt_app
