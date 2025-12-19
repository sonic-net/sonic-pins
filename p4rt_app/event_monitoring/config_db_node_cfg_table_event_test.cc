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
#include "p4rt_app/event_monitoring/config_db_node_cfg_table_event.h"

#include "absl/status/status.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "p4rt_app/p4runtime/mock_p4runtime_impl.h"
#include "swss/schema.h"

namespace p4rt_app {
namespace {

using ::gutil::StatusIs;
using ::testing::HasSubstr;
using ::testing::Return;

TEST(ConfigDbNodeCfgEventTest, CanSetDeviceId) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  ConfigDbNodeCfgTableEventHandler event_handler(&mock_p4runtime_impl);

  EXPECT_CALL(mock_p4runtime_impl, UpdateDeviceId(123))
      .WillOnce(Return(absl::OkStatus()));

  EXPECT_OK(event_handler.HandleEvent(SET_COMMAND, "integrated_circuit0",
                                      {{"node-id", "123"}}));
}

TEST(ConfigDbNodeCfgEventTest, CanDeleteDeviceId) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  ConfigDbNodeCfgTableEventHandler event_handler(&mock_p4runtime_impl);

  EXPECT_CALL(mock_p4runtime_impl, UpdateDeviceId(0))
      .WillOnce(Return(absl::OkStatus()));

  EXPECT_OK(event_handler.HandleEvent(DEL_COMMAND, "integrated_circuit0",
                                      {{"node-id", "123"}}));
}

TEST(ConfigDbNodeCfgEventTest, UnexpectedKeysAreNoops) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  ConfigDbNodeCfgTableEventHandler event_handler(&mock_p4runtime_impl);

  EXPECT_CALL(mock_p4runtime_impl, UpdateDeviceId).Times(0);

  EXPECT_OK(event_handler.HandleEvent(SET_COMMAND, "unexected_key",
                                      {{"node-id", "123"}}));
}

TEST(ConfigDbNodeCfgEventTest, EmptyNodeIdCallsDelete) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  ConfigDbNodeCfgTableEventHandler event_handler(&mock_p4runtime_impl);

  EXPECT_CALL(mock_p4runtime_impl, UpdateDeviceId(0))
      .WillOnce(Return(absl::OkStatus()))
      .WillOnce(Return(absl::OkStatus()));

  EXPECT_OK(event_handler.HandleEvent(SET_COMMAND, "integrated_circuit0",
                                      {{"node-id", ""}}));
  EXPECT_OK(event_handler.HandleEvent(SET_COMMAND, "integrated_circuit0", {}));
}

TEST(ConfigDbNodeCfgEventTest, InvalidNodeIdCallsDelete) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  ConfigDbNodeCfgTableEventHandler event_handler(&mock_p4runtime_impl);

  EXPECT_CALL(mock_p4runtime_impl, UpdateDeviceId(0))
      .WillOnce(Return(absl::OkStatus()));

  EXPECT_OK(event_handler.HandleEvent(SET_COMMAND, "integrated_circuit0",
                                      {{"node-id", "0xa"}}));
}

TEST(ConfigDbNodeCfgEventTest, DeviceIdUpdateErrorsGetPropagated) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  ConfigDbNodeCfgTableEventHandler event_handler(&mock_p4runtime_impl);

  EXPECT_CALL(mock_p4runtime_impl, UpdateDeviceId)
      .WillOnce(Return(absl::InvalidArgumentError("some invalid error")))
      .WillOnce(Return(absl::UnknownError("some unknown error")));

  EXPECT_THAT(
      event_handler.HandleEvent(SET_COMMAND, "integrated_circuit0",
                                {{"node-id", "1"}}),
      StatusIs(absl::StatusCode::kInvalidArgument, HasSubstr("invalid")));
  EXPECT_THAT(event_handler.HandleEvent(DEL_COMMAND, "integrated_circuit0",
                                        {{"node-id", "1"}}),
              StatusIs(absl::StatusCode::kUnknown, HasSubstr("unknown")));
}

}  // namespace
}  // namespace p4rt_app
