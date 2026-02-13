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
#include "p4rt_app/event_monitoring/config_db_port_table_event.h"

#include <memory>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "p4rt_app/p4runtime/mock_p4runtime_impl.h"

namespace p4rt_app {
namespace {

using ::gutil::StatusIs;
using ::testing::HasSubstr;
using ::testing::Return;
using ::testing::StrictMock;

// Expected SONiC commands assumed by state events.
constexpr char kSetCommand[] = "SET";
constexpr char kDelCommand[] = "DEL";

TEST(PortTableIdEventTest, AcceptEthernetPortIds) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  EXPECT_CALL(mock_p4runtime_impl,
              AddPortTranslation("Ethernet1/1/1", "1", /*update_dbs=*/true))
      .WillOnce(Return(absl::OkStatus()));
  ConfigDbPortTableEventHandler event_handler(&mock_p4runtime_impl);
  EXPECT_OK(
      event_handler.HandleEvent(kSetCommand, "Ethernet1/1/1", {{"id", "1"}}));
}

TEST(PortTableIdEventTest, AcceptPortChannelPortIds) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  EXPECT_CALL(mock_p4runtime_impl,
              AddPortTranslation("PortChannel11", "2001", /*update_dbs=*/true))
      .WillOnce(Return(absl::OkStatus()));
  ConfigDbPortTableEventHandler event_handler(&mock_p4runtime_impl);
  EXPECT_OK(event_handler.HandleEvent(kSetCommand, "PortChannel11",
                                      {{"id", "2001"}}));
}

TEST(PortTableIdEventTest, AcceptCpuPortIds) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  EXPECT_CALL(mock_p4runtime_impl,
              AddPortTranslation("CPU", "3", /*update_dbs=*/true))
      .WillOnce(Return(absl::OkStatus()));
  ConfigDbPortTableEventHandler event_handler(&mock_p4runtime_impl);
  EXPECT_OK(event_handler.HandleEvent(kSetCommand, "CPU", {{"id", "3"}}));
}

TEST(PortTableIdEventTest, SetMultiplePortIds) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  EXPECT_CALL(mock_p4runtime_impl,
              AddPortTranslation("Ethernet1/1/1", "1", /*update_dbs=*/true))
      .WillOnce(Return(absl::OkStatus()));
  EXPECT_CALL(mock_p4runtime_impl,
              AddPortTranslation("Ethernet2", "2", /*update_dbs=*/true))
      .WillOnce(Return(absl::OkStatus()));
  ConfigDbPortTableEventHandler event_handler(&mock_p4runtime_impl);
  EXPECT_OK(
      event_handler.HandleEvent(kSetCommand, "Ethernet1/1/1", {{"id", "1"}}));
  EXPECT_OK(event_handler.HandleEvent(kSetCommand, "Ethernet2", {{"id", "2"}}));
}

TEST(PortTableIdEventTest, UpdatePortId) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  EXPECT_CALL(mock_p4runtime_impl,
              AddPortTranslation("Ethernet1/1/1", "2", /*update_dbs=*/true))
      .WillOnce(Return(absl::OkStatus()));
  EXPECT_CALL(mock_p4runtime_impl,
              AddPortTranslation("Ethernet1/1/1", "3", /*update_dbs=*/true))
      .WillOnce(Return(absl::OkStatus()));
  ConfigDbPortTableEventHandler event_handler(&mock_p4runtime_impl);
  EXPECT_OK(
      event_handler.HandleEvent(kSetCommand, "Ethernet1/1/1", {{"id", "2"}}));
  EXPECT_OK(
      event_handler.HandleEvent(kSetCommand, "Ethernet1/1/1", {{"id", "3"}}));
}

TEST(PortTableIdEventTest, SetPortIdToAnEmptyString) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  EXPECT_CALL(mock_p4runtime_impl, RemovePortTranslation("Ethernet1/1/1"))
      .WillOnce(Return(absl::OkStatus()));
  ConfigDbPortTableEventHandler event_handler(&mock_p4runtime_impl);
  EXPECT_OK(
      event_handler.HandleEvent(kSetCommand, "Ethernet1/1/1", {{"id", ""}}));
}

TEST(PortTableIdEventTest, DeletePortId) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  EXPECT_CALL(mock_p4runtime_impl, RemovePortTranslation("Ethernet1/1/1"))
      .WillOnce(Return(absl::OkStatus()));
  ConfigDbPortTableEventHandler event_handler(&mock_p4runtime_impl);
  EXPECT_OK(
      event_handler.HandleEvent(kDelCommand, "Ethernet1/1/1", {{"id", "1"}}));
}

TEST(PortTableIdEventTest, UnexpectedOperationReturnsAnError) {
  StrictMock<MockP4RuntimeImpl> mock_p4runtime_impl;  // Expect no calls.
  // Invalid operations should not update any redis state.
  EXPECT_CALL(mock_p4runtime_impl, AddPortTranslation).Times(0);
  EXPECT_CALL(mock_p4runtime_impl, RemovePortTranslation).Times(0);
  ConfigDbPortTableEventHandler event_handler(&mock_p4runtime_impl);
  EXPECT_THAT(event_handler.HandleEvent("INVALID_OPERATION", "Ethernet1/1/1",
                                        {{"id", "1"}}),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(PortTableIdEventTest, P4RuntimeAddPortTranslationFails) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  EXPECT_CALL(mock_p4runtime_impl,
              AddPortTranslation("Ethernet1/1/1", "1", /*update_dbs=*/true))
      .WillOnce(Return(absl::InvalidArgumentError("could not add")));
  ConfigDbPortTableEventHandler event_handler(&mock_p4runtime_impl);
  EXPECT_THAT(
      event_handler.HandleEvent(kSetCommand, "Ethernet1/1/1", {{"id", "1"}}),
      StatusIs(absl::StatusCode::kInvalidArgument, HasSubstr("could not add")));
}

TEST(PortTableIdEventTest, P4RuntimeRemovePortTranslationFails) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  EXPECT_CALL(mock_p4runtime_impl, RemovePortTranslation("Ethernet1/1/1"))
      .WillOnce(Return(absl::UnknownError("could not remove")));
  ConfigDbPortTableEventHandler event_handler(&mock_p4runtime_impl);
  EXPECT_THAT(
      event_handler.HandleEvent(kDelCommand, "Ethernet1/1/1", {{"id", "1"}}),
      StatusIs(absl::StatusCode::kUnknown, HasSubstr("could not remove")));
}

}  // namespace
}  // namespace p4rt_app
