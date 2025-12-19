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
#include "p4rt_app/event_monitoring/app_state_db_port_table_event.h"

#include <deque>
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

// Expected SONiC commands assumed by PortChangeEvents.
constexpr char kSetCommand[] = "SET";
constexpr char kDelCommand[] = "DEL";

TEST(PortTableEventTest, SetEventCreatesPacketIoPort) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  AppStateDbPortTableEventHandler port_change_events(&mock_p4runtime_impl);

  EXPECT_CALL(mock_p4runtime_impl, AddPacketIoPort("Ethernet0"))
      .WillOnce(Return(absl::OkStatus()));
  EXPECT_CALL(mock_p4runtime_impl, AddPacketIoPort("Ethernet1"))
      .WillOnce(Return(absl::OkStatus()));

  EXPECT_OK(port_change_events.HandleEvent(kSetCommand, "Ethernet0",
                                           {{"id", "1"}, {"status", "up"}}));
  EXPECT_OK(port_change_events.HandleEvent(kSetCommand, "Ethernet1",
                                           {{"id", "4"}, {"status", "down"}}));
}

TEST(PortTableEventTest, DeleteEventRemovesPacketIoPort) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  AppStateDbPortTableEventHandler port_change_events(&mock_p4runtime_impl);

  EXPECT_CALL(mock_p4runtime_impl, RemovePacketIoPort("Ethernet1/1/1"))
      .WillOnce(Return(absl::OkStatus()));
  EXPECT_CALL(mock_p4runtime_impl, RemovePacketIoPort("Ethernet1/2/1"))
      .WillOnce(Return(absl::OkStatus()));

  EXPECT_OK(port_change_events.HandleEvent(kDelCommand, "Ethernet1/1/1",
                                           {{"id", "1"}, {"status", "up"}}));
  EXPECT_OK(port_change_events.HandleEvent(kDelCommand, "Ethernet1/2/1",
                                           {{"id", "4"}, {"status", "down"}}));
}

TEST(PortTableEventTest, NonEthernetPortEventIsANoop) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  AppStateDbPortTableEventHandler port_change_events(&mock_p4runtime_impl);

  EXPECT_CALL(mock_p4runtime_impl, AddPortTranslation).Times(0);
  EXPECT_CALL(mock_p4runtime_impl, RemovePortTranslation).Times(0);

  EXPECT_OK(port_change_events.HandleEvent(kSetCommand, "bond0",
                                           {{"id", "1"}, {"status", "up"}}));
}

TEST(PortTableEventTest, UnknownPortEventFails) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  AppStateDbPortTableEventHandler port_change_events(&mock_p4runtime_impl);

  EXPECT_CALL(mock_p4runtime_impl, AddPortTranslation).Times(0);
  EXPECT_CALL(mock_p4runtime_impl, RemovePortTranslation).Times(0);

  EXPECT_THAT(port_change_events.HandleEvent(/*op=*/"UNKNOWN", "Ethernet1",
                                             {{"id", "1"}, {"status", "up"}}),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(PortTableEventTest, P4RuntimeAddPacketIoFails) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  AppStateDbPortTableEventHandler port_change_events(&mock_p4runtime_impl);

  EXPECT_CALL(mock_p4runtime_impl, AddPacketIoPort)
      .WillOnce(Return(absl::InvalidArgumentError("something was bad")));

  EXPECT_THAT(port_change_events.HandleEvent(kSetCommand, "Ethernet1/2",
                                             {{"id", "1"}, {"status", "up"}}),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       HasSubstr("something was bad")));
}

TEST(PortTableEventTest, P4RuntimeRemovePacketIoFails) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  AppStateDbPortTableEventHandler port_change_events(&mock_p4runtime_impl);

  EXPECT_CALL(mock_p4runtime_impl, RemovePacketIoPort)
      .WillOnce(Return(absl::InvalidArgumentError("something was bad")));

  EXPECT_THAT(port_change_events.HandleEvent(kDelCommand, "Ethernet1/5/4",
                                             {{"id", "1"}, {"status", "up"}}),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       HasSubstr("something was bad")));
}

}  // namespace
}  // namespace p4rt_app
