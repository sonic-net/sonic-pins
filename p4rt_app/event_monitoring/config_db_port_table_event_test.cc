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
#include "p4rt_app/sonic/adapters/mock_table_adapter.h"
#include "p4rt_app/sonic/redis_connections.h"

namespace p4rt_app {
namespace {

using ::gutil::StatusIs;
using ::testing::HasSubstr;
using ::testing::Return;

// Expected SONiC commands assumed by state events.
constexpr char kSetCommand[] = "SET";
constexpr char kDelCommand[] = "DEL";

std::vector<std::pair<std::string, std::string>> IdValueEntry(
    const std::string& id) {
  return {{"id", id}};
}

TEST(PortTableIdEventTest, AcceptEthernetPortIds) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  sonic::PortTable mock_port_table{
      .app_db = std::make_unique<sonic::MockTableAdapter>(),
      .app_state_db = std::make_unique<sonic::MockTableAdapter>(),
  };
  auto mock_app_db =
      static_cast<sonic::MockTableAdapter*>(mock_port_table.app_db.get());
  auto mock_app_state_db =
      static_cast<sonic::MockTableAdapter*>(mock_port_table.app_state_db.get());

  EXPECT_CALL(mock_p4runtime_impl, AddPortTranslation("Ethernet1/1/1", "1"))
      .WillOnce(Return(absl::OkStatus()));
  EXPECT_CALL(*mock_app_db, set("Ethernet1/1/1", IdValueEntry("1"))).Times(1);
  EXPECT_CALL(*mock_app_state_db, set("Ethernet1/1/1", IdValueEntry("1")))
      .Times(1);

  ConfigDbPortTableEventHandler event_handler(&mock_p4runtime_impl,
                                              &mock_port_table);
  EXPECT_OK(
      event_handler.HandleEvent(kSetCommand, "Ethernet1/1/1", {{"id", "1"}}));
}

TEST(PortTableIdEventTest, AcceptPortChannelPortIds) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  sonic::PortTable mock_port_table{
      .app_db = std::make_unique<sonic::MockTableAdapter>(),
      .app_state_db = std::make_unique<sonic::MockTableAdapter>(),
  };
  auto mock_app_db =
      static_cast<sonic::MockTableAdapter*>(mock_port_table.app_db.get());
  auto mock_app_state_db =
      static_cast<sonic::MockTableAdapter*>(mock_port_table.app_state_db.get());

  EXPECT_CALL(mock_p4runtime_impl, AddPortTranslation("PortChannel11", "2001"))
      .WillOnce(Return(absl::OkStatus()));
  EXPECT_CALL(*mock_app_db, set("PortChannel11", IdValueEntry("2001")))
      .Times(1);
  EXPECT_CALL(*mock_app_state_db, set("PortChannel11", IdValueEntry("2001")))
      .Times(1);

  ConfigDbPortTableEventHandler event_handler(&mock_p4runtime_impl,
                                              &mock_port_table);
  EXPECT_OK(event_handler.HandleEvent(kSetCommand, "PortChannel11",
                                      {{"id", "2001"}}));
}

TEST(PortTableIdEventTest, IgnoreUnexpectedPortNames) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  sonic::PortTable mock_port_table{
      .app_db = std::make_unique<sonic::MockTableAdapter>(),
      .app_state_db = std::make_unique<sonic::MockTableAdapter>(),
  };
  auto mock_app_db =
      static_cast<sonic::MockTableAdapter*>(mock_port_table.app_db.get());
  auto mock_app_state_db =
      static_cast<sonic::MockTableAdapter*>(mock_port_table.app_state_db.get());

  EXPECT_CALL(mock_p4runtime_impl, AddPortTranslation).Times(0);
  EXPECT_CALL(mock_p4runtime_impl, RemovePortTranslation).Times(0);
  EXPECT_CALL(*mock_app_db, set).Times(0);
  EXPECT_CALL(*mock_app_db, del).Times(0);
  EXPECT_CALL(*mock_app_state_db, set).Times(0);
  EXPECT_CALL(*mock_app_state_db, del).Times(0);

  ConfigDbPortTableEventHandler event_handler(&mock_p4runtime_impl,
                                              &mock_port_table);
  EXPECT_OK(event_handler.HandleEvent(kDelCommand, "loopback0", {{"id", "1"}}));
}

TEST(PortTableIdEventTest, SetMultiplePortIds) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  sonic::PortTable mock_port_table{
      .app_db = std::make_unique<sonic::MockTableAdapter>(),
      .app_state_db = std::make_unique<sonic::MockTableAdapter>(),
  };
  auto mock_app_db =
      static_cast<sonic::MockTableAdapter*>(mock_port_table.app_db.get());
  auto mock_app_state_db =
      static_cast<sonic::MockTableAdapter*>(mock_port_table.app_state_db.get());

  EXPECT_CALL(mock_p4runtime_impl, AddPortTranslation("Ethernet1/1/1", "1"))
      .WillOnce(Return(absl::OkStatus()));
  EXPECT_CALL(*mock_app_db, set("Ethernet1/1/1", IdValueEntry("1"))).Times(1);
  EXPECT_CALL(*mock_app_state_db, set("Ethernet1/1/1", IdValueEntry("1")))
      .Times(1);

  EXPECT_CALL(mock_p4runtime_impl, AddPortTranslation("Ethernet2", "2"))
      .WillOnce(Return(absl::OkStatus()));
  EXPECT_CALL(*mock_app_db, set("Ethernet2", IdValueEntry("2"))).Times(1);
  EXPECT_CALL(*mock_app_state_db, set("Ethernet2", IdValueEntry("2"))).Times(1);

  ConfigDbPortTableEventHandler event_handler(&mock_p4runtime_impl,
                                              &mock_port_table);
  EXPECT_OK(
      event_handler.HandleEvent(kSetCommand, "Ethernet1/1/1", {{"id", "1"}}));
  EXPECT_OK(event_handler.HandleEvent(kSetCommand, "Ethernet2", {{"id", "2"}}));
}

TEST(PortTableIdEventTest, PortIdZeroShouldNotAddToP4RuntimeOnSet) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  sonic::PortTable mock_port_table{
      .app_db = std::make_unique<sonic::MockTableAdapter>(),
      .app_state_db = std::make_unique<sonic::MockTableAdapter>(),
  };
  auto mock_app_db =
      static_cast<sonic::MockTableAdapter*>(mock_port_table.app_db.get());
  auto mock_app_state_db =
      static_cast<sonic::MockTableAdapter*>(mock_port_table.app_state_db.get());

  // Because an ID 0 is ignored we should not call add the port.
  EXPECT_CALL(mock_p4runtime_impl, AddPortTranslation).Times(0);

  // However, because P4RT App may already have another ID assigned to the port
  // we send a remove request to ensure the port translation is removed.
  EXPECT_CALL(mock_p4runtime_impl, RemovePortTranslation("Ethernet1/1/1"))
      .WillOnce(Return(absl::OkStatus()));
  EXPECT_CALL(*mock_app_db, set("Ethernet1/1/1", IdValueEntry("0"))).Times(1);
  EXPECT_CALL(*mock_app_state_db, set("Ethernet1/1/1", IdValueEntry("0")))
      .Times(1);

  ConfigDbPortTableEventHandler event_handler(&mock_p4runtime_impl,
                                              &mock_port_table);
  EXPECT_OK(
      event_handler.HandleEvent(kSetCommand, "Ethernet1/1/1", {{"id", "0"}}));
}

TEST(PortTableIdEventTest, UpdatePortId) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  sonic::PortTable mock_port_table{
      .app_db = std::make_unique<sonic::MockTableAdapter>(),
      .app_state_db = std::make_unique<sonic::MockTableAdapter>(),
  };
  auto mock_app_db =
      static_cast<sonic::MockTableAdapter*>(mock_port_table.app_db.get());
  auto mock_app_state_db =
      static_cast<sonic::MockTableAdapter*>(mock_port_table.app_state_db.get());

  EXPECT_CALL(mock_p4runtime_impl, AddPortTranslation("Ethernet1/1/1", "2"))
      .WillOnce(Return(absl::OkStatus()));
  EXPECT_CALL(*mock_app_db, set("Ethernet1/1/1", IdValueEntry("2"))).Times(1);
  EXPECT_CALL(*mock_app_state_db, set("Ethernet1/1/1", IdValueEntry("2")))
      .Times(1);

  EXPECT_CALL(mock_p4runtime_impl, AddPortTranslation("Ethernet1/1/1", "3"))
      .WillOnce(Return(absl::OkStatus()));
  EXPECT_CALL(*mock_app_db, set("Ethernet1/1/1", IdValueEntry("3"))).Times(1);
  EXPECT_CALL(*mock_app_state_db, set("Ethernet1/1/1", IdValueEntry("3")))
      .Times(1);

  ConfigDbPortTableEventHandler event_handler(&mock_p4runtime_impl,
                                              &mock_port_table);
  EXPECT_OK(
      event_handler.HandleEvent(kSetCommand, "Ethernet1/1/1", {{"id", "2"}}));
  EXPECT_OK(
      event_handler.HandleEvent(kSetCommand, "Ethernet1/1/1", {{"id", "3"}}));
}

TEST(PortTableIdEventTest, SetPortIdToAnEmptyString) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  sonic::PortTable mock_port_table{
      .app_db = std::make_unique<sonic::MockTableAdapter>(),
      .app_state_db = std::make_unique<sonic::MockTableAdapter>(),
  };
  auto mock_app_db =
      static_cast<sonic::MockTableAdapter*>(mock_port_table.app_db.get());
  auto mock_app_state_db =
      static_cast<sonic::MockTableAdapter*>(mock_port_table.app_state_db.get());

  EXPECT_CALL(mock_p4runtime_impl, RemovePortTranslation("Ethernet1/1/1"))
      .WillOnce(Return(absl::OkStatus()));
  EXPECT_CALL(*mock_app_db, del("Ethernet1/1/1")).Times(1);
  EXPECT_CALL(*mock_app_state_db, del("Ethernet1/1/1")).Times(1);

  ConfigDbPortTableEventHandler event_handler(&mock_p4runtime_impl,
                                              &mock_port_table);
  EXPECT_OK(
      event_handler.HandleEvent(kSetCommand, "Ethernet1/1/1", {{"id", ""}}));
}

TEST(PortTableIdEventTest, DeletePortId) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  sonic::PortTable mock_port_table{
      .app_db = std::make_unique<sonic::MockTableAdapter>(),
      .app_state_db = std::make_unique<sonic::MockTableAdapter>(),
  };
  auto mock_app_db =
      static_cast<sonic::MockTableAdapter*>(mock_port_table.app_db.get());
  auto mock_app_state_db =
      static_cast<sonic::MockTableAdapter*>(mock_port_table.app_state_db.get());

  EXPECT_CALL(mock_p4runtime_impl, RemovePortTranslation("Ethernet1/1/1"))
      .WillOnce(Return(absl::OkStatus()));
  EXPECT_CALL(*mock_app_db, del("Ethernet1/1/1")).Times(1);
  EXPECT_CALL(*mock_app_state_db, del("Ethernet1/1/1")).Times(1);

  ConfigDbPortTableEventHandler event_handler(&mock_p4runtime_impl,
                                              &mock_port_table);
  EXPECT_OK(
      event_handler.HandleEvent(kDelCommand, "Ethernet1/1/1", {{"id", "1"}}));
}

TEST(PortTableIdEventTest, UnexpectedOperationReturnsAnError) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  sonic::PortTable mock_port_table{
      .app_db = std::make_unique<sonic::MockTableAdapter>(),
      .app_state_db = std::make_unique<sonic::MockTableAdapter>(),
  };
  auto mock_app_db =
      static_cast<sonic::MockTableAdapter*>(mock_port_table.app_db.get());
  auto mock_app_state_db =
      static_cast<sonic::MockTableAdapter*>(mock_port_table.app_state_db.get());

  // Invalid operations should not update any redis state.
  EXPECT_CALL(mock_p4runtime_impl, AddPortTranslation).Times(0);
  EXPECT_CALL(mock_p4runtime_impl, RemovePortTranslation).Times(0);
  EXPECT_CALL(*mock_app_db, set).Times(0);
  EXPECT_CALL(*mock_app_db, del).Times(0);
  EXPECT_CALL(*mock_app_state_db, set).Times(0);
  EXPECT_CALL(*mock_app_state_db, del).Times(0);

  ConfigDbPortTableEventHandler event_handler(&mock_p4runtime_impl,
                                              &mock_port_table);
  EXPECT_THAT(event_handler.HandleEvent("INVALID_OPERATION", "Ethernet1/1/1",
                                        {{"id", "1"}}),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(PortTableIdEventTest, P4RuntimeAddPortTranslationFails) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  sonic::PortTable mock_port_table{
      .app_db = std::make_unique<sonic::MockTableAdapter>(),
      .app_state_db = std::make_unique<sonic::MockTableAdapter>(),
  };
  auto mock_app_db =
      static_cast<sonic::MockTableAdapter*>(mock_port_table.app_db.get());
  auto mock_app_state_db =
      static_cast<sonic::MockTableAdapter*>(mock_port_table.app_state_db.get());

  EXPECT_CALL(mock_p4runtime_impl, AddPortTranslation("Ethernet1/1/1", "1"))
      .WillOnce(Return(absl::InvalidArgumentError("could not add")));
  EXPECT_CALL(*mock_app_db, set).Times(0);
  EXPECT_CALL(*mock_app_state_db, set).Times(0);

  ConfigDbPortTableEventHandler event_handler(&mock_p4runtime_impl,
                                              &mock_port_table);
  EXPECT_THAT(
      event_handler.HandleEvent(kSetCommand, "Ethernet1/1/1", {{"id", "1"}}),
      StatusIs(absl::StatusCode::kInvalidArgument, HasSubstr("could not add")));
}

TEST(PortTableIdEventTest, P4RuntimeRemovePortTranslationFails) {
  MockP4RuntimeImpl mock_p4runtime_impl;
  sonic::PortTable mock_port_table{
      .app_db = std::make_unique<sonic::MockTableAdapter>(),
      .app_state_db = std::make_unique<sonic::MockTableAdapter>(),
  };
  auto mock_app_db =
      static_cast<sonic::MockTableAdapter*>(mock_port_table.app_db.get());
  auto mock_app_state_db =
      static_cast<sonic::MockTableAdapter*>(mock_port_table.app_state_db.get());

  EXPECT_CALL(mock_p4runtime_impl, RemovePortTranslation("Ethernet1/1/1"))
      .WillOnce(Return(absl::UnknownError("could not remove")));
  EXPECT_CALL(*mock_app_db, del).Times(0);
  EXPECT_CALL(*mock_app_state_db, del).Times(0);

  ConfigDbPortTableEventHandler event_handler(&mock_p4runtime_impl,
                                              &mock_port_table);
  EXPECT_THAT(
      event_handler.HandleEvent(kDelCommand, "Ethernet1/1/1", {{"id", "1"}}),
      StatusIs(absl::StatusCode::kUnknown, HasSubstr("could not remove")));
}

}  // namespace
}  // namespace p4rt_app
