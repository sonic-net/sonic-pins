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
#include "p4rt_app/sonic/adapters/fake_sonic_db_table.h"

#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"

namespace p4rt_app {
namespace sonic {
namespace {

using ::testing::ElementsAre;
using ::testing::UnorderedElementsAre;

TEST(FakeSonicDbTest, InsertSingleEntry) {
  FakeSonicDbTable table;
  table.InsertTableEntry("entry", /*values=*/{});
  EXPECT_THAT(table.GetAllKeys(), ElementsAre("entry"));
}

TEST(FakeSonicDbTest, InsertDuplicateEntry) {
  FakeSonicDbTable table;
  table.InsertTableEntry("entry", /*values=*/{});
  table.InsertTableEntry("entry", /*values=*/{});
  EXPECT_THAT(table.GetAllKeys(), ElementsAre("entry"));
}

TEST(FakeSonicDbTest, InsertMultipleEntries) {
  FakeSonicDbTable table;
  table.InsertTableEntry("entry0", /*values=*/{});
  table.InsertTableEntry("entry1", /*values=*/{});
  EXPECT_THAT(table.GetAllKeys(), UnorderedElementsAre("entry0", "entry1"));
}

TEST(FakeSonicDbTest, ReadNonExistantEntryReturnsNotFoundError) {
  FakeSonicDbTable table;
  EXPECT_EQ(table.ReadTableEntry("bad_entry").status().code(),
            absl::StatusCode::kNotFound);
}

TEST(FakeSonicDbTest, ReadBackEntry) {
  FakeSonicDbTable table;
  table.InsertTableEntry("entry", /*values=*/{{"key", "value"}});

  auto result = table.ReadTableEntry("entry");
  ASSERT_TRUE(result.ok());
  EXPECT_THAT(*result, UnorderedElementsAre(std::make_pair("key", "value")));
}

TEST(FakeSonicDbTest, InsertDuplicateKeyReplacesExistingEntry) {
  FakeSonicDbTable table;

  // First insert.
  table.InsertTableEntry("entry", /*values=*/{{"key", "value"}});
  auto result = table.ReadTableEntry("entry");
  ASSERT_TRUE(result.ok());
  EXPECT_THAT(*result, UnorderedElementsAre(std::make_pair("key", "value")));

  // Second insert.
  table.InsertTableEntry("entry", /*values=*/{{"new_key", "new_value"}});
  result = table.ReadTableEntry("entry");
  ASSERT_TRUE(result.ok());
  EXPECT_THAT(*result,
              UnorderedElementsAre(std::make_pair("new_key", "new_value")));
}

TEST(FakeSonicDbTest, DeleteNonExistantEntry) {
  // Is acts as a no-op.
  FakeSonicDbTable table;
  table.DeleteTableEntry("entry");
}

TEST(FakeSonicDbTest, DeleteEntry) {
  FakeSonicDbTable table;

  // First insert.
  table.InsertTableEntry("entry", /*values=*/{{"key", "value"}});
  EXPECT_THAT(table.GetAllKeys(), ElementsAre("entry"));

  // Then delete.
  table.DeleteTableEntry("entry");
  EXPECT_TRUE(table.GetAllKeys().empty());
}

TEST(FakeSonicDbDeathTest, GetNotificationFailsIfNoNotificationExists) {
  FakeSonicDbTable table;
  std::string op;
  std::string data;
  SonicDbEntryList value;

  EXPECT_FALSE(table.GetNextNotification(op, data, value).ok());
}

TEST(FakeSonicDbTest, DefaultNotificationResponseIsSuccess) {
  FakeSonicDbTable table;
  std::string op;
  std::string data;
  SonicDbEntryList values;

  // First insert.
  EXPECT_TRUE(table.PushNotification("entry"));
  table.GetNextNotification(op, data, values);
  EXPECT_EQ(op, "SWSS_RC_SUCCESS");
  EXPECT_EQ(data, "entry");
  EXPECT_THAT(values,
              ElementsAre(SonicDbKeyValue{"err_str", "SWSS_RC_SUCCESS"}));
}

TEST(FakeSonicDbTest, SetNotificationResponseForKey) {
  FakeSonicDbTable table;
  std::string op;
  std::string data;
  SonicDbEntryList values;

  table.SetResponseForKey(/*key=*/"entry", /*code=*/"SWSS_RC_UNKNOWN",
                          /*message=*/"my error message");
  EXPECT_FALSE(table.PushNotification("entry"));
  table.GetNextNotification(op, data, values);
  EXPECT_EQ(op, "SWSS_RC_UNKNOWN");
  EXPECT_EQ(data, "entry");
  EXPECT_THAT(values,
              ElementsAre(SonicDbKeyValue{"err_str", "my error message"}));
}

TEST(FakeSonicDbTest, StateDbUpdatedOnInsertSuccess) {
  FakeSonicDbTable state_table;
  FakeSonicDbTable table("AppDb:TABLE", &state_table);

  table.InsertTableEntry("entry", /*values=*/{{"key", "value"}});
  EXPECT_TRUE(table.PushNotification("entry"));
  auto result = table.ReadTableEntry("entry");
  ASSERT_TRUE(result.ok());
  EXPECT_THAT(*result, UnorderedElementsAre(std::make_pair("key", "value")));

  result = state_table.ReadTableEntry("entry");
  ASSERT_TRUE(result.ok());
  EXPECT_THAT(*result, UnorderedElementsAre(std::make_pair("key", "value")));
}

TEST(FakeSonicDbTest, StateDbUpdatedOnDeleteSuccess) {
  FakeSonicDbTable state_table;
  FakeSonicDbTable table("AppDb:TABLE", &state_table);

  // First insert
  table.InsertTableEntry("entry", /*values=*/{{"key", "value"}});
  EXPECT_TRUE(table.PushNotification("entry"));
  EXPECT_THAT(table.GetAllKeys(), ElementsAre("entry"));
  EXPECT_THAT(state_table.GetAllKeys(), ElementsAre("entry"));

  // Then delete.
  table.DeleteTableEntry("entry");
  EXPECT_TRUE(table.PushNotification("entry"));
  EXPECT_TRUE(table.GetAllKeys().empty());
  EXPECT_TRUE(state_table.GetAllKeys().empty());
}

TEST(FakeSonicDbTest, StateDbUpdatedOnModifySuccess) {
  FakeSonicDbTable state_table;
  FakeSonicDbTable table("AppDb:TABLE", &state_table);

  // First insert.
  table.InsertTableEntry("entry", /*values=*/{{"key", "value"}});
  EXPECT_TRUE(table.PushNotification("entry"));
  auto result = table.ReadTableEntry("entry");
  ASSERT_TRUE(result.ok());
  EXPECT_THAT(*result, UnorderedElementsAre(std::make_pair("key", "value")));

  result = state_table.ReadTableEntry("entry");
  ASSERT_TRUE(result.ok());
  EXPECT_THAT(*result, UnorderedElementsAre(std::make_pair("key", "value")));

  // Then modify.
  table.DeleteTableEntry("entry");
  table.InsertTableEntry("entry", /*values=*/{});
  EXPECT_TRUE(table.PushNotification("entry"));

  result = table.ReadTableEntry("entry");
  ASSERT_TRUE(result.ok());
  EXPECT_TRUE(result->empty());

  result = state_table.ReadTableEntry("entry");
  ASSERT_TRUE(result.ok());
  EXPECT_TRUE(result->empty());
}

TEST(FakeSonicDbTest, StateDbDoesNotUpdatedOnInsertFailure) {
  FakeSonicDbTable state_table;
  FakeSonicDbTable table("AppDb:TABLE", &state_table);

  table.SetResponseForKey(/*key=*/"entry", /*code=*/"SWSS_RC_UNKNOWN",
                          /*message=*/"my error message");
  table.InsertTableEntry("entry", /*values=*/{{"key", "value"}});
  EXPECT_FALSE(table.PushNotification("entry"));

  // We still insert the entry, and it is the callers responsiblity to clean it
  // up on failure.
  auto result = table.ReadTableEntry("entry");
  ASSERT_TRUE(result.ok());
  EXPECT_THAT(*result, UnorderedElementsAre(std::make_pair("key", "value")));

  // However, on failure the StateDb should not be affected.
  EXPECT_TRUE(state_table.GetAllKeys().empty());
}

TEST(FakeSonicDbTest, StateDbDoesNotUpdatedOnDeleteFailure) {
  FakeSonicDbTable state_table;
  FakeSonicDbTable table("AppDb:TABLE", &state_table);

  // First insert
  table.InsertTableEntry("entry", /*values=*/{{"key", "value"}});
  EXPECT_TRUE(table.PushNotification("entry"));
  EXPECT_THAT(table.GetAllKeys(), ElementsAre("entry"));
  EXPECT_THAT(state_table.GetAllKeys(), ElementsAre("entry"));

  // Then delete with failure
  table.SetResponseForKey(/*key=*/"entry", /*code=*/"SWSS_RC_UNKNOWN",
                          /*message=*/"my error message");
  table.DeleteTableEntry("entry");
  EXPECT_FALSE(table.PushNotification("entry"));

  // We still delete the entry, and it is the callers responsiblity to cean it
  // up on failure.
  EXPECT_TRUE(table.GetAllKeys().empty());

  // However, on failure the StateDb should not be affected.
  EXPECT_THAT(state_table.GetAllKeys(), ElementsAre("entry"));
}

TEST(FakeSonicDbTest, StateDbDoesNotUpdatedOnModifyFailure) {
  FakeSonicDbTable state_table;
  FakeSonicDbTable table("AppDb:TABLE", &state_table);

  // First insert.
  table.InsertTableEntry("entry", /*values=*/{{"key", "value"}});
  EXPECT_TRUE(table.PushNotification("entry"));
  EXPECT_THAT(table.GetAllKeys(), ElementsAre("entry"));
  EXPECT_THAT(state_table.GetAllKeys(), ElementsAre("entry"));

  // Then modify with failure.
  table.DeleteTableEntry("entry");
  table.SetResponseForKey(/*key=*/"entry", /*code=*/"SWSS_RC_UNKNOWN",
                          /*message=*/"my error message");
  table.InsertTableEntry("entry", /*values=*/{});
  EXPECT_FALSE(table.PushNotification("entry"));

  // We still modify the entry, and it is the callers responsiblity to clean it
  // up on failure.
  auto result = table.ReadTableEntry("entry");
  ASSERT_TRUE(result.ok());
  EXPECT_TRUE(result->empty());

  // However, on failure the StateDb should not be affected.
  result = state_table.ReadTableEntry("entry");
  ASSERT_TRUE(result.ok());
  EXPECT_THAT(*result, UnorderedElementsAre(std::make_pair("key", "value")));
}

TEST(FakeSonicDbTest, DebutState) {
  // This is a no-op.
  FakeSonicDbTable table;
  table.InsertTableEntry("entry", /*values=*/{{"key", "value"}});
  table.DebugState();
}

}  // namespace
}  // namespace sonic
}  // namespace p4rt_app
