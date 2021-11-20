// Copyright 2020 Google LLC
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
#include "p4rt_app/tests/lib//app_db_entry_builder.h"

#include <string>
#include <vector>

#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace p4rt_app {
namespace test_lib {
namespace {

using ::testing::ContainerEq;

using ActionValues = std::vector<std::pair<std::string, std::string>>;

TEST(AppDbEntryBuilderTest, NoMatchFields) {
  auto app_db_entry = AppDbEntryBuilder{}.SetTableName("FIXED_TABLE");
  EXPECT_EQ(app_db_entry.GetKey(), R"(FIXED_TABLE:{})");
}

TEST(AppDbEntryBuilderTest, SingleMatchField) {
  auto app_db_entry = AppDbEntryBuilder{}
                          .SetTableName("FIXED_TABLE")
                          .AddMatchField("field1", "123");
  EXPECT_EQ(app_db_entry.GetKey(), R"(FIXED_TABLE:{"match/field1":"123"})");
}

TEST(AppDbEntryBuilderTest, MultipleMatchField) {
  auto app_db_entry = AppDbEntryBuilder{}
                          .SetTableName("FIXED_TABLE")
                          .AddMatchField("field1", "123")
                          .AddMatchField("field2", "abc");
  EXPECT_EQ(app_db_entry.GetKey(),
            R"(FIXED_TABLE:{"match/field1":"123","match/field2":"abc"})");
}

TEST(AppDbEntryBuilderTest, OnlyPriorityMatchField) {
  auto app_db_entry =
      AppDbEntryBuilder{}.SetTableName("FIXED_TABLE").SetPriority(123);
  EXPECT_EQ(app_db_entry.GetKey(), R"(FIXED_TABLE:{"priority":123})");
}

TEST(AppDbEntryBuilderTest, MatchFieldsWithPriority) {
  auto app_db_entry = AppDbEntryBuilder{}
                          .SetTableName("FIXED_TABLE")
                          .SetPriority(123)
                          .AddMatchField("field1", "abc");
  EXPECT_EQ(app_db_entry.GetKey(),
            R"(FIXED_TABLE:{"match/field1":"abc","priority":123})");
}

TEST(AppDbEntryBuilderTest, NoActionParameters) {
  auto app_db_entry = AppDbEntryBuilder{}.SetAction("do_something");
  EXPECT_THAT(app_db_entry.GetValueList(), ContainerEq(ActionValues{
                                               {"action", "do_something"},
                                           }));
}

TEST(AppDbEntryBuilderTest, SingleActionParameter) {
  auto app_db_entry = AppDbEntryBuilder{}
                          .SetAction("do_something")
                          .AddActionParam("arg1", "ce-1/2");
  EXPECT_THAT(app_db_entry.GetValueList(), ContainerEq(ActionValues{
                                               {"action", "do_something"},
                                               {"param/arg1", "ce-1/2"},
                                           }));
}

TEST(AppDbEntryBuilderTest, MultipleActionParameters) {
  auto app_db_entry = AppDbEntryBuilder{}
                          .SetAction("do_something")
                          .AddActionParam("arg1", "ce-1/2")
                          .AddActionParam("arg2", "10.0.0.1");
  EXPECT_THAT(app_db_entry.GetValueList(), ContainerEq(ActionValues{
                                               {"action", "do_something"},
                                               {"param/arg1", "ce-1/2"},
                                               {"param/arg2", "10.0.0.1"},
                                           }));
}

}  // namespace
}  // namespace test_lib
}  // namespace p4rt_app
