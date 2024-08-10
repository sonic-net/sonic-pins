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
#include "p4rt_app/event_monitoring/config_db_cpu_queue_table_event.h"

#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "p4rt_app/p4runtime/cpu_queue_translator.h"
#include "p4rt_app/p4runtime/mock_p4runtime_impl.h"
#include "swss/schema.h"

namespace p4rt_app {
namespace {

using ::gutil::StatusIs;

MATCHER_P2(BidirectionallyMaps, name, id,
           absl::Substitute(".NameToId($0) = $1 and .IdToName($1) = $0", name,
                            id)) {
  bool success = true;
  auto id_lookup = arg.NameToId(name);
  if (!id_lookup.ok()) {
    *result_listener << "arg.NameToId(" << name << ")" << " returned status "
                     << id_lookup.status();
    success = false;
  } else if (*id_lookup != id) {
    *result_listener << "arg.NameToId(" << name << ")"
                     << " returned unexpected ID " << *id_lookup;
    success = false;
  }
  auto name_lookup = arg.IdToName(id);
  if (!name_lookup.ok()) {
    *result_listener << "arg.IdToName(" << id << ")" << " returned status "
                     << name_lookup.status();
    success = false;
  } else if (*name_lookup != name) {
    *result_listener << "arg.IdToName(" << id << ")"
                     << " returned unexpected Name " << *name_lookup;
    success = false;
  }
  return success;
}

TEST(ConfigDbCpuQueueTableEventHandler, AddEventSetsP4RuntimeMap) {
  MockP4RuntimeImpl p4runtime;
  std::unique_ptr<CpuQueueTranslator> translator;
  EXPECT_CALL(p4runtime, SetCpuQueueTranslator)
      .WillOnce([&](std::unique_ptr<CpuQueueTranslator> t) {
        translator = std::move(t);
      });
  ConfigDbCpuQueueTableEventHandler handler(&p4runtime);
  ASSERT_OK(handler.HandleEvent(SET_COMMAND, "CPU",
                                {
                                    {"BE", "1"},
                                    {"AF1", "2"},
                                    {"AF2", "3"},
                                    {"AF3", "4"},
                                    {"AF4", "5"},
                                    {"NC1", "6"},
                                }));
  EXPECT_THAT(*translator, BidirectionallyMaps("BE", 1));
  EXPECT_THAT(*translator, BidirectionallyMaps("AF1", 2));
  EXPECT_THAT(*translator, BidirectionallyMaps("AF2", 3));
  EXPECT_THAT(*translator, BidirectionallyMaps("AF3", 4));
  EXPECT_THAT(*translator, BidirectionallyMaps("AF4", 5));
  EXPECT_THAT(*translator, BidirectionallyMaps("NC1", 6));
}

TEST(ConfigDbCpuQueueTableEventHandler, DeleteEventClearsP4RuntimeMap) {
  MockP4RuntimeImpl p4runtime;
  std::unique_ptr<CpuQueueTranslator> translator;
  EXPECT_CALL(p4runtime, SetCpuQueueTranslator)
      .WillRepeatedly([&](std::unique_ptr<CpuQueueTranslator> t) {
        translator = std::move(t);
      });
  ConfigDbCpuQueueTableEventHandler handler(&p4runtime);
  std::vector<std::pair<std::string, std::string>> db_values = {
      {"BE", "1"},  {"AF1", "2"}, {"AF2", "3"},
      {"AF3", "4"}, {"AF4", "5"}, {"NC1", "6"},
  };
  ASSERT_OK(handler.HandleEvent(SET_COMMAND, "CPU", db_values));

  ASSERT_OK(handler.HandleEvent(DEL_COMMAND, "CPU", db_values));

  for (const auto& [name, id_string] : db_values) {
    EXPECT_THAT(translator->NameToId(name),
                StatusIs(absl::StatusCode::kNotFound));
    int id;
    ASSERT_TRUE(absl::SimpleAtoi(id_string, &id));
    EXPECT_THAT(translator->IdToName(id),
                StatusIs(absl::StatusCode::kNotFound));
  }
}

TEST(ConfigDbCpuQueueTableEventHandler, AddEventReplacesP4RuntimeMap) {
  MockP4RuntimeImpl p4runtime;
  std::unique_ptr<CpuQueueTranslator> translator;
  EXPECT_CALL(p4runtime, SetCpuQueueTranslator)
      .WillRepeatedly([&](std::unique_ptr<CpuQueueTranslator> t) {
        translator = std::move(t);
      });
  ConfigDbCpuQueueTableEventHandler handler(&p4runtime);
  ASSERT_OK(handler.HandleEvent(SET_COMMAND, "CPU",
                                {
                                    {"BE", "1"},
                                    {"AF1", "2"},
                                    {"AF2", "3"},
                                    {"AF3", "4"},
                                    {"AF4", "5"},
                                    {"NC1", "6"},
                                }));
  ASSERT_OK(handler.HandleEvent(SET_COMMAND, "CPU",
                                {
                                    {"BE", "2"},
                                    {"AF1", "3"},
                                    {"AF2", "4"},
                                    {"AF3", "5"},
                                    {"AF4", "6"},
                                    {"NC2", "7"},
                                }));
  EXPECT_THAT(*translator, BidirectionallyMaps("BE", 2));
  EXPECT_THAT(*translator, BidirectionallyMaps("AF1", 3));
  EXPECT_THAT(*translator, BidirectionallyMaps("AF2", 4));
  EXPECT_THAT(*translator, BidirectionallyMaps("AF3", 5));
  EXPECT_THAT(*translator, BidirectionallyMaps("AF4", 6));
  EXPECT_THAT(*translator, BidirectionallyMaps("NC2", 7));
}

TEST(ConfigDbCpuQueueTableEventHandler, ReturnsFailureToCreateTranslator) {
  MockP4RuntimeImpl p4runtime;
  ConfigDbCpuQueueTableEventHandler handler(&p4runtime);
  EXPECT_THAT(
      handler.HandleEvent(SET_COMMAND, "CPU",
                          {
                              {"BE", "1"},
                              {"AF1", "2"},
                              {"AF2", "3"},
                              {"AF3", "4"},
                              {"AF4", "5"},
                              {"NC1", "1"},  // INVALID: Repeated Queue ID
                          }),
      StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(ConfigDbCpuQueueTableEventHandler, DoesNotReplaceWithFailedTranslator) {
  MockP4RuntimeImpl p4runtime;
  std::unique_ptr<CpuQueueTranslator> translator;
  EXPECT_CALL(p4runtime, SetCpuQueueTranslator)
      .WillRepeatedly([&](std::unique_ptr<CpuQueueTranslator> t) {
        translator = std::move(t);
      });
  ConfigDbCpuQueueTableEventHandler handler(&p4runtime);
  ASSERT_OK(handler.HandleEvent(SET_COMMAND, "CPU",
                                {
                                    {"AF1", "1"},
                                    {"AF2", "2"},
                                }));
  EXPECT_FALSE(
      handler
          .HandleEvent(SET_COMMAND, "CPU",
                       {
                           {"AF1", "1"},
                           {"AF2", "3"},
                           {"AF1", "2"},  // INVALID: Repeated Queue Name
                       })
          .ok());

  EXPECT_THAT(*translator, BidirectionallyMaps("AF1", 1));
  EXPECT_THAT(*translator, BidirectionallyMaps("AF2", 2));
}

}  // namespace
}  // namespace p4rt_app
