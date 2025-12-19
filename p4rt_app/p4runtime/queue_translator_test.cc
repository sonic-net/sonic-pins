#include "p4rt_app/p4runtime/queue_translator.h"

#include <string>

#include "absl/strings/str_cat.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"

namespace p4rt_app {
namespace {
using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::testing::HasSubstr;

// Succeeds if the translator has both translations:
//   IdToName(id) == name
//   NameToId(name) == id
MATCHER_P2(HasBidirectionalTranslation, id, name,
           absl::StrCat("Translates Queue ID '", absl::StrCat(id),
                        "' to Queue Name '", name, "' and vice versa")) {
  bool success = true;

  auto name_lookup = arg.IdToName(id);
  if (!name_lookup.ok()) {
    *result_listener << "\nIdToName(" << id
                     << ") translation failed: " << name_lookup.status();
    success = false;
  } else if (*name_lookup != name) {
    *result_listener << "\nIdToName(" << id
                     << ") translation returned the wrong queue name: "
                     << *name_lookup;
    success = false;
  }

  auto id_lookup = arg.NameToId(name);
  if (!id_lookup.ok()) {
    *result_listener << "\nNameToId(\"" << name
                     << "\") translation failed: " << id_lookup.status();
    success = false;
  } else if (*id_lookup != id) {
    *result_listener << "\nNameToId(\"" << name
                     << "\") translation returned the wrong queue ID: "
                     << *id_lookup;
    success = false;
  }
  return success;
}

MATCHER_P(LacksIdToNameTranslation, id,
          absl::StrCat("IdToName(", id, ") returns NOT_FOUND")) {
  auto id_to_name = arg.IdToName(id);
  if (id_to_name.ok()) {
    *result_listener << "\nIdToName(" << id << ") succeeded with queue name '"
                     << *id_to_name << "'";
    return false;
  }
  if (id_to_name.status().code() != absl::StatusCode::kNotFound) {
    *result_listener << "\nIdToName(" << id
                     << ") returned unexpected status: " << id_to_name.status();
    return false;
  }
  return true;
}

MATCHER_P(LacksNameToIdTranslation, name,
          absl::StrCat("NameToId(", name, ") returns NOT_FOUND")) {
  auto name_to_id = arg.NameToId(name);
  if (name_to_id.ok()) {
    *result_listener << "\nNameToId(" << name << ") succeeded with queue name '"
                     << *name_to_id << "'";
    return false;
  }
  if (name_to_id.status().code() != absl::StatusCode::kNotFound) {
    *result_listener << "\nNameToId(" << name
                     << ") returned unexpected status: " << name_to_id.status();
    return false;
  }
  return true;
}

TEST(QueueTranslator, CreateFailsForNonIntegerId) {
  EXPECT_THAT(QueueTranslator::Create({{"a", "1.2"}}),
              StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_THAT(QueueTranslator::Create({
                  {"b", "1.2"},
              }),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(QueueTranslator, CreateFailsForRepeatedQueueName) {
  EXPECT_THAT(QueueTranslator::Create({
                  {"a", "1"},
                  {"a", "3"},
              }),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(QueueTranslator, CreateFailsForRepeatedQueueId) {
  EXPECT_THAT(QueueTranslator::Create({
                  {"b", "2"},
                  {"c", "2"},
              }),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(QueueTranslator, CreateFailsWhenSomeValuesAreInvalid) {
  EXPECT_THAT(QueueTranslator::Create({
                  {"a", "1"},
                  {"b", "2.2"},
                  {"c", "3"},
                  {"d", "4"},
              }),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(QueueTranslator, MissingTranslationReturnsNotFoundError) {
  auto empty = QueueTranslator::Empty();
  EXPECT_THAT(empty->IdToName(1), StatusIs(absl::StatusCode::kNotFound));
  EXPECT_THAT(empty->NameToId("a"), StatusIs(absl::StatusCode::kNotFound));
}

TEST(QueueTranslator, CanTranslateIdToName) {
  ASSERT_OK_AND_ASSIGN(auto translator, QueueTranslator::Create({
                                            {"a", "1"},
                                            {"b", "2"},
                                            {"c", "3"},
                                        }));
  EXPECT_THAT(translator->IdToName(1), IsOkAndHolds("a"));
  EXPECT_THAT(translator->IdToName(2), IsOkAndHolds("b"));
  EXPECT_THAT(translator->IdToName(3), IsOkAndHolds("c"));
}

TEST(QueueTranslator, CanTranslateNameToId) {
  ASSERT_OK_AND_ASSIGN(auto translator, QueueTranslator::Create({
                                            {"a", "1"},
                                            {"b", "2"},
                                            {"c", "3"},
                                        }));
  EXPECT_THAT(translator->NameToId("a"), IsOkAndHolds(1));
  EXPECT_THAT(translator->NameToId("b"), IsOkAndHolds(2));
  EXPECT_THAT(translator->NameToId("c"), IsOkAndHolds(3));
}

TEST(QueueTranslator, OptionallyTranslateIdToName) {
  ASSERT_OK_AND_ASSIGN(auto translator, QueueTranslator::Create({
                                            {"a", "1"},
                                            {"c", "3"},
                                            {"d", "11"},
                                        }));

  EXPECT_THAT(translator->OptionallyTranslateIdToName("1"), IsOkAndHolds("a"));
  EXPECT_THAT(translator->OptionallyTranslateIdToName("3"), IsOkAndHolds("c"));
  EXPECT_THAT(translator->OptionallyTranslateIdToName("11"),
              IsOkAndHolds("11"));
  EXPECT_THAT(translator->OptionallyTranslateIdToName("0xb"),
              IsOkAndHolds("d"));
  EXPECT_THAT(translator->OptionallyTranslateIdToName("0"), IsOkAndHolds("0"));
  EXPECT_THAT(translator->OptionallyTranslateIdToName("0x3"),
              IsOkAndHolds("c"));
  EXPECT_THAT(translator->OptionallyTranslateIdToName("a"), IsOkAndHolds("a"));
}

TEST(QueueTranslator, OptionallyTranslateNameToIdInHexString) {
  ASSERT_OK_AND_ASSIGN(auto translator, QueueTranslator::Create({
                                            {"a", "1"},
                                            {"c", "3"},
                                        }));
  EXPECT_EQ(translator->OptionallyTranslateNameToIdInHexString("a"), "0x1");
  EXPECT_EQ(translator->OptionallyTranslateNameToIdInHexString("c"), "0x3");
  EXPECT_EQ(translator->OptionallyTranslateNameToIdInHexString("0x3"), "0x3");
  // TODO: Accept queue number in non-hex-string format for now.
  EXPECT_EQ(translator->OptionallyTranslateNameToIdInHexString("3"), "0x3");
  EXPECT_EQ(translator->OptionallyTranslateNameToIdInHexString("0"), "0");
}

TEST(QueueTranslator, DebugDataMatches) {
  ASSERT_OK_AND_ASSIGN(auto translator, QueueTranslator::Create({
                                            {"a", "1"},
                                            {"b", "2"},
                                            {"c", "3"},
                                        }));
  std::string dump = translator->DumpDebugData();
  EXPECT_THAT(dump, HasSubstr("a : 1\n"));
  EXPECT_THAT(dump, HasSubstr("b : 2\n"));
  EXPECT_THAT(dump, HasSubstr("c : 3\n"));
}

}  // namespace
}  // namespace p4rt_app
