#include "p4rt_app/p4runtime/queue_translator.h"

#include "absl/strings/str_cat.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"

namespace p4rt_app {
namespace {
using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;

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

}  // namespace
}  // namespace p4rt_app
