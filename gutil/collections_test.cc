#include "gutil/collections.h"

#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"

namespace gutil {
namespace {

using ::gutil::IsOk;
using ::gutil::IsOkAndHolds;
using ::testing::Eq;
using ::testing::IsNull;
using ::testing::Not;
using ::testing::Pointee;

TEST(FindOrDefault, ReturnsDefaultForEmptyMap) {
  absl::flat_hash_map<std::string, std::string> empty_map;
  EXPECT_THAT(FindOrDefault(empty_map, "key", "default"), Eq("default"));
}

TEST(FindOrDefault, ReturnsMappedValueForExistingKeyAndDefaultOtherwise) {
  absl::flat_hash_map<std::string, std::string> map = {{"key", "value"}};
  EXPECT_THAT(FindOrDefault(map, "key", "default"), Eq("value"));
  EXPECT_THAT(FindOrDefault(map, "other key", "default"), Eq("default"));
}

TEST(FindFunctions, CanLookUpStringsUsingStringViews) {
  // Non-const and const dictionaries use different code paths, so we test both.
  absl::flat_hash_map<std::string, std::string> mutable_map = {
      {"key", "value"}};
  const auto& immutable_map = mutable_map;
  constexpr absl::string_view kCorrectKey = "key";
  constexpr absl::string_view kIncorrectKey = "incorrect key";

  // FindOrStatus.
  EXPECT_THAT(FindOrStatus(mutable_map, kCorrectKey),
              IsOkAndHolds(Eq("value")));
  EXPECT_THAT(FindOrStatus(immutable_map, kCorrectKey),
              IsOkAndHolds(Eq("value")));
  EXPECT_THAT(FindOrStatus(mutable_map, kIncorrectKey).status(), Not(IsOk()));
  EXPECT_THAT(FindOrStatus(immutable_map, kIncorrectKey).status(), Not(IsOk()));

  // FindPtrOrStatus.
  EXPECT_THAT(FindPtrOrStatus(mutable_map, kCorrectKey),
              IsOkAndHolds(Pointee(Eq("value"))));
  EXPECT_THAT(FindPtrOrStatus(immutable_map, kCorrectKey),
              IsOkAndHolds(Pointee(Eq("value"))));
  EXPECT_THAT(FindPtrOrStatus(mutable_map, kIncorrectKey).status(),
              Not(IsOk()));
  EXPECT_THAT(FindPtrOrStatus(immutable_map, kIncorrectKey).status(),
              Not(IsOk()));

  // FindOrNull.
  EXPECT_THAT(FindOrNull(mutable_map, kCorrectKey), Pointee(Eq("value")));
  EXPECT_THAT(FindOrNull(immutable_map, kCorrectKey), Pointee(Eq("value")));
  EXPECT_THAT(FindOrNull(mutable_map, kIncorrectKey), IsNull());
  EXPECT_THAT(FindOrNull(immutable_map, kIncorrectKey), IsNull());

  // FindOrDie.
  EXPECT_THAT(FindOrDie(mutable_map, kCorrectKey), Eq("value"));
  EXPECT_THAT(FindOrDie(immutable_map, kCorrectKey), Eq("value"));
  // Skip death tests.

  // FindOrDefault.
  const std::string kDefault = "default";
  EXPECT_THAT(FindOrDefault(mutable_map, kCorrectKey, kDefault), Eq("value"));
  EXPECT_THAT(FindOrDefault(immutable_map, kCorrectKey, kDefault), Eq("value"));
  EXPECT_THAT(FindOrDefault(mutable_map, kIncorrectKey, kDefault),
              Eq(kDefault));
  EXPECT_THAT(FindOrDefault(immutable_map, kIncorrectKey, kDefault),
              Eq(kDefault));
}

}  // namespace
}  // namespace gutil
