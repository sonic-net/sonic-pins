#include "gutil/collections.h"

#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace gutil {
namespace {

using ::testing::Eq;

TEST(FindOrDefault, ReturnsDefaultForEmptyMap) {
  absl::flat_hash_map<std::string, std::string> empty_map;
  EXPECT_THAT(FindOrDefault(empty_map, "key", "default"), Eq("default"));
}

TEST(FindOrDefault, ReturnsMappedValueForExistingKeyAndDefaultOtherwise) {
  absl::flat_hash_map<std::string, std::string> map = {{"key", "value"}};
  EXPECT_THAT(FindOrDefault(map, "key", "default"), Eq("value"));
  EXPECT_THAT(FindOrDefault(map, "other key", "default"), Eq("default"));
}

}  // namespace
}  // namespace gutil
