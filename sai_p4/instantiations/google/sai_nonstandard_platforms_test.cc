#include "sai_p4/instantiations/google/sai_nonstandard_platforms.h"

#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "p4/config/v1/p4info.pb.h"
#include "sai_p4/instantiations/google/instantiations.h"

namespace sai {
namespace {

constexpr NonstandardPlatform kAllPlatforms[] = {
    NonstandardPlatform::kBmv2,
    NonstandardPlatform::kP4Symbolic,
};

// GetNonstandardP4Config contains a CHECK; ensure it doesn't fail.
TEST(GetNonstandardP4ConfigTest, DoesNotCheckCrashForAllPlatforms) {
  for (auto instantiation : AllInstantiations()) {
    for (auto platform : kAllPlatforms) {
      GetNonstandardP4Config(instantiation, platform);
    }
  }
}

// GetNonstandardP4Info contains a CHECK; ensure it doesn't fail.
TEST(GetNonstandardP4InfoTest, DoesNotCheckCrashForAllPlatforms) {
  for (auto instantiation : AllInstantiations()) {
    for (auto platform : kAllPlatforms) {
      GetNonstandardP4Info(instantiation, platform);
    }
  }
}

TEST(NonstandardPlatformsFlagTest, ParsingValidNameSucceeds) {
  NonstandardPlatform platform;
  std::string error;
  ASSERT_TRUE(AbslParseFlag("bmv2", &platform, &error));
  ASSERT_THAT(platform, testing::Eq(NonstandardPlatform::kBmv2));
}

TEST(NonstandardPlatformsFlagTest, ParsingInvalidNameFails) {
  NonstandardPlatform platform;
  std::string error;
  ASSERT_FALSE(AbslParseFlag("non-existing-platform-name", &platform, &error));
}

TEST(NonstandardPlatformsFlagTest, UnparsingWorks) {
  ASSERT_THAT(AbslUnparseFlag(NonstandardPlatform::kBmv2), testing::Eq("bmv2"));
}

}  // namespace
}  // namespace sai
