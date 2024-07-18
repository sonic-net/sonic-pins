#include "thinkit/bazel_test_environment.h"

#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"

namespace thinkit {
namespace {

constexpr absl::string_view kTestArtifact = "my_test_artifact.txt";

class BazelTestEnvironmentTest : public testing::Test {
 protected:
  std::unique_ptr<TestEnvironment> environment_ =
      absl::make_unique<BazelTestEnvironment>(/*mask_known_failures=*/true);
};

TEST_F(BazelTestEnvironmentTest, StoreTestArtifact) {
  EXPECT_OK(environment_->StoreTestArtifact(kTestArtifact, "Hello, World!\n"));
  EXPECT_OK(environment_->StoreTestArtifact(kTestArtifact, "Hello, Test!\n"));
}

TEST_F(BazelTestEnvironmentTest, AppendToTestArtifact) {
  EXPECT_OK(
      environment_->AppendToTestArtifact(kTestArtifact, "Hello, World!\n"));
  EXPECT_OK(
      environment_->AppendToTestArtifact(kTestArtifact, "Hello, Test!\n"));
}

}  // namespace
}  // namespace thinkit
