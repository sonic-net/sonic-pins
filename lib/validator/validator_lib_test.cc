#include "lib/validator/validator_lib.h"

#include "absl/status/status.h"
#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"

namespace pins_test {
namespace {

TEST(WaitForConditionTest, SucceedsInOneTry) {
  int call_count = 0;
  auto succeed = [&call_count](absl::Duration /*timeout*/) {
    ++call_count;
    return absl::OkStatus();
  };
  EXPECT_OK(WaitForCondition(succeed, absl::Milliseconds(1)));
  EXPECT_EQ(call_count, 1);
}

TEST(WaitForConditionTest, RunsAtLeastOnce) {
  auto succeed = [](absl::Duration /*timeout*/) { return absl::OkStatus(); };
  EXPECT_OK(WaitForCondition(succeed, absl::ZeroDuration()));
}

TEST(WaitForConditionTest, SucceedsOnNthTry) {
  int call_count = 0;
  auto past_deadline = [&call_count](absl::Duration /*timeout*/) {
    if (++call_count >= 5) return absl::OkStatus();
    return absl::InternalError("Failed");
  };
  EXPECT_OK(WaitForCondition(past_deadline, absl::Milliseconds(100)));
  EXPECT_EQ(call_count, 5);
}

TEST(WaitForConditionTest, FailsAfterDeadline) {
  auto fail = [](absl::Duration /*timeout*/) {
    return absl::InternalError("Failed");
  };
  constexpr absl::Duration kTimeout = absl::Milliseconds(10);

  absl::Time start = absl::Now();
  EXPECT_THAT(WaitForCondition(fail, kTimeout),
              gutil::StatusIs(absl::StatusCode::kDeadlineExceeded,
                              testing::HasSubstr("Failed")));
  EXPECT_GT(absl::Now() - start, kTimeout);
}

TEST(WaitForConditionTest, PassesParametersToCondition) {
  auto ok_if = [](bool condition, absl::Duration /*timeout*/) {
    return condition ? absl::OkStatus() : absl::InternalError("Failed");
  };
  EXPECT_OK(WaitForCondition(ok_if, absl::ZeroDuration(), true));
  EXPECT_FALSE(WaitForCondition(ok_if, absl::ZeroDuration(), false).ok());
}

TEST(WaitForConditionTest, WorksWithNonTimeoutCondition) {
  auto ok_if = [](bool condition) {
    return condition ? absl::OkStatus() : absl::InternalError("Failed");
  };
  EXPECT_OK(WaitForCondition(ok_if, absl::ZeroDuration(), true));
  EXPECT_FALSE(WaitForCondition(ok_if, absl::ZeroDuration(), false).ok());
}

MATCHER(IsStrictlyDescending, "") {
  for (int i = 1; i < arg.size(); ++i) {
    if (arg.at(i) >= arg.at(i - 1)) {
      return false;
    }
  }
  return true;
}

TEST(WaitForConditionTest, PassesTimeoutToCondition) {
  std::vector<absl::Duration> timeouts;
  auto record_timeout = [&timeouts](absl::Duration timeout) {
    timeouts.push_back(timeout);
    absl::SleepFor(absl::Milliseconds(1));
    return absl::InternalError("Failed");
  };
  EXPECT_FALSE(WaitForCondition(record_timeout, absl::Milliseconds(10)).ok());
  EXPECT_GT(timeouts.size(), 1);
  EXPECT_THAT(timeouts, IsStrictlyDescending());
}

}  // namespace
}  // namespace pins_test
