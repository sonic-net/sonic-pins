// Copyright (c) 2024, Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "lib/validator/validator_lib.h"

#include "absl/status/status.h"
#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"

namespace pins_test {
namespace {

using ::gutil::StatusIs;
using ::testing::MockFunction;

TEST(WaitForConditionTest, SucceedsInOneTry) {
  int call_count = 0;
  auto succeed = [&call_count] {
    ++call_count;
    return absl::OkStatus();
  };
  EXPECT_OK(WaitForCondition(succeed, absl::Milliseconds(1)));
  EXPECT_EQ(call_count, 1);
}

TEST(WaitForConditionTest, RunsAtLeastOnce) {
  auto succeed = [] { return absl::OkStatus(); };
  EXPECT_OK(WaitForCondition(succeed, absl::ZeroDuration()));
}

TEST(WaitForConditionTest, SucceedsOnNthTry) {
  int call_count = 0;
  auto past_deadline = [&call_count] {
    if (++call_count >= 5) return absl::OkStatus();
    return absl::InternalError("Failed");
  };
  EXPECT_OK(WaitForCondition(past_deadline, absl::Milliseconds(100)));
  EXPECT_EQ(call_count, 5);
}

TEST(WaitForConditionTest, FailsAfterDeadline) {
  auto fail = [] { return absl::InternalError("Failed"); };
  constexpr absl::Duration kTimeout = absl::Milliseconds(10);

  absl::Time start = absl::Now();
  EXPECT_THAT(WaitForCondition(fail, kTimeout),
              gutil::StatusIs(absl::StatusCode::kDeadlineExceeded,
                              testing::HasSubstr("Failed")));
  EXPECT_GT(absl::Now() - start, kTimeout);
}

TEST(WaitForConditionTest, PassesParametersToCondition) {
  auto ok_if = [](bool condition) {
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

TEST(WaitForConditionTest, NotWorks) {
  int call_count = 0;
  auto succeed = [&call_count](absl::string_view) {
    ++call_count;
    return call_count < 5 ? absl::OkStatus() : absl::InternalError("Failed");
  };
  EXPECT_OK(WaitForNot(succeed, absl::Milliseconds(1), ""));
  EXPECT_EQ(call_count, 5);
}

TEST(OnFailureTest, DoesntRunOnSuccess) {
  MockFunction<void()> mock_function;
  EXPECT_CALL(mock_function, Call()).Times(0);
  EXPECT_OK(OnFailure(absl::OkStatus(), mock_function.AsStdFunction()));
}

TEST(OnFailureTest, RunsOnFailure) {
  MockFunction<void()> mock_function;
  EXPECT_CALL(mock_function, Call()).Times(1);
  EXPECT_THAT(
      OnFailure(absl::InternalError("Failed"), mock_function.AsStdFunction()),
      StatusIs(absl::StatusCode::kInternal));
}

}  // namespace
}  // namespace pins_test
