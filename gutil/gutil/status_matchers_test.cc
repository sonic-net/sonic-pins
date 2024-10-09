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
#include "gutil/gutil/status_matchers.h"

#include <string>

#include "absl/memory/memory.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status.h"

namespace gutil {
namespace {

using ::testing::_;
using ::testing::Eq;
using ::testing::HasSubstr;
using ::testing::Not;

TEST(AbseilStatusMatcher, IsOk) { EXPECT_THAT(absl::Status(), IsOk()); }

TEST(AbseilStatusMatcher, IsNotOk) {
  EXPECT_THAT(absl::UnknownError("unknown error"), Not(IsOk()));
}

TEST(AbseilStatusMatcher, StatusIs) {
  EXPECT_THAT(absl::UnknownError("unknown error"),
              StatusIs(absl::StatusCode::kUnknown));
}

TEST(AbseilStatusMatcher, StatusIsNot) {
  EXPECT_THAT(absl::UnknownError("unknown error"),
              Not(StatusIs(absl::StatusCode::kInvalidArgument)));
}

TEST(AbseilStatusMatcher, StatusIsWithMessage) {
  EXPECT_THAT(absl::UnknownError("unknown error"),
              StatusIs(absl::StatusCode::kUnknown, "unknown error"));
}

TEST(AbseilStatusMatcher, StatusIsWithMessageNot) {
  EXPECT_THAT(absl::UnknownError("unknown error"),
              Not(StatusIs(absl::StatusCode::kInvalidArgument, "unknown")));
}

TEST(AbslStatusOrMatcher, IsOk) { EXPECT_THAT(absl::StatusOr<int>(1), IsOk()); }

TEST(AbslStatusOrMatcher, IsNotOk) {
  EXPECT_THAT(absl::StatusOr<int>(absl::UnknownError("unknown error")),
              Not(IsOk()));
}

TEST(AbslStatusOrMatcher, StatusIs) {
  EXPECT_THAT(absl::StatusOr<int>(absl::UnknownError("unknown error")),
              StatusIs(absl::StatusCode::kUnknown));
}

TEST(AbslStatusOrMatcher, StatusIsNot) {
  EXPECT_THAT(absl::StatusOr<int>(absl::UnknownError("unknown error")),
              Not(StatusIs(absl::StatusCode::kInvalidArgument)));
}

TEST(AbslStatusOrMatcher, StatusIsWithMessage) {
  EXPECT_THAT(absl::StatusOr<int>(absl::UnknownError("unknown error")),
              StatusIs(absl::StatusCode::kUnknown, HasSubstr("unknown")));
}

TEST(AbslStatusOrMatcher, StatusIsWithMessageNot) {
  EXPECT_THAT(absl::StatusOr<int>(absl::UnknownError("unknown error")),
              Not(StatusIs(absl::StatusCode::kInvalidArgument, "unknown")));
}

TEST(AbslStatusOrMatcher, StatusIsOkAndHolds) {
  EXPECT_THAT(absl::StatusOr<int>(1320), IsOkAndHolds(1320));
}

TEST(AbslStatusOrMatcher, StatusIsNotOkAndHolds) {
  EXPECT_THAT(absl::StatusOr<int>(1320), Not(IsOkAndHolds(0)));
}

TEST(AbslStatusOrMatcher, StatusIsOkAndHoldsWithExpectation) {
  EXPECT_THAT(absl::StatusOr<std::string>("The quick brown fox"),
              IsOkAndHolds(HasSubstr("fox")));
}

// This test will fail to build if the macro doesn't work.
TEST(AbslStatusOrMatcher, AssignOrReturnWorksWithMoveOnlyTypes) {
  ASSERT_OK_AND_ASSIGN(
      auto value_from_expression,
      absl::StatusOr<std::unique_ptr<int>>(absl::make_unique<int>(0)));
}

TEST(IsOkAndHoldsTest, Description) {
  auto describe = [](const auto& matcher) {
    return testing::DescribeMatcher<absl::StatusOr<int>>(matcher);
  };
  EXPECT_EQ(describe(IsOkAndHolds(_)),
            "is OK and has a value that is anything");
  EXPECT_EQ(describe(Not(IsOkAndHolds(Eq(4)))),
            "is not OK or has a value that isn't equal to 4");
}

}  // namespace
}  // namespace gutil
