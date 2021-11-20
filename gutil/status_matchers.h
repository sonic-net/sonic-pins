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

#ifndef GUTIL_STATUS_MATCHERS_H
#define GUTIL_STATUS_MATCHERS_H

#include <ostream>
#include <string>
#include <type_traits>
#include <utility>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status.h"

namespace absl {

// Overload the absl::StatusOr insertion operator to output its status. This
// makes it so test matchers output the status instead of byte strings.
//
// NOTE: the insertion operator must be in the same namespace as the object for
// the matching framework to work correctly.
template <typename T>
std::ostream& operator<<(std::ostream& out, const StatusOr<T>& status_or) {
  return out << status_or.status();
}

}  // namespace absl

namespace gutil {

// Implements a status matcher interface to verify a status variable is okay.
//
// Sample usage:
//   EXPECT_THAT(MyCall, IsOk());
//   EXPECT_OK(MyCall());
//
// Sample output on failure:
//   Value of: MyCall()
//   Expected: is Ok.
//     Actual: UNKNOWN: descriptive error (of type absl::lts_2020_02_25::Status)
class StatusIsOkMatcher {
 public:
  void DescribeTo(std::ostream* os) const { *os << "is OK"; }
  void DescribeNegationTo(std::ostream* os) const { *os << "is not OK"; }

  template <typename StatusType>
  bool MatchAndExplain(const StatusType& actual,
                       testing::MatchResultListener* /*listener*/) const {
    return actual.ok();
  }
};

// Status matcher that confirms the status is okay.
inline testing::PolymorphicMatcher<StatusIsOkMatcher> IsOk() {
  return testing::MakePolymorphicMatcher(StatusIsOkMatcher());
}

// Convenience macros for checking that a status return type is okay.
#define EXPECT_OK(expression) EXPECT_THAT(expression, ::gutil::IsOk())
#define ASSERT_OK(expression) ASSERT_THAT(expression, ::gutil::IsOk())

#ifndef __ASSIGN_OR_RETURN_VAL_DIRECT
#define __ASSIGN_OR_RETURN_VAL_DIRECT(arg) __ASSIGN_OR_RETURN_RESULT_##arg
#define __ASSIGN_OR_RETURN_VAL(arg) __ASSIGN_OR_RETURN_VAL_DIRECT(arg)
#endif

// ASSERT_OK_AND_ASSIGN evaluates the expression (which needs to evaluate to a
// StatusOr) and asserts that the expression has status OK. It then assigns the
// result to lhs, and otherwise fails.
#define ASSERT_OK_AND_ASSIGN(lhs, expression)                           \
  auto __ASSIGN_OR_RETURN_VAL(__LINE__) = expression;                   \
  if (!__ASSIGN_OR_RETURN_VAL(__LINE__).status().ok()) {                \
    FAIL() << #expression                                               \
           << " failed: " << __ASSIGN_OR_RETURN_VAL(__LINE__).status(); \
  }                                                                     \
  lhs = std::move(__ASSIGN_OR_RETURN_VAL(__LINE__)).value();

namespace internal {

inline const absl::Status& GetStatus(const absl::Status& status) {
  return status;
}

template <typename T>
const absl::Status& GetStatus(const absl::StatusOr<T>& status) {
  return status.status();
}

}  // namespace internal

// Implements a status matcher interface to verify a status error code, and
// error message if set, matches an expected value.
//
// Sample usage:
//   EXPECT_THAT(MyCall(), StatusIs(absl::StatusCode::kNotFound,
//                                  HasSubstr("message")));
//
// Sample output on failure:
//   Value of: MyCall()
//   Expected: NOT_FOUND and has substring "message"
//     Actual: UNKNOWN: descriptive error (of type absl::lts_2020_02_25::Status)
class StatusIsMatcher {
 public:
  StatusIsMatcher(const absl::StatusCode& status_code,
                  const testing::Matcher<const std::string&>& message_matcher)
      : status_code_(status_code), message_matcher_(message_matcher) {}

  void DescribeTo(std::ostream* os) const {
    *os << status_code_ << " status code where the message ";
    message_matcher_.DescribeTo(os);
  }

  void DescribeNegationTo(std::ostream* os) const {
    *os << "not (";
    DescribeTo(os);
    *os << ")";
  }

  template <typename StatusType>
  bool MatchAndExplain(const StatusType& actual,
                       testing::MatchResultListener* listener) const {
    const absl::Status& actual_status = internal::GetStatus(actual);
    return actual_status.code() == status_code_ &&
           message_matcher_.MatchAndExplain(
               std::string{actual_status.message()}, listener);
  }

 private:
  const absl::StatusCode status_code_;
  const testing::Matcher<const std::string&> message_matcher_;
};

// Status matcher that checks the StatusCode for an expected value.
inline testing::PolymorphicMatcher<StatusIsMatcher> StatusIs(
    const absl::StatusCode& code) {
  return testing::MakePolymorphicMatcher(StatusIsMatcher(code, testing::_));
}

// Status matcher that checks the StatusCode and message for expected values.
template <typename MessageMatcher>
testing::PolymorphicMatcher<StatusIsMatcher> StatusIs(
    const absl::StatusCode& code, const MessageMatcher& message) {
  return testing::MakePolymorphicMatcher(
      StatusIsMatcher(code, testing::MatcherCast<const std::string&>(message)));
}

// Implements a status_or matcher interface to verify a status_or value is
// successfully set, and equal to an expected value.
//
// Sample usage:
//   EXPECT_THAT(MyCall(), IsOkAndHolds(1));
//
// Sample output on failure:
//   Value of: MyCall()
//   Expected: is OK and holds 1
//     Actual: OK (of type absl::StatusOr<int>)
MATCHER_P(IsOkAndHolds, value, "") {
  if (!arg.ok()) {
    return false;
  }

  *result_listener << "with value: " << testing::PrintToString(*arg);
  auto matcher = testing::MatcherCast<
      typename std::remove_reference<decltype(arg)>::type::value_type>(value);
  return ExplainMatchResult(matcher, arg.value(), result_listener);
}

}  // namespace gutil

#endif  // GUTIL_STATUS_MATCHERS_H
