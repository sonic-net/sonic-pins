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
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "gutil/status.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace gutil {

namespace internal {

template <class Status> const Status &GetStatus(const Status &status) {
  return status;
}

template <class T>
const absl::Status &GetStatus(const absl::StatusOr<T> &statusor) {
  return statusor.status();
}

} // namespace internal

MATCHER(IsOk, negation ? "is not OK" : "is OK") {
  return internal::GetStatus(arg).ok();
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
#define ASSERT_OK_AND_ASSIGN(lhs, expression)                                  \
  auto __ASSIGN_OR_RETURN_VAL(__LINE__) = expression;                          \
  if (!__ASSIGN_OR_RETURN_VAL(__LINE__).status().ok()) {                       \
    FAIL() << #expression                                                      \
           << " failed: " << __ASSIGN_OR_RETURN_VAL(__LINE__).status();        \
  }                                                                            \
  lhs = std::move(__ASSIGN_OR_RETURN_VAL(__LINE__)).value();

MATCHER_P(StatusIs, status_code,
          absl::StrCat(negation ? "is not " : "is ",
                       absl::StatusCodeToString(status_code))) {
  return internal::GetStatus(arg).code() == status_code;
}

MATCHER_P2(StatusIs, status_code, message_matcher,
           absl::StrFormat("is %s%s, %s has a status message that %s",
                           negation ? "not " : "",
                           absl::StatusCodeToString(status_code),
                           negation ? "or" : "and",
                           testing::DescribeMatcher<const std::string &>(
                               message_matcher, negation))) {
  const absl::Status &status = internal::GetStatus(arg);
  return status.code() == status_code &&
         testing::ExplainMatchResult(message_matcher, status.message(),
                                     result_listener);
}

template <class StatusOrT>
class IsOkAndHoldsMatcherImpl : public testing::MatcherInterface<StatusOrT> {
public:
  using T = typename std::remove_reference_t<StatusOrT>::value_type;

  template <class InnerMatcher>
  explicit IsOkAndHoldsMatcherImpl(InnerMatcher &&inner_matcher)
      : inner_matcher_(testing::SafeMatcherCast<T>(
            std::forward<InnerMatcher>(inner_matcher))) {}

  bool MatchAndExplain(StatusOrT t,
                       testing::MatchResultListener *listener) const override {
    if (!t.ok()) {
      *listener << "which has status " << t.status();
      return false;
    }
    return inner_matcher_.MatchAndExplain(*t, listener);
  }

  void DescribeTo(std::ostream *os) const override {
    *os << "is OK and has a value that ";
    inner_matcher_.DescribeTo(os);
  }
  void DescribeNegationTo(std::ostream *os) const override {
    *os << "is not OK or has a value that ";
    inner_matcher_.DescribeNegationTo(os);
  }

private:
  testing::Matcher<T> inner_matcher_;
};

template <class InnerMatcher> class IsOkAndHoldsMatcher {
public:
  explicit IsOkAndHoldsMatcher(InnerMatcher &&inner_matcher)
      : inner_matcher_(std::forward<InnerMatcher>(inner_matcher)) {}

  template <class StatusOrT>
  operator testing::Matcher<StatusOrT>() const { // NOLINT
    return testing::Matcher<StatusOrT>(
        new IsOkAndHoldsMatcherImpl<StatusOrT>(inner_matcher_));
  }

private:
  InnerMatcher inner_matcher_;
};

template <class InnerMatcher>
IsOkAndHoldsMatcher<InnerMatcher> IsOkAndHolds(InnerMatcher &&inner_matcher) {
  return IsOkAndHoldsMatcher<InnerMatcher>(
      std::forward<InnerMatcher>(inner_matcher));
}

} // namespace gutil

#endif // GUTIL_STATUS_MATCHERS_H
