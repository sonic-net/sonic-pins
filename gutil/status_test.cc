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

#include "absl/status/status.h"

#include <stdint.h>

#include <string>
#include <tuple>
#include <vector>

#include "gtest/gtest.h"
#include "gutil/status.h"
#include "util/task/error_space.h"
#include "util/task/status_builder.h"

namespace gutil {

absl::Status ReturnStatusWithAnnotatedStream(std::string status_message,
                                             std::string streamed_message,
                                             bool is_google3) {
  if (is_google3) {
    return util::StatusBuilder(absl::InvalidArgumentError(status_message))
           << streamed_message;
  } else {
    return gutil::StatusBuilder(absl::InvalidArgumentError(status_message))
           << streamed_message;
  }
}

absl::Status ReturnStatusWithPrependedStream(std::string status_message,
                                             std::string streamed_message,
                                             bool is_google3) {
  if (is_google3) {
    return util::StatusBuilder(absl::InvalidArgumentError(status_message))
               .SetPrepend()
           << streamed_message;
  } else {
    return gutil::StatusBuilder(absl::InvalidArgumentError(status_message))
               .SetPrepend()
           << streamed_message;
  }
}

absl::Status ReturnStatusWithAppendedStream(std::string status_message,
                                            std::string streamed_message,
                                            bool is_google3) {
  if (is_google3) {
    return util::StatusBuilder(absl::InvalidArgumentError(status_message))
               .SetAppend()
           << streamed_message;
  } else {
    return gutil::StatusBuilder(absl::InvalidArgumentError(status_message))
               .SetAppend()
           << streamed_message;
  }
}

absl::Status ReturnStatusWithOverriddenError(std::string status_message,
                                             std::string streamed_message,
                                             absl::StatusCode code,
                                             bool is_google3) {
  if (is_google3) {
    return util::StatusBuilder(absl::InvalidArgumentError(status_message))
               .SetCode(code)
           << streamed_message;
  } else {
    return gutil::StatusBuilder(absl::InvalidArgumentError(status_message))
               .SetCode(code)
           << streamed_message;
  }
}

TEST(StatusTest, TestPrependMessage) {
  std::string status_message = "Original message";
  std::string streamed_message = "Prepended message";
  // TODO: Investigate if these tests can be parameterized
  const auto gutil_status = ReturnStatusWithPrependedStream(
      status_message, streamed_message, /*is_google3=*/false);
  EXPECT_EQ(gutil_status.message(),
            absl::StrCat(streamed_message, status_message));
  const auto util_status = ReturnStatusWithPrependedStream(
      status_message, streamed_message, /*is_google3=*/true);
  EXPECT_EQ(gutil_status, util_status);
}

TEST(StatusTest, TestAppendMessage) {
  std::string status_message = "Original message";
  std::string streamed_message = "Appended message";
  const auto gutil_status = ReturnStatusWithAppendedStream(
      status_message, streamed_message, /*is_google3=*/false);
  EXPECT_EQ(gutil_status.message(),
            absl::StrCat(status_message, streamed_message));
  const auto util_status = ReturnStatusWithAppendedStream(
      status_message, streamed_message, /*is_google3=*/true);
  EXPECT_EQ(gutil_status, util_status);
}

TEST(StatusTest, TestAnnotateMessage) {
  std::string status_message = "Original message";
  std::string streamed_message = "Annotated message";
  const auto gutil_status = ReturnStatusWithAnnotatedStream(
      status_message, streamed_message, /*is_google3=*/false);
  EXPECT_EQ(gutil_status.message(),
            absl::StrCat(status_message, "; ", streamed_message));
  const auto util_status = ReturnStatusWithAnnotatedStream(
      status_message, streamed_message, /*is_google3=*/true);
  EXPECT_EQ(gutil_status, util_status);
}

TEST(StatusTest, TestSetError) {
  std::string status_message = "Original message";
  std::string streamed_message = "Annotated message";
  absl::StatusCode code = absl::StatusCode::kCancelled;
  const auto gutil_status = ReturnStatusWithOverriddenError(
      status_message, streamed_message, code, /*is_google3=*/false);
  EXPECT_EQ(gutil_status.message(),
            absl::StrCat(status_message, "; ", streamed_message));
  EXPECT_EQ(gutil_status.code(), code);
  const auto util_status = ReturnStatusWithOverriddenError(
      status_message, streamed_message, code, /*is_google3=*/true);
  EXPECT_EQ(gutil_status, util_status);
}

TEST(StatusTest, TestEmptyStream) {
  std::string status_message = "Original message";
  std::string streamed_message = "";
  const auto gutil_status = ReturnStatusWithAnnotatedStream(
      status_message, streamed_message, /*is_google3=*/false);
  EXPECT_EQ(gutil_status.message(), status_message);
  const auto util_status = ReturnStatusWithAnnotatedStream(
      status_message, streamed_message, /*is_google3=*/true);
  EXPECT_EQ(gutil_status, util_status);
}

TEST(StatusTest, TestEmptyStatusMessage) {
  std::string status_message = "";
  std::string streamed_message = "Appended message";
  const auto gutil_status = ReturnStatusWithAnnotatedStream(
      status_message, streamed_message, /*is_google3=*/false);
  EXPECT_EQ(gutil_status.message(), streamed_message);
  const auto util_status = ReturnStatusWithAnnotatedStream(
      status_message, streamed_message, /*is_google3=*/true);
  EXPECT_EQ(gutil_status, util_status);
}

}  // namespace gutil
