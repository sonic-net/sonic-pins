// Copyright 2024 Google LLC
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

#include "gutil/version.h"

#include "absl/status/status.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"

namespace gutil {
namespace {
using gutil::IsOkAndHolds;
using testing::Eq;

bool RoundTrips(const Version& version) {
  absl::StatusOr<Version> roundtripped_version =
      ParseVersion(VersionToString(version));
  return roundtripped_version.ok() && *roundtripped_version == version;
}

TEST(ParseVersionTest, PositiveExamples) {
  EXPECT_THAT(ParseVersion("1.2.3"), IsOkAndHolds(Eq(Version{1, 2, 3})));
  EXPECT_THAT(ParseVersion("01.2.3"), IsOkAndHolds(Eq(Version{1, 2, 3})));
  EXPECT_THAT(ParseVersion("255.512.1024"),
              IsOkAndHolds(Eq(Version{255, 512, 1024})));
}

TEST(ParseVersionTest, NegativeExamples) {
  EXPECT_THAT(ParseVersion("100"),
              gutil::StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_THAT(ParseVersion("1.1"),
              gutil::StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_THAT(ParseVersion("1.1.1."),
              gutil::StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_THAT(ParseVersion("1.1.1.1"),
              gutil::StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_THAT(ParseVersion("1.1.1,0"),
              gutil::StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_THAT(ParseVersion("hello"),
              gutil::StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(VersionTest, VersionToStringAndParseVersionRoundTrip) {
  EXPECT_TRUE(RoundTrips(Version{1, 2, 3}));
  EXPECT_TRUE(RoundTrips(Version{0, 2, 0}));
  EXPECT_TRUE(RoundTrips(Version{1024, 987654321, 0}));
}

TEST(ComparisonTest, OrderingIsLexicographic) {
  EXPECT_GT((Version{1, 0, 1}), (Version{1, 0, 0}));
  EXPECT_GT((Version{1, 1, 1}), (Version{1, 0, 1}));
  EXPECT_GT((Version{2, 0, 0}), (Version{1, 255, 255}));
  EXPECT_GT((Version{0, 1, 0}), (Version{0, 0, 255}));
  EXPECT_GT((Version{10, 0, 0}), (Version{2, 0, 0}));
}

}  // namespace
}  // namespace gutil
