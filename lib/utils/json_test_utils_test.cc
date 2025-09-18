// Copyright 2025 Google LLC
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
#include "lib/utils/json_test_utils.h"

#include <sstream>
#include <string_view>

#include "absl/strings/strip.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace pins_test {
namespace {

using ::testing::HasSubstr;

// The output of MatchAndExplain() starts with this prefix when there is an
// error before the actual differenece as JSON.
constexpr std::string_view kErrorPrefix = "Difference:";

TEST(JsonTestUtilsTest, ActualIsntParseable) {
  std::ostringstream out;
  JsonIsMatcher matcher(R"json({})json");
  EXPECT_FALSE(matcher.MatchAndExplain(R"json({"something"})json", &out));
  EXPECT_THAT(out.str(), HasSubstr("Failed to parse JSON"));
}

TEST(JsonTestUtilsTest, SuccessWithDifferentFormatting) {
  JsonIsMatcher matcher(R"json({"something":0})json");
  EXPECT_TRUE(matcher.MatchAndExplain(
      R"json({
        "something": 0
      })json",
      /*os=*/nullptr));
}

TEST(JsonTestUtilsTest, FailsWithDifference) {
  std::ostringstream out;
  JsonIsMatcher matcher(R"json({"something":0,"other":1})json");
  EXPECT_FALSE(matcher.MatchAndExplain(R"json({"something": 0})json", &out));
  // Since the actual value is missing "other", it should be detected as a
  // "remove" operation.
  EXPECT_THAT(absl::StripPrefix(out.str(), kErrorPrefix),
              JsonIs(R"json([{"op": "remove", "path": "/other"}])json"));
}

TEST(JsonTestUtilsTest, WorksWithNoOstream) {
  JsonIsMatcher matcher(R"json({"something":0,"other":1})json");
  EXPECT_FALSE(matcher.MatchAndExplain(R"json({"something": 0})json",
                                       /*os=*/nullptr));
}

TEST(JsonTestUtilsTest, ExpectEmptySuccess) {
  JsonIsMatcher matcher(R"json({})json");
  EXPECT_TRUE(matcher.MatchAndExplain(R"json({})json", /*os=*/nullptr));
}

TEST(JsonTestUtilsTest, ExpectEmptyFails) {
  std::ostringstream out;
  JsonIsMatcher matcher(R"json({})json");
  EXPECT_FALSE(matcher.MatchAndExplain(R"json({"something": 0})json", &out));
  EXPECT_THAT(absl::StripPrefix(out.str(), kErrorPrefix),
              JsonIs(R"json([{"op": "add",
                              "path": "/something",
                              "value": 0}])json"));
}

TEST(JsonTestUtilsTest, DifferentFieldOrderingIsOkay) {
  JsonIsMatcher matcher(R"json({"something": 0, "other": 1})json");
  EXPECT_TRUE(matcher.MatchAndExplain(R"json({"other": 1,"something": 0})json",
                                      /*os=*/nullptr));
}

TEST(JsonTestUtilsDeathTest, ExpectedFailsToParse) {
  EXPECT_ANY_THROW(JsonIsMatcher(R"json({"something"})json"));
}

TEST(JsonTestUtilsTest, Describe) {
  std::ostringstream out;
  JsonIsMatcher matcher(R"json({"something": 0})json");
  matcher.DescribeTo(&out);
  EXPECT_EQ(out.str(), R"(Equal to:
{
  "something": 0
})");
}

TEST(JsonTestUtilsTest, DescribeNegation) {
  std::ostringstream out;
  JsonIsMatcher matcher(R"json({"something": 0})json");
  matcher.DescribeNegationTo(&out);
  EXPECT_EQ(out.str(), R"(Not equal to:
{
  "something": 0
})");
}

}  // namespace
}  // namespace pins_test
