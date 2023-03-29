#include "gutil/testing.h"

#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace gutil {
namespace {

TEST(SnakeCaseToCamelCaseTest, WorksForSomeStandardInputs) {
  EXPECT_EQ(SnakeCaseToCamelCase("my_camel_case"), "MyCamelCase");
  EXPECT_EQ(SnakeCaseToCamelCase("word"), "Word");
  EXPECT_EQ(SnakeCaseToCamelCase("two_words"), "TwoWords");
  EXPECT_EQ(SnakeCaseToCamelCase("3_words"), "3Words");
  EXPECT_EQ(SnakeCaseToCamelCase("_my_camel_case_"), "MyCamelCase");
}

TEST(SnakeCaseToCamelCaseTest, LowerFirstWorks) {
  EXPECT_EQ(SnakeCaseToCamelCase("my_camel_case", /*lower_first=*/true),
            "myCamelCase");
  EXPECT_EQ(SnakeCaseToCamelCase("word", /*lower_first=*/true), "word");
  EXPECT_EQ(SnakeCaseToCamelCase("two_words", /*lower_first=*/true),
            "twoWords");
  EXPECT_EQ(SnakeCaseToCamelCase("3_words", /*lower_first=*/true), "3Words");
  EXPECT_EQ(SnakeCaseToCamelCase("_my_camel_case_", /*lower_first=*/true),
            "myCamelCase");
}

TEST(SnakeCaseToCamelCaseTest, WorksForWeirdInputs) {
  for (bool lower_first : {true, false}) {
    EXPECT_EQ(SnakeCaseToCamelCase("_with__extra_underlines_", lower_first),
              absl::StrCat(lower_first ? "w" : "W", "ithExtraUnderlines"));
    EXPECT_EQ(SnakeCaseToCamelCase("alreadyCamelCase", lower_first),
              absl::StrCat(lower_first ? "a" : "A", "lreadyCamelCase"));
    // Note that only the first letter after each '_' and the first letter
    // changes case.
    EXPECT_EQ(SnakeCaseToCamelCase("wEiRd_cASiNg", lower_first),
              absl::StrCat(lower_first ? "w" : "W", "EiRdCASiNg"));
    EXPECT_EQ(SnakeCaseToCamelCase("?weird_first_character", lower_first),
              "?weirdFirstCharacter");
    EXPECT_EQ(
        SnakeCaseToCamelCase("many_\nnon-letter..._char:acters", lower_first),
        absl::StrCat(lower_first ? "m" : "M", "any\nnon-letter...Char:acters"));
  }
}

}  // namespace
}  // namespace gutil
