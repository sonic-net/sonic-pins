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

#include "p4_infra/p4_pdpi/utils/annotation_parser.h"

#include <map>
#include <set>
#include <string>
#include <tuple>
#include <type_traits>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status_matchers.h"

namespace pdpi {
namespace annotation {
namespace {

using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::testing::ElementsAre;
using ::testing::IsEmpty;

template <typename T>
std::set<typename T::key_type> Keys(T map_container) {
  std::set<typename T::key_type> keys;
  for (const auto& pair : map_container) {
    keys.insert(pair.first);
  }
  return keys;
}

// === Status Matchers ===

// Mock parser to ensure parsing is not invoked.
absl::StatusOr<int> ExpectNoParsing(std::string) {
  ADD_FAILURE() << "Parser is not expected to be called.";
  return 0;
}

// Matcher for struct AnnotationComponents.
MATCHER_P2(AnnotationComponentsAre, label, body, "") {
  auto label_matcher = testing::MatcherCast<std::string>(label);
  auto body_matcher = testing::MatcherCast<std::string>(body);
  if (testing::Matches(label_matcher)(arg.label) &&
      testing::Matches(body_matcher)(arg.body)) {
    return true;
  }
  *result_listener << "Expected AnnotationComponents whose label matches ";
  label_matcher.DescribeTo(result_listener->stream());
  *result_listener << "and whose body matches ";
  body_matcher.DescribeTo(result_listener->stream());
  return false;
}

// === Tests ===

TEST(GetAllAnnotations, ReturnsLabelBodyAnnotations) {
  EXPECT_THAT(GetAllAnnotations(std::vector<std::string>(
                  {"@label(body)", "@l2(b2)", "@l3(b3)"})),
              ElementsAre(AnnotationComponentsAre("label", "body"),
                          AnnotationComponentsAre("l2", "b2"),
                          AnnotationComponentsAre("l3", "b3")));
}

TEST(GetParsedAnnotation, EmptyAnnotationListReturnsNotFound) {
  std::vector<std::string> empty;
  EXPECT_THAT(GetParsedAnnotation<int>("label", empty, ExpectNoParsing),
              StatusIs(absl::StatusCode::kNotFound));
}

TEST(GetParsedAnnotation, MultipleMatchingAnnotationsReturnsError) {
  EXPECT_THAT(
      GetAnnotationAsArgList(
          "label", std::vector<std::string>(
                       {"@a(b)", "@b(a)", "@label(arg)", "@label(arg2)"})),
      StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(GetAllParsedAnnotations, EmptyAnnotationListReturnsEmptyList) {
  std::vector<std::string> empty;
  EXPECT_THAT(GetAllParsedAnnotations<int>("label", empty, ExpectNoParsing),
              IsOkAndHolds(IsEmpty()));
}

TEST(GetAllParsedAnnotations, ReturnsAllMatchingAnnotations) {
  EXPECT_THAT(GetAllAnnotationsAsArgList(
                  "label", std::vector<std::string>(
                               {"@a(b)", "@b(a)", "@label(arg)",
                                "@label(arg1, arg2)", "@c(c)", "@label()"})),
              IsOkAndHolds(ElementsAre(
                  ElementsAre("arg"), ElementsAre("arg1", "arg2"), IsEmpty())));
}

// This class of tests ensures uniform response of unexpected annotation forms.
// This differs from the previous tests, which test expected but non-matching
// annotations.
class NonMatchingAnnotationTest : public testing::TestWithParam<std::string> {
 public:
  // Returns a static map of annotation test name to annotation string.
  static const std::map<std::string, std::string>& TestCases() {
    static const auto* const test_cases =
        new std::map<std::string, std::string>({
            {"EmptyLabel", "@"},
            {"EmptyLabelWithEmptyBody", "@()"},
            {"EmptyLabelWithBody", "@(arg)"},
            {"NonMatchingLabel", "@a()"},
            {"SuperstringLabel", "@labela()"},
            {"SubstringLabel", "@labe()"},
            {"MissingAt", "label()"},
            {"SpaceBetweenAtAndLabel", "@ label()"},
            {"MissingOpenParenthesis", "@label)"},
            {"MissingClosedParenthesis", "@label(arg"},
        });
    return *test_cases;
  }
};

TEST_P(NonMatchingAnnotationTest, ParseAnnotationReturnsError) {
  // GetAllAnnotations doesn't require a particular label, so some cases do not
  // apply.
  if (GetParam() == "NonMatchingLabel" || GetParam() == "SuperstringLabel" ||
      GetParam() == "SubstringLabel") {
    GTEST_SKIP() << "GetAllAnnotations does not perform label matching.";
  } else {
    EXPECT_FALSE(ParseAnnotation(TestCases().at(GetParam())).ok());
  }
}

TEST_P(NonMatchingAnnotationTest, GetAllAnnotationsReturnsEmpty) {
  // GetAllAnnotations doesn't require a particular label, so some cases do not
  // apply.
  if (GetParam() == "NonMatchingLabel" || GetParam() == "SuperstringLabel" ||
      GetParam() == "SubstringLabel") {
    GTEST_SKIP() << "GetAllAnnotations does not perform label matching.";
  } else {
    EXPECT_THAT(GetAllAnnotations(
                    std::vector<std::string>({TestCases().at(GetParam())})),
                IsEmpty());
  }
}

TEST_P(NonMatchingAnnotationTest, GetAnnotationReturnsNotFound) {
  EXPECT_THAT(
      GetParsedAnnotation<int>(
          "label", std::vector<std::string>({TestCases().at(GetParam())}),
          ExpectNoParsing),
      StatusIs(absl::StatusCode::kNotFound));
}

TEST_P(NonMatchingAnnotationTest, GetAllParsedAnnotationsReturnsEmptyList) {
  EXPECT_THAT(
      GetAllParsedAnnotations<int>(
          "label", std::vector<std::string>({TestCases().at(GetParam())}),
          ExpectNoParsing),
      IsOkAndHolds(IsEmpty()));
}

TEST_P(NonMatchingAnnotationTest, GetParsedAnnotationSkipsAnnotation) {
  EXPECT_THAT(GetAnnotationAsArgList(
                  "label", std::vector<std::string>(
                               {TestCases().at(GetParam()), "@label(arg)"})),
              IsOkAndHolds(ElementsAre("arg")));
}

TEST_P(NonMatchingAnnotationTest, GetAllParsedAnnotationsSkipsAnnotation) {
  EXPECT_THAT(GetAllAnnotationsAsArgList(
                  "label", std::vector<std::string>(
                               {TestCases().at(GetParam()), "@label(arg)"})),
              IsOkAndHolds(ElementsAre(ElementsAre("arg"))));
}

INSTANTIATE_TEST_SUITE_P(
    NonMatchingAnnotation, NonMatchingAnnotationTest,
    testing::ValuesIn(Keys(NonMatchingAnnotationTest::TestCases())),
    [](const testing::TestParamInfo<NonMatchingAnnotationTest::ParamType>&
           info) { return info.param; });

TEST(GetParsedAnnotation, ReturnsParserError) {
  auto parser = [](std::string) -> absl::StatusOr<int> {
    return absl::Status(absl::StatusCode::kUnknown, "ErrorMessage");
  };
  EXPECT_THAT(
      GetParsedAnnotation<int>("label", std::vector<std::string>({"@label()"}),
                               parser),
      StatusIs(absl::StatusCode::kUnknown, testing::HasSubstr("ErrorMessage")));
}

TEST(GetAllParsedAnnotations, ReturnsParserError) {
  auto parser = [](std::string) -> absl::StatusOr<int> {
    return absl::Status(absl::StatusCode::kUnknown, "ErrorMessage");
  };
  EXPECT_THAT(
      GetAllParsedAnnotations<int>(
          "label", std::vector<std::string>({"@label()"}), parser),
      StatusIs(absl::StatusCode::kUnknown, testing::HasSubstr("ErrorMessage")));
}

TEST(GetAllAnnotations, CapturesAllCharactersWithinParentheses) {
  EXPECT_THAT(
      GetAllAnnotations(std::vector<std::string>({"@label(*aBxC[]()\"\")"})),
      ElementsAre(AnnotationComponentsAre("label", "*aBxC[]()\"\"")));
}

TEST(GetParsedAnnotation, CapturesAllCharactersWithinParentheses) {
  EXPECT_THAT(GetAnnotationBody(
                  "label", std::vector<std::string>({"@label(*aBxC[]()\"\")"})),
              IsOkAndHolds("*aBxC[]()\"\""));
}

TEST(GetAllParsedAnnotations, CapturesAllCharactersWithinParentheses) {
  EXPECT_THAT(GetAllAnnotationBodies(
                  "label", std::vector<std::string>({"@label(*aBxC[]()\"\")"})),
              IsOkAndHolds(ElementsAre("*aBxC[]()\"\"")));
}

TEST(GetAllAnnotations, CapturesAllWhitespace) {
  EXPECT_THAT(GetAllAnnotations(std::vector<std::string>({"@label(  )"})),
              ElementsAre(AnnotationComponentsAre("label", "  ")));
}

TEST(GetParsedAnnotation, CapturesAllWhitespace) {
  EXPECT_THAT(
      GetAnnotationBody("label", std::vector<std::string>({"@label(  )"})),
      IsOkAndHolds("  "));
}

TEST(GetAllParsedAnnotations, CapturesAllWhitespace) {
  EXPECT_THAT(
      GetAllAnnotationBodies("label", std::vector<std::string>({"@label(  )"})),
      IsOkAndHolds(ElementsAre("  ")));
}

TEST(GetAllAnnotations, ReturnsLabelOnlyAnnotation) {
  EXPECT_THAT(GetAllAnnotations(std::vector<std::string>({"@label"})),
              ElementsAre(AnnotationComponentsAre("label", "")));
}

TEST(GetParsedAnnotation, ReturnsLabelOnlyAnnotation) {
  EXPECT_THAT(GetAnnotationBody("label", std::vector<std::string>({"@label"})),
              IsOkAndHolds(""));
}

TEST(GetAllParsedAnnotations, ReturnsLabelOnlyAnnotation) {
  EXPECT_THAT(GetAllAnnotationBodies(
                  "label", std::vector<std::string>({"@label", "@label"})),
              IsOkAndHolds(ElementsAre("", "")));
}

class LabelValueWhitespaceTest : public testing::TestWithParam<std::string> {
 public:
  static const std::map<std::string, std::string>& TestCases() {
    static const auto* const cases = new std::map<std::string, std::string>({
        {"PrefixSpace", " @label(arg)"},
        {"SuffixSpace", "@label(arg) "},
        {"InnerSpace", "@label (arg)"},
        {"AllSpace", " @label (arg) "},
        {"PrefixTab", "\t@label(arg)"},
        {"SuffixTab", "@label(arg)\t"},
        {"InnerTab", "@label\t(arg)"},
        {"AllTab", "\t@label\t(arg)\t"},
    });
    return *cases;
  }
};

TEST_P(LabelValueWhitespaceTest, GetAllAnnotationsIgnoresWhitespace) {
  EXPECT_THAT(
      GetAllAnnotations(std::vector<std::string>({TestCases().at(GetParam())})),
      ElementsAre(AnnotationComponentsAre("label", "arg")))
      << "Annotations {" << TestCases().at(GetParam()) << "}";
}

TEST_P(LabelValueWhitespaceTest, GetParsedAnnotationIgnoresWhitespace) {
  EXPECT_THAT(GetAnnotationBody("label", std::vector<std::string>(
                                             {TestCases().at(GetParam())})),
              IsOkAndHolds("arg"))
      << "Annotations {" << TestCases().at(GetParam()) << "}";
}

TEST_P(LabelValueWhitespaceTest, GetAllParsedAnnotationsIgnoresWhitespace) {
  EXPECT_THAT(
      GetAllAnnotationBodies(
          "label", std::vector<std::string>({TestCases().at(GetParam())})),
      IsOkAndHolds(ElementsAre("arg")))
      << "Annotations {" << TestCases().at(GetParam()) << "}";
}

INSTANTIATE_TEST_SUITE_P(
    LabelValueWhitespace, LabelValueWhitespaceTest,
    testing::ValuesIn(Keys(LabelValueWhitespaceTest::TestCases())),
    [](const testing::TestParamInfo<std::string>& info) { return info.param; });

class LabelOnlyWhitespaceTest : public testing::TestWithParam<std::string> {
 public:
  static const std::map<std::string, std::string>& TestCases() {
    static const auto* const cases = new std::map<std::string, std::string>({
        {"PrefixSpace", " @label"},
        {"SuffixSpace", "@label "},
        {"PrefixTab", "\t@label"},
        {"SuffixTab", "@label\t"},
    });
    return *cases;
  }
};

TEST_P(LabelOnlyWhitespaceTest, GetAnnotationIgnoresWhitespace) {
  EXPECT_THAT(GetAnnotationBody("label", std::vector<std::string>(
                                             {TestCases().at(GetParam())})),
              IsOkAndHolds(""))
      << "Annotations {" << TestCases().at(GetParam()) << "}";
}

TEST_P(LabelOnlyWhitespaceTest, GetAllAnnotationsIgnoresWhitespace) {
  EXPECT_THAT(
      GetAllAnnotationBodies(
          "label", std::vector<std::string>({TestCases().at(GetParam())})),
      IsOkAndHolds(ElementsAre("")))
      << "Annotations {" << TestCases().at(GetParam()) << "}";
}

INSTANTIATE_TEST_SUITE_P(
    LabelOnlyWhitespace, LabelOnlyWhitespaceTest,
    testing::ValuesIn(Keys(LabelOnlyWhitespaceTest::TestCases())),
    [](const testing::TestParamInfo<std::string>& info) { return info.param; });

// === ParseAsArgList tests ===
enum class WhitespaceCase {
  kNone,
  kLeftSpace,
  kRightSpace,
  kBothSpace,
  kLeftTab,
  kRightTab,
  kBothTab
};

constexpr WhitespaceCase kAllWhitespaceCases[] = {
    WhitespaceCase::kNone,       WhitespaceCase::kLeftSpace,
    WhitespaceCase::kRightSpace, WhitespaceCase::kBothSpace,
    WhitespaceCase::kLeftTab,    WhitespaceCase::kRightTab,
    WhitespaceCase::kBothTab};

std::string WhitespaceCaseName(WhitespaceCase whitespace) {
  switch (whitespace) {
    case WhitespaceCase::kNone:
      return "None";
    case WhitespaceCase::kLeftSpace:
      return "LeftSpace";
    case WhitespaceCase::kRightSpace:
      return "RightSpace";
    case WhitespaceCase::kBothSpace:
      return "BothSpace";
    case WhitespaceCase::kLeftTab:
      return "LeftTab";
    case WhitespaceCase::kRightTab:
      return "RightTab";
    case WhitespaceCase::kBothTab:
      return "BothTab";
  }
  ADD_FAILURE() << "Unsupported whitespace case.";
  return "";
}

std::string AddWhitespace(absl::string_view base, WhitespaceCase whitespace) {
  switch (whitespace) {
    case WhitespaceCase::kNone:
      return std::string(base);
    case WhitespaceCase::kLeftSpace:
      return absl::StrCat("  ", base);
    case WhitespaceCase::kRightSpace:
      return absl::StrCat(base, " ");
    case WhitespaceCase::kBothSpace:
      return absl::StrCat(" ", base, "  ");
    case WhitespaceCase::kLeftTab:
      return absl::StrCat("\t\t", base);
    case WhitespaceCase::kRightTab:
      return absl::StrCat(base, "\t");
    case WhitespaceCase::kBothTab:
      return absl::StrCat("\t", base, "\t\t");
  }
  ADD_FAILURE() << "Unsupported whitespace case.";
  return "";
}

class ParseAsArgListTest : public testing::TestWithParam<WhitespaceCase> {};

TEST_P(ParseAsArgListTest, ParsesSingleArgument) {
  EXPECT_THAT(ParseAsArgList(AddWhitespace("arg", GetParam())),
              IsOkAndHolds(ElementsAre("arg")));
}

TEST_P(ParseAsArgListTest, ParsesTwoArguments) {
  std::vector<std::string> args = {AddWhitespace("arg1", GetParam()),
                                   AddWhitespace("arg2", GetParam())};
  EXPECT_THAT(ParseAsArgList(absl::StrJoin(args, ",")),
              IsOkAndHolds(ElementsAre("arg1", "arg2")));
}

TEST_P(ParseAsArgListTest, ParsesThreeArguments) {
  std::vector<std::string> args = {AddWhitespace("arg1", GetParam()),
                                   AddWhitespace("arg2", GetParam()),
                                   AddWhitespace("arg3", GetParam())};
  EXPECT_THAT(ParseAsArgList(absl::StrJoin(args, ",")),
              IsOkAndHolds(ElementsAre("arg1", "arg2", "arg3")));
}

TEST_P(ParseAsArgListTest, ParsesArgumentsInOrder) {
  // Use reverse alphabetical order to ensure ordering is left-to-right.
  std::vector<std::string> args = {AddWhitespace("arg3", GetParam()),
                                   AddWhitespace("arg2", GetParam()),
                                   AddWhitespace("arg1", GetParam())};
  EXPECT_THAT(ParseAsArgList(absl::StrJoin(args, ",")),
              IsOkAndHolds(ElementsAre("arg3", "arg2", "arg1")));
}

INSTANTIATE_TEST_SUITE_P(
    ParseAsArgList, ParseAsArgListTest, testing::ValuesIn(kAllWhitespaceCases),
    [](const testing::TestParamInfo<ParseAsArgListTest::ParamType>& info) {
      return absl::StrCat("Whitespace", WhitespaceCaseName(info.param));
    });

TEST(ParseAsArgList, EmptyValueReturnsEmptyList) {
  EXPECT_THAT(ParseAsArgList(""), IsOkAndHolds(IsEmpty()));
}

TEST(ParseAsArgList, WhitespaceValueReturnsEmptyList) {
  EXPECT_THAT(ParseAsArgList("    "), IsOkAndHolds(IsEmpty()));
}

TEST(ParseAsArgList, RemovesSpaceWithinArgument) {
  EXPECT_THAT(ParseAsArgList("a b, b c,c d "),
              IsOkAndHolds(ElementsAre("ab", "bc", "cd")));
}

TEST(ParseAsArgList, RemovesTabWithinArgument) {
  EXPECT_THAT(ParseAsArgList("a\tb,\tb\tc,c\td\t"),
              IsOkAndHolds(ElementsAre("ab", "bc", "cd")));
}

TEST(ParseAsArgList, PreservesSpacesWithinQuotes) {
  EXPECT_THAT(ParseAsArgList("  \"  a\t \"  "),
              IsOkAndHolds(ElementsAre("\"  a\t \"")));
}

TEST(ParseAsArgList, ConsecutiveCommasReturnEmptyValues) {
  EXPECT_THAT(ParseAsArgList(",,  , ,\t,"),
              IsOkAndHolds(ElementsAre("", "", "", "", "", "")));
}

TEST(ParseAsArgList, TokenizesParentheses) {
  EXPECT_THAT(ParseAsArgList("(,),(a,)"),
              IsOkAndHolds(ElementsAre("(,)", "(a,)")));
}

TEST(ParseAsArgList, TokenizesBraces) {
  EXPECT_THAT(ParseAsArgList("{,},{a,}"),
              IsOkAndHolds(ElementsAre("{,}", "{a,}")));
}

TEST(ParseAsArgList, TokenizesBrackets) {
  EXPECT_THAT(ParseAsArgList("[,],[a,]"),
              IsOkAndHolds(ElementsAre("[,]", "[a,]")));
}

TEST(ParseAsArgList, TokenizesQuotes) {
  EXPECT_THAT(ParseAsArgList("\",\",\"a,\""),
              IsOkAndHolds(ElementsAre("\",\"", "\"a,\"")));
}

TEST(ParseAsArgList, HandlesNestedScope) {
  EXPECT_THAT(ParseAsArgList("([({(a,b,d),e},f), g], h), a"),
              IsOkAndHolds(ElementsAre("([({(a,b,d),e},f),g],h)", "a")));
}

TEST(ParseAsArgList, TreatsQuotesAsLiterals) {
  EXPECT_THAT(ParseAsArgList("\"[({\", a\"])}\""),
              IsOkAndHolds(ElementsAre("\"[({\"", "a\"])}\"")));
}

constexpr char kUnpairedCharacterCases[] = {'(', ')', '{', '}', '[', ']', '\"'};

std::string UnpairedCharacterCasesName(char c) {
  switch (c) {
    case '(':
      return "OpenParenthesis";
    case ')':
      return "CloseParenthesis";
    case '[':
      return "OpenBracket";
    case ']':
      return "CloseBracket";
    case '{':
      return "OpenBrace";
    case '}':
      return "CloseBrace";
    case '\"':
      return "Quote";
    default:
      break;
  }
  ADD_FAILURE() << "Unsupported unpaired character case: " << c;
  return "";
}

class UnpairedCharacterTest : public testing::TestWithParam<char> {};

TEST_P(UnpairedCharacterTest, ReturnsInvalidArgument) {
  EXPECT_THAT(ParseAsArgList(std::string(1, GetParam())),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_P(UnpairedCharacterTest, ReturnsInvalidArgumentWithinNest) {
  EXPECT_THAT(
      ParseAsArgList(absl::StrCat("(", std::string(1, GetParam()), ")")),
      StatusIs(absl::StatusCode::kInvalidArgument));
}

INSTANTIATE_TEST_SUITE_P(
    ParseAsArgList, UnpairedCharacterTest,
    testing::ValuesIn(kUnpairedCharacterCases),
    [](const testing::TestParamInfo<UnpairedCharacterTest::ParamType>& info) {
      return UnpairedCharacterCasesName(info.param);
    });

}  // namespace
}  // namespace annotation
}  // namespace pdpi
