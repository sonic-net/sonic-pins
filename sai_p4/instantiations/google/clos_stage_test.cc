#include "sai_p4/instantiations/google/clos_stage.h"

#include <optional>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "sai_p4/instantiations/google/instantiations.h"

namespace sai {
namespace {

using ClosStageTest = testing::TestWithParam<sai::Instantiation>;

// Ensure that DiffersByClosStage correctly corresponds to
// AssertInstantiationAndClosStageAreCompatible.
TEST_P(ClosStageTest, DiffersByClosStateCapturesClosStageCompatibility) {
  if (DiffersByClosStage(GetParam())) {
    EXPECT_OK(AssertInstantiationAndClosStageAreCompatible(GetParam(),
                                                           ClosStage::kStage2));
  } else {
    EXPECT_OK(AssertInstantiationAndClosStageAreCompatible(
        GetParam(), /*stage=*/std::nullopt));
  }
}

// Checks that any instantiation that differs by stage is compatible with all
// stages or none.
// Note that this could in theory eventually not be true.
TEST_P(ClosStageTest, InstantationEitherSupportsAllStagesOrNone) {
  for (const sai::ClosStage stage : sai::AllStages()) {
    // Either an instantiation should be compatible with all stages, or no
    // stage, but not both.
    EXPECT_NE(
        AssertInstantiationAndClosStageAreCompatible(GetParam(), stage),
        AssertInstantiationAndClosStageAreCompatible(GetParam(), std::nullopt));
  }
}

INSTANTIATE_TEST_SUITE_P(
    ClosStageTestForAllInstantiations, ClosStageTest,
    testing::ValuesIn(sai::AllInstantiations()),
    [](const testing::TestParamInfo<sai::Instantiation>& info) {
      return gutil::SnakeCaseToCamelCase(
          sai::InstantiationToString(info.param));
    });

using ClosStageFlagTestWithParam = testing::TestWithParam<ClosStage>;

TEST_P(ClosStageFlagTestWithParam, ParsingUnparsedStageYieldsTheSameStage) {
  std::string unparsed_stage = AbslUnparseFlag(GetParam());
  ClosStage parsed_stage;
  std::string error;
  bool success = AbslParseFlag(unparsed_stage, &parsed_stage, &error);
  ASSERT_TRUE(success);
  ASSERT_EQ(parsed_stage, GetParam());
  ASSERT_EQ(error, "");
}

INSTANTIATE_TEST_SUITE_P(ClosStageFlagTestForAllStages,
                         ClosStageFlagTestWithParam,
                         testing::ValuesIn(AllStages()));

TEST(CloseStageFlagTest, ParsingIncorrectFlagYieldsError) {
  ClosStage parsed_stage;
  std::string error;
  bool success = AbslParseFlag("DummyStage", &parsed_stage, &error);
  ASSERT_FALSE(success);
  ASSERT_THAT(error, testing::Not(testing::IsEmpty()));
}

}  // namespace
}  // namespace sai
