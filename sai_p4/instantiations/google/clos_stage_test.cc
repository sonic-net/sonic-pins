#include "sai_p4/instantiations/google/clos_stage.h"

#include <optional>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "sai_p4/instantiations/google/instantiations.h"

namespace sai {
namespace {

using ::gutil::StatusIs;

// Checks that any instantiation that differs by stage is compatible with all
// stages.
// Note that this could in theory eventually not be true.
TEST(InstantiationAndStageCompatibility, DiffersByStageImpliesCompatible) {
  EXPECT_OK(AssertInstantiationAndClosStageAreCompatible(
      Instantiation::kMiddleblock, ClosStage::kStage2));
  EXPECT_THAT(AssertInstantiationAndClosStageAreCompatible(
                  Instantiation::kFabricBorderRouter, /*stage=*/std::nullopt),
              StatusIs(absl::StatusCode::kInvalidArgument));

  EXPECT_OK(AssertInstantiationAndClosStageAreCompatible(
      Instantiation::kWbb, /*stage=*/std::nullopt));
  EXPECT_THAT(AssertInstantiationAndClosStageAreCompatible(Instantiation::kWbb,
                                                           ClosStage::kStage3),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

}  // namespace
}  // namespace sai
