#include "sai_p4/instantiations/google/sai_p4info_fetcher.h"

#include <string>
#include <vector>

#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/strings/str_replace.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "p4/config/v1/p4info.pb.h"
#include "sai_p4/instantiations/google/clos_stage.h"
#include "sai_p4/instantiations/google/instantiations.h"

namespace sai {
namespace {
using ::gutil::EqualsProto;
using ::testing::Gt;
using ::testing::Not;

class InstantiationTest : public testing::TestWithParam<Instantiation> {};
class InstantiationsWithoutStageTest : public InstantiationTest {};

std::string InstantiationTestName(
    const testing::TestParamInfo<Instantiation>& info) {
  return InstantiationToString(info.param);
}

absl::flat_hash_set<Instantiation> InstantiationsWithStage() {
  return {Instantiation::kMiddleblock, Instantiation::kFabricBorderRouter};
}

std::vector<Instantiation> InstantiationsWithoutStage() {
  std::vector<Instantiation> instantiations;
  for (const auto& stage : AllInstantiations()) {
    if (!InstantiationsWithStage().contains(stage)) {
      instantiations.push_back(stage);
    }
  }
  return instantiations;
}

TEST_P(InstantiationTest, BaseCaseReturnsP4Info) {
  EXPECT_THAT(FetchP4Info(GetParam()).ByteSizeLong(), Gt(0));
}

INSTANTIATE_TEST_SUITE_P(FetchP4InfoTest, InstantiationTest,
                         testing::ValuesIn(AllInstantiations()),
                         InstantiationTestName);

TEST_P(InstantiationsWithoutStageTest, IgnoresStage) {
  EXPECT_THAT(FetchP4Info(GetParam(), ClosStage::kStage2),
              EqualsProto(FetchP4Info(GetParam())));
  EXPECT_THAT(FetchP4Info(GetParam(), ClosStage::kStage3),
              EqualsProto(FetchP4Info(GetParam())));
}

INSTANTIATE_TEST_SUITE_P(FetchP4InfoTest, InstantiationsWithoutStageTest,
                         testing::ValuesIn(InstantiationsWithoutStage()),
                         InstantiationTestName);

TEST(FetchP4InfoTest, CanFetchUnionedP4Info) {
  EXPECT_THAT(FetchUnionedP4Info().ByteSizeLong(), Gt(0));
}

}  // namespace
}  // namespace sai
