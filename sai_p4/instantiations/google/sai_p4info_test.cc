#include "sai_p4/instantiations/google/sai_p4info.h"

#include "absl/strings/match.h"
#include "absl/strings/str_replace.h"
#include "absl/strings/string_view.h"
#include "absl/types/optional.h"
#include "absl/types/variant.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_constraints/backend/constraint_info.h"
#include "sai_p4/instantiations/google/instantiations.h"

namespace sai {
namespace {

class InstantiationTest : public testing::TestWithParam<Instantiation> {};

TEST_P(InstantiationTest, GetP4InfoDoesNotCrashAndP4ConstraintsAreParsable) {
  // GetP4Info contains a CHECK; ensure it doesn't fail.
  auto info = GetP4Info(GetParam());
  ASSERT_OK_AND_ASSIGN(p4_constraints::ConstraintInfo constraint_info,
                       p4_constraints::P4ToConstraintInfo(info));
}

// GetIrP4Info contains a CHECK; ensure it doesn't fail.
TEST_P(InstantiationTest, GetIrP4InfoDoesNotCrash) {
  auto info = GetIrP4Info(GetParam());
  for (const auto& [name, table] : info.tables_by_name()) {
    EXPECT_NE(table.role(), "")
        << "Table '" << name << "' is missing a @p4runtime_role annotation.";
  }
}

TEST_P(InstantiationTest, GetP4InfoWithHashSeedReplacesHashSeed) {
  constexpr uint32_t kHashSeed = 1966175594;
  std::string p4info = GetP4Info(GetParam()).ShortDebugString();
  absl::StrReplaceAll({{"@sai_hash_seed(0)", "@sai_hash_seed(1966175594)"}},
                      &p4info);
  EXPECT_THAT(GetP4InfoWithHashSeed(GetParam(), kHashSeed),
              gutil::EqualsProto(p4info));
}

INSTANTIATE_TEST_SUITE_P(
    P4InfoTest, InstantiationTest, testing::ValuesIn(AllInstantiations()),
    [&](const testing::TestParamInfo<Instantiation>& info) {
      return InstantiationToString(info.param);
    });

TEST(GetUnionedP4InfoTest, DoesNotCrashTest) { GetUnionedP4Info(); }

}  // namespace
}  // namespace sai
