#include <optional>
#include <string>
#include <vector>

#include "absl/strings/str_cat.h"
#include "gtest/gtest.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_nonstandard_platforms.h"

namespace sai {

namespace {

struct TestParams {
  // The flavor of SAI P4 to be tested. The test should pass for all
  // instantiations.
  sai::Instantiation instantiation;
  // Whether the instantiation is preprocessed for BMv2.
  std::optional<NonstandardPlatform> nonstandard_platform;
};

std::vector<TestParams> GetTestParams() {
  std::vector<TestParams> params;
  for (const auto& instantiation : sai::AllInstantiations()) {
    for (bool processed_for_bmv2 : {false, true}) {
      auto test_params = TestParams{
          .instantiation = instantiation,
      };
      if (processed_for_bmv2) {
        test_params.nonstandard_platform = NonstandardPlatform::kBmv2;
      }
      params.emplace_back() = test_params;
    }
  }
  return params;
}

using PreprocessedSaiProgramsTest = ::testing::TestWithParam<TestParams>;

TEST_P(PreprocessedSaiProgramsTest, PreprocessedInstantiationIsAccessible) {
  std::string preprocessed_instantiation_file_path = absl::StrCat(
      "sai_p4/instantiations/google/",
      PreprocessedInstantiationFileName(
          GetParam().instantiation,
          /*nonstandard_platform=*/GetParam().nonstandard_platform));
  // Portable method to check that the file exists.
  struct stat buffer;
  EXPECT_EQ(0, stat(preprocessed_instantiation_file_path.c_str(), &buffer));
}

INSTANTIATE_TEST_SUITE_P(
    PreprocessedSaiProgramsTest, PreprocessedSaiProgramsTest,
    testing::ValuesIn(GetTestParams()), [](const auto& test) {
      return absl::StrFormat(
          "%v%s", test.param.instantiation,
          "_preprocessed_" +
              (test.param.nonstandard_platform.has_value()
                   ? PlatformName(test.param.nonstandard_platform.value())
                   : "standard"));
    });

}  // namespace

}  // namespace sai
