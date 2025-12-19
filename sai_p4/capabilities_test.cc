#include "sai_p4/capabilities.h"

#include "absl/status/status.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status_matchers.h"
#include "sai_p4/capabilities.pb.h"

namespace sai {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::p4::v1::CapabilitiesResponse;

TEST(CapabilitiesTest, AddExperimentalResourceCapabilitiesWorks) {
  CapabilitiesResponse response;
  ExperimentalResourceCapabilities experimental_resource_capabilities;
  experimental_resource_capabilities.mutable_wcmp_group_limitations()
      ->set_max_distinct_weights_per_group(8);
  experimental_resource_capabilities.mutable_wcmp_group_limitations()
      ->set_max_total_weight_per_group(2000);

  EXPECT_OK(AddExperimentalResourceCapabilities(
      experimental_resource_capabilities, response));

  ExperimentalResourceCapabilities unpacked_experimental_resource_capabilities;
  response.mutable_experimental()->UnpackTo(
      &unpacked_experimental_resource_capabilities);
  EXPECT_THAT(unpacked_experimental_resource_capabilities,
              EqualsProto(experimental_resource_capabilities));
}

TEST(CapabilitiesTest, GetExperimentalResourceCapabilitiesWorks) {
  CapabilitiesResponse response;
  ExperimentalResourceCapabilities experimental_resource_capabilities;
  experimental_resource_capabilities.mutable_wcmp_group_limitations()
      ->set_max_distinct_weights_per_group(8);
  experimental_resource_capabilities.mutable_wcmp_group_limitations()
      ->set_max_total_weight_per_group(2000);

  ASSERT_OK(AddExperimentalResourceCapabilities(
      experimental_resource_capabilities, response));
  EXPECT_THAT(GetExperimentalResourceCapabilities(response),
              IsOkAndHolds(EqualsProto(experimental_resource_capabilities)));
}

TEST(CapabilitiesTest, GetExperimentalResourceCapabilitiesFailsWhenMissing) {
  EXPECT_THAT(GetExperimentalResourceCapabilities(CapabilitiesResponse()),
              gutil::StatusIs(absl::StatusCode::kNotFound));
}

TEST(CapabilitiesTest, GetWcmpGroupLimitationsWorks) {
  CapabilitiesResponse response;
  ExperimentalResourceCapabilities experimental_resource_capabilities;
  experimental_resource_capabilities.mutable_wcmp_group_limitations()
      ->set_max_distinct_weights_per_group(8);
  experimental_resource_capabilities.mutable_wcmp_group_limitations()
      ->set_max_total_weight_per_group(2000);

  ASSERT_OK(AddExperimentalResourceCapabilities(
      experimental_resource_capabilities, response));
  EXPECT_THAT(
      GetWcmpGroupLimitations(response),
      IsOkAndHolds(EqualsProto(
          experimental_resource_capabilities.wcmp_group_limitations())));
}

TEST(CapabilitiesTest, GetWcmpGroupLimitationsWorksWithDefaultValues) {
  CapabilitiesResponse response;
  ASSERT_OK(AddExperimentalResourceCapabilities(
      ExperimentalResourceCapabilities(), response));
  EXPECT_THAT(GetWcmpGroupLimitations(response),
              IsOkAndHolds(EqualsProto(WcmpGroupLimitations())));
}

TEST(CapabilitiesTest, GetWcmpGroupLimitationsFailsWhenParentMessageMissing) {
  EXPECT_THAT(GetWcmpGroupLimitations(CapabilitiesResponse()),
              gutil::StatusIs(absl::StatusCode::kNotFound));
}

}  // namespace
}  // namespace sai
