#include "sai_p4/capabilities.h"

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status_matchers.h"  // IWYU pragma: keep
#include "sai_p4/capabilities.pb.h"

namespace sai {
namespace {

using ::gutil::EqualsProto;
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
              EqualsProto(experimental_resource_capabilities));
}

TEST(CapabilitiesTest,
     GetExperimentalResourceCapabilitiesReturnsEmptyWhenMissing) {
  EXPECT_THAT(GetExperimentalResourceCapabilities(CapabilitiesResponse()),
              EqualsProto(ExperimentalResourceCapabilities()));
}

TEST(CapabilitiesTest,
     GetExperimentalResourceCapabilitiesReturnsEmptyWhenWrongType) {
  CapabilitiesResponse response;
  p4::v1::TableEntry entry;
  ASSERT_TRUE(response.mutable_experimental()->PackFrom(entry));
  EXPECT_THAT(GetExperimentalResourceCapabilities(response),
              EqualsProto(ExperimentalResourceCapabilities()));
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
      EqualsProto(experimental_resource_capabilities.wcmp_group_limitations()));
}

TEST(CapabilitiesTest, GetWcmpGroupLimitationsWorksWhenMissing) {
  CapabilitiesResponse response;
  ASSERT_OK(AddExperimentalResourceCapabilities(
      ExperimentalResourceCapabilities(), response));
  EXPECT_THAT(GetWcmpGroupLimitations(response),
              EqualsProto(WcmpGroupLimitations()));
}

TEST(CapabilitiesTest,
     GetWcmpGroupLimitationsReturnsEmptyWhenParentWhenMissing) {
  EXPECT_THAT(GetWcmpGroupLimitations(CapabilitiesResponse()),
              EqualsProto(WcmpGroupLimitations()));
}

TEST(CapabilitiesTest, GetWcmpGroupLimitationsReturnsEmptyWhenWrongType) {
  CapabilitiesResponse response;
  p4::v1::TableEntry entry;
  ASSERT_TRUE(response.mutable_experimental()->PackFrom(entry));
  EXPECT_THAT(GetWcmpGroupLimitations(response),
              EqualsProto(WcmpGroupLimitations()));
}

}  // namespace
}  // namespace sai
