// Copyright 2021 Google LLC
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

#include "sai_p4/tools/p4info_tools.h"

#include <cstdint>

#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/testing.h"
#include "p4/config/v1/p4info.pb.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/minimum_guaranteed_sizes.h"
#include "sai_p4/instantiations/google/sai_p4info.h"

namespace sai {
namespace {

using ::gutil::EqualsProto;
using ::gutil::Partially;

p4::config::v1::Action ActionWithHashSeed(uint32_t action_id,
                                          uint32_t hash_seed) {
  constexpr absl::string_view kTemplate = R"pb(
    preamble {
      id: $0
      name: "ingress.hashing.select_ecmp_hash_algorithm_$0"
      alias: "select_ecmp_hash_algorithm_$0"
      annotations: "@sai_hash_algorithm(SAI_HASH_ALGORITHM_CRC_32LO)"
      annotations: "@sai_hash_seed($1)"
      annotations: "@sai_hash_offset(0)"
    })pb";
  return gutil::ParseProtoOrDie<p4::config::v1::Action>(
      absl::Substitute(kTemplate, action_id, hash_seed));
}

p4::config::v1::P4Info P4InfoWithHashSeed(uint32_t hash_seed) {
  constexpr uint32_t kActionId = 17825802;
  constexpr absl::string_view kTemplate = R"pb(
    pkg_info { arch: "v1model" }
    tables {
      preamble {
        id: 33554689
        name: "ingress.hashing.table"
        alias: "table"
        annotations: "@p4runtime_role(\"sdn_controller\")"
        annotations: "@sai_acl(PRE_INGRESS)"
      }
      match_fields {
        id: 1
        name: "is_ip"
        annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_ACL_IP_TYPE / IP)"
        bitwidth: 1
        match_type: OPTIONAL
      }
      action_refs { id: 17825802 annotations: "@proto_id(1)" }
      size: 256
    })pb";

  auto p4info = gutil::ParseProtoOrDie<p4::config::v1::P4Info>(kTemplate);
  *p4info.add_actions() = ActionWithHashSeed(kActionId, hash_seed);
  return p4info;
}

TEST(SetHashSeedTest, ReturnsTrueAndSetsHash) {
  constexpr uint32_t kHashSeed = 1966175594;
  p4::config::v1::P4Info p4info = P4InfoWithHashSeed(0);
  p4::config::v1::P4Info expected_p4info = P4InfoWithHashSeed(kHashSeed);
  EXPECT_TRUE(SetSaiHashSeed(p4info, kHashSeed));
  EXPECT_THAT(p4info, gutil::EqualsProto(expected_p4info));
}

TEST(SetHashSeedTest, SetsAllHashes) {
  constexpr uint32_t kSecondActionId = 2;
  constexpr uint32_t kHashSeed = 1966175594;
  p4::config::v1::P4Info p4info = P4InfoWithHashSeed(0);
  *p4info.add_actions() = ActionWithHashSeed(kSecondActionId, 0);

  p4::config::v1::P4Info expected_p4info = P4InfoWithHashSeed(kHashSeed);
  *expected_p4info.add_actions() =
      ActionWithHashSeed(kSecondActionId, kHashSeed);

  EXPECT_TRUE(SetSaiHashSeed(p4info, kHashSeed));
  EXPECT_THAT(p4info, gutil::EqualsProto(expected_p4info));
}

TEST(SetHashSeedTest, DoesNotOverwriteNonZeroHashes) {
  constexpr uint32_t kHashSeed1 = 1966175594;
  constexpr uint32_t kHashSeed2 = 100;
  p4::config::v1::P4Info p4info = P4InfoWithHashSeed(kHashSeed1);
  p4::config::v1::P4Info original_p4info = p4info;

  EXPECT_FALSE(SetSaiHashSeed(p4info, kHashSeed2));
  EXPECT_THAT(p4info, gutil::EqualsProto(original_p4info));
}

p4::config::v1::P4Info P4InfoWithActionProfile() {
  return gutil::ParseProtoOrDie<p4::config::v1::P4Info>(R"pb(
    action_profiles {
      preamble {
        id: 1
        name: "some_action_profile"
        alias: "some_action_profile"
      }
      table_ids: 2
      with_selector: true
    })pb");
}

TEST(SetSemanticsTest, SumOfMembersSemanticsCorrectlySetAndIsIdempotent) {
  p4::config::v1::P4Info p4info = P4InfoWithActionProfile();

  // Check that the p4info is modified the first time and that the new fields
  // are set correctly.
  EXPECT_TRUE(ApplySumOfMembersSemanticsForActionProfiles(p4info));
  EXPECT_EQ(p4info.action_profiles(0).sum_of_members().max_member_weight(),
            WCMP_GROUP_SELECTOR_SUM_OF_MEMBERS_MAX_MEMBER_WEIGHT);
  EXPECT_EQ(p4info.action_profiles(0).size(), WCMP_GROUP_SUM_OF_MEMBERS_SIZE);
  EXPECT_EQ(p4info.action_profiles(0).max_group_size(),
            WCMP_GROUP_SELECTOR_SUM_OF_MEMBERS_MAX_GROUP_SIZE);

  // Check that pre-existing fields are unmodified.
  EXPECT_THAT(p4info, Partially(EqualsProto(P4InfoWithActionProfile())));

  // Check that the p4info is unmodified the second time and that this is
  // reflected in the return value.
  p4::config::v1::P4Info p4info_copy = p4info;
  EXPECT_FALSE(ApplySumOfMembersSemanticsForActionProfiles(p4info_copy));
  EXPECT_THAT(p4info, EqualsProto(p4info_copy));
}

TEST(SetSemanticsTest, SumOfWeightsSemanticsForTorCorrectlySetAndIsIdempotent) {
  p4::config::v1::P4Info p4info = P4InfoWithActionProfile();

  // Check that the p4info is modified the first time and that the new fields
  // are set correctly.
  EXPECT_TRUE(
      ApplySumOfWeightsSemanticsForActionProfiles(Instantiation::kTor, p4info));
  EXPECT_TRUE(p4info.action_profiles(0).has_sum_of_weights());
  EXPECT_EQ(p4info.action_profiles(0).size(),
            WCMP_GROUP_SUM_OF_WEIGHTS_SIZE_TOR);
  EXPECT_EQ(p4info.action_profiles(0).max_group_size(),
            WCMP_GROUP_SELECTOR_SUM_OF_WEIGHTS_MAX_GROUP_SIZE_TOR);

  // Check that pre-existing fields are unmodified.
  EXPECT_THAT(p4info, Partially(EqualsProto(P4InfoWithActionProfile())));

  // Check that the p4info is unmodified the second time and that this is
  // reflected in the return value.
  p4::config::v1::P4Info p4info_copy = p4info;
  EXPECT_FALSE(ApplySumOfWeightsSemanticsForActionProfiles(Instantiation::kTor,
                                                           p4info_copy));
  EXPECT_THAT(p4info, EqualsProto(p4info_copy));
}

TEST(SetSemanticsTest,
     SumOfWeightsSemanticsForNonTorCorrectlySetAndIsIdempotent) {
  p4::config::v1::P4Info p4info = P4InfoWithActionProfile();

  // Check that the p4info is modified the first time and that the new fields
  // are set correctly.
  EXPECT_TRUE(ApplySumOfWeightsSemanticsForActionProfiles(
      Instantiation::kFabricBorderRouter, p4info));
  EXPECT_TRUE(p4info.action_profiles(0).has_sum_of_weights());
  EXPECT_EQ(p4info.action_profiles(0).size(),
            WCMP_GROUP_SUM_OF_WEIGHTS_SIZE_NON_TOR);
  EXPECT_EQ(p4info.action_profiles(0).max_group_size(),
            WCMP_GROUP_SELECTOR_SUM_OF_WEIGHTS_MAX_GROUP_SIZE_NON_TOR);

  // Check that the p4info is unmodified the second time and that this is
  // reflected in the return value.
  p4::config::v1::P4Info p4info_copy = p4info;
  EXPECT_FALSE(ApplySumOfWeightsSemanticsForActionProfiles(
      Instantiation::kFabricBorderRouter, p4info_copy));
  EXPECT_THAT(p4info, EqualsProto(p4info_copy));
}

TEST(SetSemanticsTest, SemanticsChangeWorksAndIsReflectedInReturn) {
  p4::config::v1::P4Info p4info = P4InfoWithActionProfile();

  // Check that the p4info is modified the first time and that the new fields
  // are set correctly.
  EXPECT_TRUE(
      ApplySumOfWeightsSemanticsForActionProfiles(Instantiation::kTor, p4info));
  EXPECT_TRUE(p4info.action_profiles(0).has_sum_of_weights());
  EXPECT_EQ(p4info.action_profiles(0).size(),
            WCMP_GROUP_SUM_OF_WEIGHTS_SIZE_TOR);
  EXPECT_EQ(p4info.action_profiles(0).max_group_size(),
            WCMP_GROUP_SELECTOR_SUM_OF_WEIGHTS_MAX_GROUP_SIZE_TOR);

  // Check that the p4info is modified the second time and that the new fields
  // are set correctly.
  EXPECT_TRUE(ApplySumOfMembersSemanticsForActionProfiles(p4info));
  EXPECT_EQ(p4info.action_profiles(0).sum_of_members().max_member_weight(),
            WCMP_GROUP_SELECTOR_SUM_OF_MEMBERS_MAX_MEMBER_WEIGHT);
  EXPECT_EQ(p4info.action_profiles(0).size(), WCMP_GROUP_SUM_OF_MEMBERS_SIZE);
  EXPECT_EQ(p4info.action_profiles(0).max_group_size(),
            WCMP_GROUP_SELECTOR_SUM_OF_MEMBERS_MAX_GROUP_SIZE);

  // Check that the p4info can be modified back, but to their non-tor versions.
  EXPECT_TRUE(ApplySumOfWeightsSemanticsForActionProfiles(
      Instantiation::kFabricBorderRouter, p4info));
  EXPECT_TRUE(p4info.action_profiles(0).has_sum_of_weights());
  EXPECT_EQ(p4info.action_profiles(0).size(),
            WCMP_GROUP_SUM_OF_WEIGHTS_SIZE_NON_TOR);
  EXPECT_EQ(p4info.action_profiles(0).max_group_size(),
            WCMP_GROUP_SELECTOR_SUM_OF_WEIGHTS_MAX_GROUP_SIZE_NON_TOR);
}

TEST(SetSemanticsTest, ProfileLessP4InfosAreUnchanged) {
  p4::config::v1::P4Info p4info = P4InfoWithHashSeed(/*hash_seed=*/1);
  p4::config::v1::P4Info original_p4info = p4info;

  EXPECT_FALSE(ApplySumOfWeightsSemanticsForActionProfiles(
      Instantiation::kTor, p4info));
  EXPECT_THAT(original_p4info, EqualsProto(p4info));

  EXPECT_FALSE(ApplySumOfWeightsSemanticsForActionProfiles(
      Instantiation::kMiddleblock, p4info));
  EXPECT_THAT(original_p4info, EqualsProto(p4info));

  EXPECT_FALSE(ApplySumOfMembersSemanticsForActionProfiles(p4info));
  EXPECT_THAT(original_p4info, EqualsProto(p4info));
}

TEST(SetSemanticsTest, WbbP4InfosAreUnchanged) {
  p4::config::v1::P4Info p4info = P4InfoWithHashSeed(/*hash_seed=*/1);
  p4::config::v1::P4Info original_p4info = p4info;

  EXPECT_FALSE(
      ApplySumOfWeightsSemanticsForActionProfiles(Instantiation::kWbb, p4info));
  EXPECT_THAT(original_p4info, EqualsProto(p4info));
}

TEST(SetSemanticsTest, RestOfP4InfoIsUnchanged) {
  p4::config::v1::P4Info p4info = P4InfoWithHashSeed(/*hash_seed=*/1);
  *p4info.add_action_profiles() = P4InfoWithActionProfile().action_profiles(0);
  p4::config::v1::P4Info original_p4info = p4info;

  // Check that the p4info is modified and that the new fields are set
  // correctly, but other fields are unchanged.
  EXPECT_TRUE(ApplySumOfMembersSemanticsForActionProfiles(p4info));
  EXPECT_EQ(p4info.action_profiles(0).sum_of_members().max_member_weight(),
            WCMP_GROUP_SELECTOR_SUM_OF_MEMBERS_MAX_MEMBER_WEIGHT);
  EXPECT_EQ(p4info.action_profiles(0).size(), WCMP_GROUP_SUM_OF_MEMBERS_SIZE);
  EXPECT_EQ(p4info.action_profiles(0).max_group_size(),
            WCMP_GROUP_SELECTOR_SUM_OF_MEMBERS_MAX_GROUP_SIZE);

  // Check that pre-existing fields are unmodified.
  EXPECT_THAT(p4info, Partially(EqualsProto(original_p4info)));
}

using TemporarySetSemanticsTest = ::testing::TestWithParam<sai::Instantiation>;

// TODO: Delete when moving to SumOfMembers semantics in head after
// rollout.
TEST_P(TemporarySetSemanticsTest,
       ConfirmThatCurrentP4InfosModifiedBySetSumOfWeightsAreUnchanged) {
  p4::config::v1::P4Info p4info = sai::GetP4Info(GetParam());
  p4::config::v1::P4Info original_p4info = p4info;

  EXPECT_FALSE(ApplySumOfWeightsSemanticsForActionProfiles(GetParam(), p4info));
  EXPECT_THAT(p4info, EqualsProto(original_p4info));
}

INSTANTIATE_TEST_SUITE_P(
    TemporarySetSemanticsTest, TemporarySetSemanticsTest,
    testing::ValuesIn(sai::AllSaiInstantiations()),
    [](const testing::TestParamInfo<sai::Instantiation>& info) {
      return gutil::SnakeCaseToCamelCase(
          sai::InstantiationToString(info.param));
    });

}  // namespace
}  // namespace sai
