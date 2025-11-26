// Copyright 2024 Google LLC
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
#include <algorithm>
#include <cstdint>
#include <optional>
#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4rt_app/tests/lib/p4runtime_component_test_fixture.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"

namespace p4rt_app {
namespace {

using ::gutil::IsOk;
using ::gutil::StatusIs;
using ::testing::AllOf;
using ::testing::HasSubstr;

absl::StatusOr<int64_t> GetMaximumSizeForActionProfile(
    const pdpi::IrP4Info& ir_p4_info, absl::string_view profile_name) {
  // Verify that the table actually exists.
  const pdpi::IrActionProfileDefinition* profile_def =
      gutil::FindOrNull(ir_p4_info.action_profiles_by_name(), profile_name);
  if (profile_def == nullptr) {
    return gutil::NotFoundErrorBuilder()
           << "action profile does not exist in the P4Info: " << profile_name;
  }
  return profile_def->action_profile().size();
}

absl::StatusOr<int64_t> GetMaxGroupSizeForActionProfile(
    const pdpi::IrP4Info& ir_p4_info, absl::string_view profile_name) {
  // Verify that the table actually exists.
  const pdpi::IrActionProfileDefinition* profile_def =
      gutil::FindOrNull(ir_p4_info.action_profiles_by_name(), profile_name);
  if (profile_def == nullptr) {
    return gutil::NotFoundErrorBuilder()
           << "action profile does not exist in the P4Info: " << profile_name;
  }
  return profile_def->action_profile().max_group_size();
}

absl::StatusOr<p4::v1::Update> WcmpUpdateWithNMembers(
    const pdpi::IrP4Info& ir_p4_info, p4::v1::Update::Type update_type,
    const std::string& group_id, int group_size, int member_weight = 1,
    int nexthop_index_start = 1) {
  // Set the update type, and table name.
  pdpi::IrUpdate update;
  update.set_type(update_type);
  update.mutable_entity()->mutable_table_entry()->set_table_name(
      "wcmp_group_table");

  // Set the match fields.
  pdpi::IrMatch* match =
      update.mutable_entity()->mutable_table_entry()->add_matches();
  match->set_name("wcmp_group_id");
  match->mutable_exact()->set_str(group_id);

  // Add all the member actions.
  for (int action_id = 0; action_id < group_size; ++action_id) {
    pdpi::IrActionSetInvocation* action_set = update.mutable_entity()
                                                  ->mutable_table_entry()
                                                  ->mutable_action_set()
                                                  ->add_actions();
    pdpi::IrActionInvocation::IrActionParam* param =
        action_set->mutable_action()->add_params();

    action_set->set_weight(member_weight);
    action_set->mutable_action()->set_name("set_nexthop_id");
    param->set_name("nexthop_id");
    param->mutable_value()->set_str(
        absl::StrCat("nexthop-", nexthop_index_start + action_id));
  }

  // Convert from IR to PI.
  return pdpi::IrUpdateToPi(ir_p4_info, update);
}

// On actual hardware resources can be very large which make these component
// tests run slowly. To speed them up and simplify the tests we modify the
// values in the P4Info for these tests.
p4::config::v1::P4Info GetResourceLimitsP4Info(
    int64_t size, int32_t max_group_size,
    std::optional<int32_t> max_member_weight) {
  p4::config::v1::P4Info p4info =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);

  for (auto& action_profile : *p4info.mutable_action_profiles()) {
    action_profile.set_size(size);
    action_profile.set_max_group_size(max_group_size);
    if (max_member_weight.has_value()) {
      action_profile.mutable_sum_of_members()->set_max_member_weight(
          *max_member_weight);
    } else {
      action_profile.mutable_sum_of_weights();
    }
  }

  return p4info;
}

constexpr int64_t kActionProfileSize = 100;
constexpr int32_t kActionProfileMaxGroupSize = 99;
class SumOfWeightsResourceLimitsTest
    : public test_lib::P4RuntimeComponentTestFixture {
 protected:
  SumOfWeightsResourceLimitsTest()
      : test_lib::P4RuntimeComponentTestFixture(GetResourceLimitsP4Info(
            kActionProfileSize, kActionProfileMaxGroupSize, std::nullopt)) {}

  // Selector names are dependent on the P4 program, but shouldn't affect the
  // test behaviors. We use a static member variable to simplify any future
  // changes.
  static constexpr absl::string_view kWcmpGroupSelectorName =
      "wcmp_group_selector";
};

constexpr int32_t kActionProfileMaxMemberWeight = 200;
class SumOfMembersResourceLimitsTest
    : public test_lib::P4RuntimeComponentTestFixture {
 protected:
  SumOfMembersResourceLimitsTest()
      : test_lib::P4RuntimeComponentTestFixture(GetResourceLimitsP4Info(
            kActionProfileSize, kActionProfileMaxGroupSize,
            kActionProfileMaxMemberWeight)) {}

  // Selector names are dependent on the P4 program, but shouldn't affect the
  // test behaviors. We use a static member variable to simplify any future
  // changes.
  static constexpr absl::string_view kWcmpGroupSelectorName =
      "wcmp_group_selector";
};

TEST_F(SumOfWeightsResourceLimitsTest,
       WcmpAccountingRejectsInsertsBeyondLimit) {
  ASSERT_OK_AND_ASSIGN(
      int64_t max_size,
      GetMaximumSizeForActionProfile(ir_p4_info_, kWcmpGroupSelectorName));

  p4::v1::WriteRequest request;
  ASSERT_OK_AND_ASSIGN(
      *request.add_updates(),
      WcmpUpdateWithNMembers(ir_p4_info_, p4::v1::Update::INSERT,
                             /*group_id=*/"group-1", max_size - 10));
  ASSERT_OK_AND_ASSIGN(
      *request.add_updates(),
      WcmpUpdateWithNMembers(ir_p4_info_, p4::v1::Update::INSERT,
                             /*group_id=*/"group-2", /*group_size=*/11));

  // Using more resources than available should result in a RESOURCE_EXHAUSTED
  // error.
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request),
      StatusIs(absl::StatusCode::kUnknown,
               HasSubstr(
                   "#2: RESOURCE_EXHAUSTED: [P4RT App] not enough resources")));
}

TEST_F(SumOfMembersResourceLimitsTest,
       WcmpAccountingRejectsInsertsBeyondLimit) {
  ASSERT_OK_AND_ASSIGN(
      int64_t max_size,
      GetMaximumSizeForActionProfile(ir_p4_info_, kWcmpGroupSelectorName));

  p4::v1::WriteRequest request;
  ASSERT_OK_AND_ASSIGN(
      *request.add_updates(),
      WcmpUpdateWithNMembers(ir_p4_info_, p4::v1::Update::INSERT,
                             /*group_id=*/"group-1", max_size - 10));
  ASSERT_OK_AND_ASSIGN(
      *request.add_updates(),
      WcmpUpdateWithNMembers(ir_p4_info_, p4::v1::Update::INSERT,
                             /*group_id=*/"group-2", /*group_size=*/11));

  // Using more resources than available should result in a RESOURCE_EXHAUSTED
  // error.
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request),
      StatusIs(absl::StatusCode::kUnknown,
               HasSubstr(
                   "#2: RESOURCE_EXHAUSTED: [P4RT App] not enough resources")));
}

TEST_F(SumOfWeightsResourceLimitsTest,
       WcmpAccountingRejectsGroupSizeThatIsTooLarge) {
  ASSERT_OK_AND_ASSIGN(
      int64_t max_group_size,
      GetMaxGroupSizeForActionProfile(ir_p4_info_, kWcmpGroupSelectorName));

  p4::v1::WriteRequest request;
  ASSERT_OK_AND_ASSIGN(
      *request.add_updates(),
      WcmpUpdateWithNMembers(ir_p4_info_, p4::v1::Update::INSERT,
                             /*group_id=*/"group-1", max_group_size + 1));

  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request),
      StatusIs(absl::StatusCode::kUnknown,
               HasSubstr("#1: INVALID_ARGUMENT: [P4RT App] too much weight")));
}

TEST_F(SumOfMembersResourceLimitsTest,
       WcmpAccountingRejectsGroupSizeThatIsTooLarge) {
  ASSERT_OK_AND_ASSIGN(
      int64_t max_group_size,
      GetMaxGroupSizeForActionProfile(ir_p4_info_, kWcmpGroupSelectorName));

  p4::v1::WriteRequest request;
  ASSERT_OK_AND_ASSIGN(
      *request.add_updates(),
      WcmpUpdateWithNMembers(ir_p4_info_, p4::v1::Update::INSERT,
                             /*group_id=*/"group-1", max_group_size + 1));

  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request),
      StatusIs(absl::StatusCode::kUnknown,
               HasSubstr("#1: INVALID_ARGUMENT: [P4RT App] too many actions")));
}

TEST_F(SumOfWeightsResourceLimitsTest,
       WcmpAccountingRejectsGroupWeightGreaterThanSize) {
  ASSERT_OK_AND_ASSIGN(
      int64_t max_group_size,
      GetMaxGroupSizeForActionProfile(ir_p4_info_, kWcmpGroupSelectorName));

  p4::v1::WriteRequest request;
  ASSERT_OK_AND_ASSIGN(
      *request.add_updates(),
      WcmpUpdateWithNMembers(ir_p4_info_, p4::v1::Update::INSERT,
                             /*group_id=*/"group-1", max_group_size / 10,
                             /*member_weight=*/50));

  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request),
      StatusIs(
          absl::StatusCode::kUnknown,
          HasSubstr(
              "#1: INVALID_ARGUMENT: [P4RT App] too much weight in actions")));
}

TEST_F(SumOfMembersResourceLimitsTest,
       WcmpAccountingAcceptsGroupWeightGreaterThanSize) {
  ASSERT_OK_AND_ASSIGN(
      int64_t max_group_size,
      GetMaxGroupSizeForActionProfile(ir_p4_info_, kWcmpGroupSelectorName));

  p4::v1::WriteRequest request;
  ASSERT_OK_AND_ASSIGN(
      *request.add_updates(),
      WcmpUpdateWithNMembers(
          ir_p4_info_, p4::v1::Update::INSERT,
          /*group_id=*/"group-1", max_group_size / 10,
          /*member_weight=*/kActionProfileMaxMemberWeight / 2));

  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request),
      IsOk());
}

TEST_F(SumOfMembersResourceLimitsTest,
       WcmpAccountingRejectsSingleMemberWeightGreaterThanMaxMemberWeight) {
  ASSERT_OK_AND_ASSIGN(
      int64_t max_group_size,
      GetMaxGroupSizeForActionProfile(ir_p4_info_, kWcmpGroupSelectorName));

  p4::v1::WriteRequest request;
  ASSERT_OK_AND_ASSIGN(
      *request.add_updates(),
      WcmpUpdateWithNMembers(
          ir_p4_info_, p4::v1::Update::INSERT,
          /*group_id=*/"group-1", max_group_size / 10,
          /*member_weight=*/kActionProfileMaxMemberWeight + 1));

  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request),
      StatusIs(
          absl::StatusCode::kUnknown,
          HasSubstr(
              "#1: INVALID_ARGUMENT: [P4RT App] Action had too high weight")));
}

// This test will:
//   * Use a SumOfWeights action profile.
//   * Insert WCMP members up to the resource limit.
//   * Verify that a modify can be done on all the members.
//   * Try to insert 1 more entry, but expect it to fail because the resources
//     are all used.
TEST_F(SumOfWeightsResourceLimitsTest,
       WcmpAccountingSupportsModifyingUpToTheLimit) {
  ASSERT_OK_AND_ASSIGN(
      int64_t max_size,
      GetMaximumSizeForActionProfile(ir_p4_info_, kWcmpGroupSelectorName));

  p4::v1::WriteRequest request;
  ASSERT_OK_AND_ASSIGN(
      *request.add_updates(),
      WcmpUpdateWithNMembers(ir_p4_info_, p4::v1::Update::INSERT,
                             /*group_id=*/"group-1", max_size - 10));
  ASSERT_OK_AND_ASSIGN(
      *request.add_updates(),
      WcmpUpdateWithNMembers(ir_p4_info_, p4::v1::Update::INSERT,
                             /*group_id=*/"group-2", /*group_size=*/10));

  p4::v1::WriteRequest overflow_request;
  ASSERT_OK_AND_ASSIGN(
      *overflow_request.add_updates(),
      WcmpUpdateWithNMembers(ir_p4_info_, p4::v1::Update::INSERT,
                             /*group_id=*/"group-3", /*group_size=*/1));

  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));

  // We're only verifyifying the accounting behavior so reusing the same value
  // should not matter.
  request.mutable_updates(0)->set_type(p4::v1::Update::MODIFY);
  request.mutable_updates(1)->set_type(p4::v1::Update::MODIFY);
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));

  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                             overflow_request),
      StatusIs(absl::StatusCode::kUnknown,
               HasSubstr(
                   "#1: RESOURCE_EXHAUSTED: [P4RT App] not enough resources")));
}

// This test will:
//   * Use a SumOfMembers action profile.
//   * Insert WCMP members with high weights up to the resource limit.
//   * Verify that a modify can be done on all the members.
//   * Try to insert 1 more entry, but expect it to fail because the resources
//     are all used.
TEST_F(SumOfMembersResourceLimitsTest,
       WcmpAccountingSupportsModifyingUpToTheLimit) {
  ASSERT_OK_AND_ASSIGN(
      int64_t max_size,
      GetMaximumSizeForActionProfile(ir_p4_info_, kWcmpGroupSelectorName));

  p4::v1::WriteRequest request;
  ASSERT_OK_AND_ASSIGN(
      *request.add_updates(),
      WcmpUpdateWithNMembers(
          ir_p4_info_, p4::v1::Update::INSERT,
          /*group_id=*/"group-1", max_size - 10,
          /*member_weight=*/kActionProfileMaxMemberWeight / 2));
  ASSERT_OK_AND_ASSIGN(
      *request.add_updates(),
      WcmpUpdateWithNMembers(
          ir_p4_info_, p4::v1::Update::INSERT,
          /*group_id=*/"group-2", /*group_size=*/10,
          /*member_weight=*/kActionProfileMaxMemberWeight / 2));

  p4::v1::WriteRequest overflow_request;
  ASSERT_OK_AND_ASSIGN(
      *overflow_request.add_updates(),
      WcmpUpdateWithNMembers(
          ir_p4_info_, p4::v1::Update::INSERT,
          /*group_id=*/"group-3", /*group_size=*/1,
          /*member_weight=*/kActionProfileMaxMemberWeight / 2));

  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));

  // We're only verifyifying the accounting behavior so reusing the same value
  // should not matter.
  request.mutable_updates(0)->set_type(p4::v1::Update::MODIFY);
  request.mutable_updates(1)->set_type(p4::v1::Update::MODIFY);
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));

  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                             overflow_request),
      StatusIs(absl::StatusCode::kUnknown,
               HasSubstr(
                   "#1: RESOURCE_EXHAUSTED: [P4RT App] not enough resources")));
}

// This test will:
//   * Insert WCMP members up to the resource limit.
//   * Modify the group to save space for 5 resource.
//   * Insert 5 new entry which should succeed.
//   * Insert 1 more entry which should fail.
TEST_F(SumOfWeightsResourceLimitsTest,
       WcmpAccountingModifyMembersCanReduceResources) {
  ASSERT_OK_AND_ASSIGN(
      int64_t max_size,
      GetMaximumSizeForActionProfile(ir_p4_info_, kWcmpGroupSelectorName));

  p4::v1::WriteRequest insert_request;
  ASSERT_OK_AND_ASSIGN(
      *insert_request.add_updates(),
      WcmpUpdateWithNMembers(ir_p4_info_, p4::v1::Update::INSERT,
                             /*group_id=*/"group-1", max_size - 1));
  p4::v1::WriteRequest modify_request;
  ASSERT_OK_AND_ASSIGN(
      *modify_request.add_updates(),
      WcmpUpdateWithNMembers(ir_p4_info_, p4::v1::Update::MODIFY,
                             /*group_id=*/"group-1", max_size - 5));
  p4::v1::WriteRequest valid_insert_request;
  ASSERT_OK_AND_ASSIGN(
      *valid_insert_request.add_updates(),
      WcmpUpdateWithNMembers(ir_p4_info_, p4::v1::Update::INSERT,
                             /*group_id=*/"group-2", /*group_size=*/5));
  p4::v1::WriteRequest overflow_insert_request;
  ASSERT_OK_AND_ASSIGN(
      *overflow_insert_request.add_updates(),
      WcmpUpdateWithNMembers(ir_p4_info_, p4::v1::Update::INSERT,
                             /*group_id=*/"group-3", /*group_size=*/1));

  EXPECT_OK(pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                   insert_request));
  EXPECT_OK(pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                   modify_request));
  EXPECT_OK(pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                   valid_insert_request));
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                             overflow_insert_request),
      StatusIs(absl::StatusCode::kUnknown,
               HasSubstr(
                   "#1: RESOURCE_EXHAUSTED: [P4RT App] not enough resources")));
}

// This test will:
//   * Use a SumOfWeights action profile.
//   * Insert a WCMP member with weight up to the limit of group size or size.
//   * Modify the group to reduce the weight by 5.
//   * Insert a new entry with the maximal weight that should succeed.
//   * Insert 1 more entry which should fail.
TEST_F(SumOfWeightsResourceLimitsTest,
       WcmpAccountingModifyWeightsCanReduceResources) {
  ASSERT_OK_AND_ASSIGN(
      int64_t max_size,
      GetMaximumSizeForActionProfile(ir_p4_info_, kWcmpGroupSelectorName));
  ASSERT_OK_AND_ASSIGN(
      int64_t max_group_size,
      GetMaxGroupSizeForActionProfile(ir_p4_info_, kWcmpGroupSelectorName));

  // If max_size isn't at most 2x max_group_size (plus a little), this test
  // won't work.
  ASSERT_GT((max_group_size + 3) * 2, max_size);

  p4::v1::WriteRequest insert_request;
  ASSERT_OK_AND_ASSIGN(
      *insert_request.add_updates(),
      WcmpUpdateWithNMembers(
          ir_p4_info_, p4::v1::Update::INSERT,
          /*group_id=*/"group-1", /*group_size=*/1,
          /*member_weight=*/std::min(max_group_size, max_size)));
  p4::v1::WriteRequest modify_request;
  ASSERT_OK_AND_ASSIGN(
      *modify_request.add_updates(),
      WcmpUpdateWithNMembers(
          ir_p4_info_, p4::v1::Update::MODIFY,
          /*group_id=*/"group-1", /*group_size=*/1,
          /*member_weight=*/std::min(max_group_size, max_size) - 5));
  p4::v1::WriteRequest valid_insert_request;
  ASSERT_OK_AND_ASSIGN(
      *valid_insert_request.add_updates(),
      WcmpUpdateWithNMembers(
          ir_p4_info_, p4::v1::Update::INSERT,
          /*group_id=*/"group-2", /*group_size=*/1,
          /*member_weight=*/max_size - std::min(max_group_size, max_size) + 5));
  p4::v1::WriteRequest overflow_insert_request;
  ASSERT_OK_AND_ASSIGN(
      *overflow_insert_request.add_updates(),
      WcmpUpdateWithNMembers(ir_p4_info_, p4::v1::Update::INSERT,
                             /*group_id=*/"group-3", /*group_size=*/1));

  EXPECT_OK(pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                   insert_request));
  EXPECT_OK(pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                   modify_request));
  EXPECT_OK(pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                   valid_insert_request));
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                             overflow_insert_request),
      StatusIs(absl::StatusCode::kUnknown,
               HasSubstr(
                   "#1: RESOURCE_EXHAUSTED: [P4RT App] not enough resources")));
}

// This test will:
//   * Insert group-1 with WCMP members up to the resource limit minus 5.
//   * Insert group-2 with 5 new members, and expect it to succeed.
//   * Insert group-3 with 5 more members, and expect it to fail.
//   * Delete group-2 freeing up space for 5 more members.
//   * Insert group-3 and expect it to succeed.
TEST_F(SumOfWeightsResourceLimitsTest, WcmpAccountingSupportsDelete) {
  ASSERT_OK_AND_ASSIGN(
      int64_t max_size,
      GetMaximumSizeForActionProfile(ir_p4_info_, kWcmpGroupSelectorName));

  p4::v1::WriteRequest group_1;
  ASSERT_OK_AND_ASSIGN(
      *group_1.add_updates(),
      WcmpUpdateWithNMembers(ir_p4_info_, p4::v1::Update::INSERT,
                             /*group_id=*/"group-1", max_size - 5));
  p4::v1::WriteRequest group_2;
  ASSERT_OK_AND_ASSIGN(
      *group_2.add_updates(),
      WcmpUpdateWithNMembers(ir_p4_info_, p4::v1::Update::INSERT,
                             /*group_id=*/"group-2", /*group_size=*/5));
  p4::v1::WriteRequest group_3;
  ASSERT_OK_AND_ASSIGN(
      *group_3.add_updates(),
      WcmpUpdateWithNMembers(ir_p4_info_, p4::v1::Update::INSERT,
                             /*group_id=*/"group-3", /*group_size=*/5));

  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), group_1));
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), group_2));
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), group_3),
      StatusIs(absl::StatusCode::kUnknown,
               HasSubstr(
                   "#1: RESOURCE_EXHAUSTED: [P4RT App] not enough resources")));

  group_2.mutable_updates(0)->set_type(p4::v1::Update::DELETE);
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), group_2));
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), group_3));
}

TEST_F(SumOfWeightsResourceLimitsTest, WcmpAccountingHandlesBatchRequests) {
  ASSERT_OK_AND_ASSIGN(
      int64_t max_size,
      GetMaximumSizeForActionProfile(ir_p4_info_, kWcmpGroupSelectorName));

  p4::v1::WriteRequest insert_request;
  ASSERT_OK_AND_ASSIGN(
      *insert_request.add_updates(),
      WcmpUpdateWithNMembers(ir_p4_info_, p4::v1::Update::INSERT,
                             /*group_id=*/"group-1", max_size - 1));
  ASSERT_OK_AND_ASSIGN(
      *insert_request.add_updates(),
      WcmpUpdateWithNMembers(ir_p4_info_, p4::v1::Update::INSERT,
                             /*group_id=*/"group-2", /*group_size=*/2));
  ASSERT_OK_AND_ASSIGN(
      *insert_request.add_updates(),
      WcmpUpdateWithNMembers(ir_p4_info_, p4::v1::Update::INSERT,
                             /*group_id=*/"group-3", /*group_size=*/1));

  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                             insert_request),
      StatusIs(
          absl::StatusCode::kUnknown,
          AllOf(HasSubstr(
                    "#2: RESOURCE_EXHAUSTED: [P4RT App] not enough resources"),
                HasSubstr("#3: ABORTED"))));
}

TEST_F(SumOfWeightsResourceLimitsTest, WcmpAccountingAssumesModifyWillPass) {
  ASSERT_OK_AND_ASSIGN(
      int64_t max_size,
      GetMaximumSizeForActionProfile(ir_p4_info_, kWcmpGroupSelectorName));

  // Insert 5 entries.
  p4::v1::WriteRequest insert_request;
  ASSERT_OK_AND_ASSIGN(
      *insert_request.add_updates(),
      WcmpUpdateWithNMembers(ir_p4_info_, p4::v1::Update::INSERT,
                             /*group_id=*/"group-1", /*group_size=*/5));
  ASSERT_OK_AND_ASSIGN(
      *insert_request.add_updates(),
      WcmpUpdateWithNMembers(ir_p4_info_, p4::v1::Update::INSERT,
                             /*group_id=*/"group-2", max_size - 5));

  // Modify the previous 5 entries down to 4, and Insert 1 more entry. If the
  // modify fails in a lower layer then it is that layer's responsibility to
  // mark the insert as aborted.
  p4::v1::WriteRequest batch_request;
  ASSERT_OK_AND_ASSIGN(
      *batch_request.add_updates(),
      WcmpUpdateWithNMembers(ir_p4_info_, p4::v1::Update::MODIFY,
                             /*group_id=*/"group-1", /*group_size=*/4));
  ASSERT_OK_AND_ASSIGN(
      *batch_request.add_updates(),
      WcmpUpdateWithNMembers(ir_p4_info_, p4::v1::Update::INSERT,
                             /*group_id=*/"group-3", /*group_size=*/1));

  EXPECT_OK(pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                   insert_request));
  EXPECT_OK(pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                   batch_request));
}

TEST_F(SumOfWeightsResourceLimitsTest, WcmpAccountingAssumesDeleteWillPass) {
  ASSERT_OK_AND_ASSIGN(
      int64_t max_size,
      GetMaximumSizeForActionProfile(ir_p4_info_, kWcmpGroupSelectorName));

  // Insert 5 entries.
  p4::v1::WriteRequest insert_request;
  ASSERT_OK_AND_ASSIGN(
      *insert_request.add_updates(),
      WcmpUpdateWithNMembers(ir_p4_info_, p4::v1::Update::INSERT,
                             /*group_id=*/"group-1", /*group_size=*/5));
  ASSERT_OK_AND_ASSIGN(
      *insert_request.add_updates(),
      WcmpUpdateWithNMembers(ir_p4_info_, p4::v1::Update::INSERT,
                             /*group_id=*/"group-2", max_size - 5));

  // Delete the previous 5 entries, and Insert 1 more entry. If the delete fails
  // in a lower layer then it is that layer's responsibility to mark the insert
  // as aborted.
  p4::v1::WriteRequest batch_request;
  *batch_request.add_updates() = insert_request.updates(0);
  batch_request.mutable_updates(0)->set_type(p4::v1::Update::DELETE);
  ASSERT_OK_AND_ASSIGN(
      *batch_request.add_updates(),
      WcmpUpdateWithNMembers(ir_p4_info_, p4::v1::Update::INSERT,
                             /*group_id=*/"group-3", /*group_size=*/1));

  EXPECT_OK(pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                   insert_request));
  EXPECT_OK(pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                   batch_request));
}

}  // namespace
}  // namespace p4rt_app
