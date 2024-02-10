// Copyright 2025 Google LLC
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

#include <vector>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "p4rt_app/tests/lib/p4runtime_component_test_fixture.h"
#include "p4rt_app/tests/lib/p4runtime_grpc_service.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "swss/warm_restart.h"

namespace p4rt_app {
namespace {

class WarmBootNotificationTest
    : public test_lib::P4RuntimeComponentTestFixture {
 protected:
  WarmBootNotificationTest()
      : test_lib::P4RuntimeComponentTestFixture(sai::Instantiation::kTor) {}
};

// Freeze notification should only be processed if the current warm boot state
// is RECONCILED.
TEST_F(WarmBootNotificationTest,
       WarmBootStateFromReconciledToQuiescentAfterFreeze) {
  p4rt_service_.GetWarmBootStateAdapter()->SetWarmBootState(
      swss::WarmStart::WarmStartState::RECONCILED);
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::RECONCILED);

  EXPECT_OK(p4rt_service_.GetP4rtServer().HandleWarmBootNotification(
      swss::WarmStart::WarmBootNotification::kFreeze));
  // Verify the warm boot state is QUIESCENT.
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);
}

TEST_F(WarmBootNotificationTest,
       FreezeNotificationIgnoredIfWarmBootStateIsNotReconciled) {
  std::vector<swss::WarmStart::WarmStartState> warm_boot_states = {
      swss::WarmStart::WarmStartState::INITIALIZED,
      swss::WarmStart::WarmStartState::RESTORED,
      swss::WarmStart::WarmStartState::REPLAYED,
      swss::WarmStart::WarmStartState::WSDISABLED,
      swss::WarmStart::WarmStartState::WSUNKNOWN,
      swss::WarmStart::WarmStartState::FROZEN,
      swss::WarmStart::WarmStartState::QUIESCENT,
      swss::WarmStart::WarmStartState::CHECKPOINTED,
      swss::WarmStart::WarmStartState::FAILED};

  for (auto warm_boot_state : warm_boot_states) {
    p4rt_service_.GetWarmBootStateAdapter()->SetWarmBootState(warm_boot_state);
    EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
              warm_boot_state);

    EXPECT_OK(p4rt_service_.GetP4rtServer().HandleWarmBootNotification(
        swss::WarmStart::WarmBootNotification::kFreeze));
    // Verify the warm boot state is not changed.
    EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
              warm_boot_state);
  }
}

TEST_F(WarmBootNotificationTest, CheckpointNotificationIsIgnored) {
  p4rt_service_.GetWarmBootStateAdapter()->SetWarmBootState(
      swss::WarmStart::WarmStartState::RECONCILED);
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::RECONCILED);

  // Checkpoint notification is ignored when P4RT is not in freeze mode.
  EXPECT_OK(p4rt_service_.GetP4rtServer().HandleWarmBootNotification(
      swss::WarmStart::WarmBootNotification::kCheckpoint));
  // Verify the warm boot state is not changed.
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::RECONCILED);

  // Send freeze notification.
  EXPECT_OK(p4rt_service_.GetP4rtServer().HandleWarmBootNotification(
      swss::WarmStart::WarmBootNotification::kFreeze));
  // Verify the warm boot state is QUIESCENT.
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);

  // Checkpoint notification is ignored when P4RT is in freeze mode.
  EXPECT_OK(p4rt_service_.GetP4rtServer().HandleWarmBootNotification(
      swss::WarmStart::WarmBootNotification::kCheckpoint));
  // Verify the warm boot state is not changed.
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);
}

TEST_F(WarmBootNotificationTest, DuplicateFreezeNotificationIsIgnored) {
  p4rt_service_.GetWarmBootStateAdapter()->SetWarmBootState(
      swss::WarmStart::WarmStartState::RECONCILED);
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::RECONCILED);

  EXPECT_OK(p4rt_service_.GetP4rtServer().HandleWarmBootNotification(
      swss::WarmStart::WarmBootNotification::kFreeze));
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);

  EXPECT_OK(p4rt_service_.GetP4rtServer().HandleWarmBootNotification(
      swss::WarmStart::WarmBootNotification::kFreeze));
  // Verify the warm boot state is not changed by duplicate freeze notification.
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);
}

TEST_F(WarmBootNotificationTest,
       WarmBootStateFromReconciledToCompletedAfterUnFreeze) {
  // Freeze P4RT
  EXPECT_OK(p4rt_service_.GetP4rtServer().HandleWarmBootNotification(
      swss::WarmStart::WarmBootNotification::kFreeze));
  // Verify the warm boot state is QUIESCENT.
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);

  p4rt_service_.GetWarmBootStateAdapter()->SetWarmBootState(
      swss::WarmStart::WarmStartState::RECONCILED);
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::RECONCILED);

  // Unfreeze P4RT
  EXPECT_OK(p4rt_service_.GetP4rtServer().HandleWarmBootNotification(
      swss::WarmStart::WarmBootNotification::kUnfreeze));
}

TEST_F(WarmBootNotificationTest, DuplicateUnfreezeNotificationIsIgnored) {
  // Freeze P4RT
  EXPECT_OK(p4rt_service_.GetP4rtServer().HandleWarmBootNotification(
      swss::WarmStart::WarmBootNotification::kFreeze));
  // Verify the warm boot state is QUIESCENT.
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);

  p4rt_service_.GetWarmBootStateAdapter()->SetWarmBootState(
      swss::WarmStart::WarmStartState::RECONCILED);
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::RECONCILED);

  // Unfreeze P4RT
  EXPECT_OK(p4rt_service_.GetP4rtServer().HandleWarmBootNotification(
      swss::WarmStart::WarmBootNotification::kUnfreeze));

  // Unfreeze P4RT
  EXPECT_OK(p4rt_service_.GetP4rtServer().HandleWarmBootNotification(
      swss::WarmStart::WarmBootNotification::kUnfreeze));
}

TEST_F(WarmBootNotificationTest,
       UnfreezeIgnoredIfStateIsNeitherReconciledNorFrozenNorQuiescent) {
  // Freeze P4RT
  EXPECT_OK(p4rt_service_.GetP4rtServer().HandleWarmBootNotification(
      swss::WarmStart::WarmBootNotification::kFreeze));
  // Verify the warm boot state is QUIESCENT.
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);

  p4rt_service_.GetWarmBootStateAdapter()->SetWarmBootState(
      swss::WarmStart::WarmStartState::RECONCILED);
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::RECONCILED);

  std::vector<swss::WarmStart::WarmStartState> warm_boot_states = {
      swss::WarmStart::WarmStartState::INITIALIZED,
      swss::WarmStart::WarmStartState::RESTORED,
      swss::WarmStart::WarmStartState::REPLAYED,
      swss::WarmStart::WarmStartState::WSDISABLED,
      swss::WarmStart::WarmStartState::WSUNKNOWN,
      swss::WarmStart::WarmStartState::CHECKPOINTED,
      swss::WarmStart::WarmStartState::FAILED};

  for (auto warm_boot_state : warm_boot_states) {
    p4rt_service_.GetWarmBootStateAdapter()->SetWarmBootState(warm_boot_state);
    EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
              warm_boot_state);

    EXPECT_OK(p4rt_service_.GetP4rtServer().HandleWarmBootNotification(
        swss::WarmStart::WarmBootNotification::kUnfreeze));
    // Verify the warm boot state is not changed.
    EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
              warm_boot_state);
  }
}

}  // namespace
}  // namespace p4rt_app
