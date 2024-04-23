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
#include "p4rt_app/sonic/adapters/fake_warm_boot_state_adapter.h"

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "swss/warm_restart.h"

namespace p4rt_app {
namespace sonic {
namespace {

TEST(FakeWarmBootStateAdapterTest, GetWarmBootStateDefault) {
  FakeWarmBootStateAdapter adapter;
  EXPECT_THAT(adapter.GetWarmBootState(),
              swss::WarmStart::WarmStartState::RECONCILED);
}

TEST(FakeWarmBootStateAdapterTest, SetWarmBootState) {
  FakeWarmBootStateAdapter adapter;
  swss::WarmStart::WarmStartState state =
      swss::WarmStart::WarmStartState::INITIALIZED;
  adapter.SetWarmBootState(state);
  EXPECT_THAT(adapter.GetWarmBootState(), state);
}

TEST(FakeWarmBootStateAdapterTest, SetWarmStart) {
  FakeWarmBootStateAdapter adapter;
  EXPECT_THAT(adapter.IsWarmStart(), false);
  adapter.SetWarmStart(true);
  EXPECT_THAT(adapter.IsWarmStart(), true);
  adapter.SetWarmStart(false);
  EXPECT_THAT(adapter.IsWarmStart(), false);
}

TEST(FakeWarmBootStateAdapterTest, WaitForUnfreeze) {
  FakeWarmBootStateAdapter adapter;
  EXPECT_THAT(adapter.WaitForUnfreeze(), false);
  adapter.SetWaitForUnfreeze(true);
  EXPECT_THAT(adapter.WaitForUnfreeze(), true);
  adapter.SetWaitForUnfreeze(false);
  EXPECT_THAT(adapter.WaitForUnfreeze(), false);
}

TEST(FakeWarmBootStateAdapterTest, SetOrchAgentWarmBootState) {
  FakeWarmBootStateAdapter adapter;
  EXPECT_THAT(adapter.GetOrchAgentWarmBootState(), swss::WarmStart::WSUNKNOWN);
  adapter.SetOrchAgentWarmBootState(
      swss::WarmStart::WarmStartState::RECONCILED);
  EXPECT_THAT(adapter.GetOrchAgentWarmBootState(), swss::WarmStart::RECONCILED);
  adapter.SetOrchAgentWarmBootState(swss::WarmStart::WarmStartState::FROZEN);
  EXPECT_THAT(adapter.GetOrchAgentWarmBootState(), swss::WarmStart::FROZEN);
  adapter.SetOrchAgentWarmBootState(swss::WarmStart::WarmStartState::FAILED);
  EXPECT_THAT(adapter.GetOrchAgentWarmBootState(), swss::WarmStart::FAILED);
}

TEST(FakeWarmBootStateAdapterTest, UpdateWarmBootStage) {
  FakeWarmBootStateAdapter adapter;
  EXPECT_THAT(adapter.GetWarmBootStage(),
              swss::WarmStart::WarmBootStage::STAGE_UNFREEZE);
  EXPECT_THAT(adapter.GetWarmBootStageFailureFlag(), false);

  adapter.UpdateWarmBootStageStart(
      swss::WarmStart::WarmBootStage::STAGE_FREEZE);
  EXPECT_THAT(adapter.GetWarmBootStage(),
              swss::WarmStart::WarmBootStage::STAGE_FREEZE);
  EXPECT_THAT(adapter.GetWarmBootStageFailureFlag(), false);

  adapter.UpdateWarmBootStageStart(
      swss::WarmStart::WarmBootStage::STAGE_UNFREEZE);
  EXPECT_THAT(adapter.GetWarmBootStage(),
              swss::WarmStart::WarmBootStage::STAGE_UNFREEZE);
  EXPECT_THAT(adapter.GetWarmBootStageFailureFlag(), false);

  adapter.UpdateWarmBootStageEndOnFailure(
      swss::WarmStart::WarmBootStage::STAGE_RECONCILIATION);
  EXPECT_THAT(adapter.GetWarmBootStage(),
              swss::WarmStart::WarmBootStage::STAGE_RECONCILIATION);
  EXPECT_THAT(adapter.GetWarmBootStageFailureFlag(), true);
}

}  // namespace
}  // namespace sonic
}  // namespace p4rt_app
