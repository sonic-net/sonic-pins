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

#include <vector>

#include "swss/warm_restart.h"

namespace p4rt_app {
namespace sonic {

FakeWarmBootStateAdapter::FakeWarmBootStateAdapter() {
  states_.push_back(swss::WarmStart::WarmStartState::RECONCILED);
}

swss::WarmStart::WarmStartState FakeWarmBootStateAdapter::GetWarmBootState() {
  return states_.back();
}

std::vector<swss::WarmStart::WarmStartState>
FakeWarmBootStateAdapter::GetWarmBootStateHistory() {
  return states_;
}

void FakeWarmBootStateAdapter::SetWarmBootState(
    swss::WarmStart::WarmStartState state) {
  states_.push_back(state);
}

bool FakeWarmBootStateAdapter::IsWarmStart() { return is_warm_start_; }

void FakeWarmBootStateAdapter::SetWarmStart(bool is_warm_start) {
  is_warm_start_ = is_warm_start;
}
void FakeWarmBootStateAdapter::SetWaitForUnfreeze(bool wait_for_unfreeze) {
  wait_for_unfreeze_ = wait_for_unfreeze;
}

bool FakeWarmBootStateAdapter::WaitForUnfreeze() { return wait_for_unfreeze_; }

void FakeWarmBootStateAdapter::SetOrchAgentWarmBootState(
    swss::WarmStart::WarmStartState state) {
  oa_state_ = state;
}

swss::WarmStart::WarmStartState
FakeWarmBootStateAdapter::GetOrchAgentWarmBootState() {
  return oa_state_;
}

void FakeWarmBootStateAdapter::UpdateWarmBootStageStart(
    const swss::WarmStart::WarmBootStage stage) {
  warm_boot_stage_ = stage;
  warm_boot_stage_failure_flag_ = false;
}

void FakeWarmBootStateAdapter::UpdateWarmBootStageEndOnFailure(
    const swss::WarmStart::WarmBootStage stage) {
  warm_boot_stage_ = stage;
  warm_boot_stage_failure_flag_ = true;
}

swss::WarmStart::WarmBootStage FakeWarmBootStateAdapter::GetWarmBootStage(
    void) {
  return warm_boot_stage_;
}

bool FakeWarmBootStateAdapter::GetWarmBootStageFailureFlag(void) {
  return warm_boot_stage_failure_flag_;
}

}  // namespace sonic
}  // namespace p4rt_app
