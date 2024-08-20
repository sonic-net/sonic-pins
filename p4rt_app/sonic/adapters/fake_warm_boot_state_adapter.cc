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

#include "swss/warm_restart.h"

namespace p4rt_app {
namespace sonic {

FakeWarmBootStateAdapter::FakeWarmBootStateAdapter() {}

swss::WarmStart::WarmStartState FakeWarmBootStateAdapter::GetWarmBootState() {
  return state_;
}

void FakeWarmBootStateAdapter::SetWarmBootState(
    swss::WarmStart::WarmStartState state) {
  state_ = state;
}

bool FakeWarmBootStateAdapter::IsWarmStart() { return is_warm_start_; }

void FakeWarmBootStateAdapter::SetWarmStart(bool is_warm_start) {
  is_warm_start_ = is_warm_start;
}

}  // namespace sonic
}  // namespace p4rt_app
