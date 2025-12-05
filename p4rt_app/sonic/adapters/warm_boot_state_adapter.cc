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
#include "p4rt_app/sonic/adapters/warm_boot_state_adapter.h"

#include <string>

#include "swss/warm_restart.h"

namespace p4rt_app {
namespace sonic {

WarmBootStateAdapter::WarmBootStateAdapter() {}

swss::WarmStart::WarmStartState WarmBootStateAdapter::GetWarmBootState() {
  swss::WarmStart::WarmStartState state;
  swss::WarmStart::getWarmStartState("p4rt", state);

  return state;
}

void WarmBootStateAdapter::SetWarmBootState(
    swss::WarmStart::WarmStartState state) {
  swss::WarmStart::setWarmStartState("p4rt", state);
}

bool WarmBootStateAdapter::IsWarmStart() {
  return swss::WarmStart::isWarmStart();
}

swss::WarmStart::WarmStartState
WarmBootStateAdapter::GetOrchAgentWarmBootState() {
  swss::WarmStart::WarmStartState state;
  swss::WarmStart::getWarmStartState("orchagent", state);

  return state;
}

}  // namespace sonic
}  // namespace p4rt_app
