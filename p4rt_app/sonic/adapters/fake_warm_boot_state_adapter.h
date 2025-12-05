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
#ifndef PINS_P4RT_APP_SONIC_ADAPTERS_FAKE_WARM_BOOT_STATE_ADAPTER_H_
#define PINS_P4RT_APP_SONIC_ADAPTERS_FAKE_WARM_BOOT_STATE_ADAPTER_H_

#include "p4rt_app/sonic/adapters/warm_boot_state_adapter.h"
#include "swss/warm_restart.h"

namespace p4rt_app {
namespace sonic {

class FakeWarmBootStateAdapter final : public WarmBootStateAdapter {
public:
  explicit FakeWarmBootStateAdapter();
  swss::WarmStart::WarmStartState GetWarmBootState() override;
  void SetWarmBootState(swss::WarmStart::WarmStartState state) override;
  swss::WarmStart::WarmStartState GetOrchAgentWarmBootState(void) override;
  bool IsWarmStart(void) override;

  // Test-only accessors
  std::vector<swss::WarmStart::WarmStartState> GetWarmBootStateHistory();
  void SetWarmStart(bool is_warm_start);
  void SetWaitForUnfreeze(bool wait_for_unfreeze);
  void SetOrchAgentWarmBootState(swss::WarmStart::WarmStartState);

 private:
  // History of warm-boot states.
  std::vector<swss::WarmStart::WarmStartState> states_;
  bool is_warm_start_ = false;
  bool wait_for_unfreeze_ = false;
  swss::WarmStart::WarmStartState oa_state_ =
      swss::WarmStart::WarmStartState::WSUNKNOWN;
};

} // namespace sonic
} // namespace p4rt_app

#endif // PINS_P4RT_APP_SONIC_ADAPTERS_FAKE_WARM_BOOT_STATE_ADAPTER_H_
