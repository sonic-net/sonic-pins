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
#ifndef PINS_P4RT_APP_SONIC_ADAPTERS_WARM_BOOT_STATE_ADAPTER_H_
#define PINS_P4RT_APP_SONIC_ADAPTERS_WARM_BOOT_STATE_ADAPTER_H_

#include "swss/warm_restart.h"

namespace p4rt_app {
namespace sonic {
// Acts as a proxy to invoke swss common swss::WarmStart class methods.
// This provides the flexibility to define the constructors needed for mocks
// and fakes.
class WarmBootStateAdapter {
public:
  explicit WarmBootStateAdapter();
  virtual ~WarmBootStateAdapter() = default;
  // Get P4RT WarmBoot state.
  virtual swss::WarmStart::WarmStartState GetWarmBootState(void);
  // Set P4RT WarmBoot state.
  virtual void SetWarmBootState(swss::WarmStart::WarmStartState state);
  // Check if WarmStart is true.
  virtual bool IsWarmStart(void);
  // Get OrchAgent WarmBoot state.
  virtual swss::WarmStart::WarmStartState GetOrchAgentWarmBootState(void);
};

} // namespace sonic
} // namespace p4rt_app

#endif // PINS_P4RT_APP_SONIC_ADAPTERS_WARM_BOOT_STATE_ADAPTER_H_
