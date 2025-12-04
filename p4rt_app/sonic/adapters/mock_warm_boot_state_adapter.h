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
#ifndef PINS_P4RT_APP_SONIC_ADAPTERS_MOCK_WARM_BOOT_STATE_ADAPTER_H_
#define PINS_P4RT_APP_SONIC_ADAPTERS_MOCK_WARM_BOOT_STATE_ADAPTER_H_

#include "p4rt_app/sonic/adapters/warm_boot_state_adapter.h"
#include "swss/warm_restart.h"
#include "gmock/gmock.h"

namespace p4rt_app {
namespace sonic {

class MockWarmBootStateAdapter : public WarmBootStateAdapter {
public:
  MOCK_METHOD(swss::WarmStart::WarmStartState, GetWarmBootState, (),
              (override));
  MOCK_METHOD(void, SetWarmBootState, (swss::WarmStart::WarmStartState state),
              (override));
  MOCK_METHOD(bool, IsWarmStart, (), (override));
  MOCK_METHOD(swss::WarmStart::WarmStartState, GetOrchAgentWarmBootState, (),
              (override));
};

} // namespace sonic
} // namespace p4rt_app

#endif // PINS_P4RT_APP_SONIC_ADAPTERS_MOCK_WARM_BOOT_STATE_ADAPTER_H_
