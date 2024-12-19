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
#ifndef PINS_P4RT_APP_SONIC_ADAPTERS_FAKE_CONSUMER_NOTIFIER_ADAPTER_H_
#define PINS_P4RT_APP_SONIC_ADAPTERS_FAKE_CONSUMER_NOTIFIER_ADAPTER_H_

#include <stdint.h>

#include <string>
#include <vector>

#include "p4rt_app/sonic/adapters/consumer_notifier_adapter.h"
#include "p4rt_app/sonic/adapters/fake_sonic_db_table.h"

namespace p4rt_app {
namespace sonic {

// Fakes the OrchAgent response path behavior for SONiC DB table entries.
//
// Every write into an SONiC table is handled by the OrchAgent. The write can
// either succeed or fail. In the latter case a failed StatusCode should be
// returned by the fake.
class FakeConsumerNotifierAdapter final : public ConsumerNotifierAdapter {
public:
  explicit FakeConsumerNotifierAdapter(FakeSonicDbTable *sonic_db_table);

  // Not copyable or moveable.
  FakeConsumerNotifierAdapter(const FakeConsumerNotifierAdapter &) = delete;
  FakeConsumerNotifierAdapter &
  operator=(const FakeConsumerNotifierAdapter &) = delete;

  // Faked methods.
  bool WaitForNotificationAndPop(std::string &op, std::string &data,
                                 SonicDbEntryList &values,
                                 int64_t timeout_ms = 60000LL) override;

private:
  // The SONiC table maintains a list of notifications that this fake can
  // request.
  FakeSonicDbTable *sonic_db_table_; // No ownership.
};

} // namespace sonic
} // namespace p4rt_app

#endif // PINS_P4RT_APP_SONIC_ADAPTERS_FAKE_CONSUMER_NOTIFIER_ADAPTER_H_
