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
#ifndef PINS_TESTS_INTEGRATION_SYSTEM_NSF_NSF_DYNAMIC_STATE_UPDATE_TEST_H_
#define PINS_TESTS_INTEGRATION_SYSTEM_NSF_NSF_DYNAMIC_STATE_UPDATE_TEST_H_

#include <memory>

#include "thinkit/generic_testbed_fixture.h"
#include "thinkit/ssh_client.h"

namespace pins_test {

struct NsfDynamicStateUpdateTestParams {
  std::shared_ptr<thinkit::SSHClient> ssh_client;
  std::shared_ptr<thinkit::GenericTestbedInterface> generic_testbed;
};

class NsfDynamicStateUpdateTestFixture
    : public testing::TestWithParam<NsfDynamicStateUpdateTestParams> {
 protected:
  void SetUp() override { GetParam().generic_testbed->SetUp(); }
  void TearDown() override { GetParam().generic_testbed->TearDown(); }
};

}  // namespace pins_test

#endif  // PINS_TESTS_INTEGRATION_SYSTEM_NSF_NSF_DYNAMIC_STATE_UPDATE_TEST_H_
