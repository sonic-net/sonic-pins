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
#ifndef PINS_TESTS_INTEGRATION_SYSTEM_NSF_NSF_ACL_FLOW_COVERAGE_TEST_H_
#define PINS_TESTS_INTEGRATION_SYSTEM_NSF_NSF_ACL_FLOW_COVERAGE_TEST_H_

#include <memory>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "gtest/gtest.h"
#include "tests/integration/system/nsf/interfaces/component_validator.h"
#include "tests/integration/system/nsf/interfaces/flow_programmer.h"
#include "tests/integration/system/nsf/interfaces/test_params.h"
#include "tests/integration/system/nsf/interfaces/testbed.h"
#include "tests/integration/system/nsf/interfaces/traffic_helper.h"
#include "thinkit/ssh_client.h"

namespace pins_test {

class NsfAclFlowCoverageTestFixture
    : public testing::TestWithParam<NsfTestParams> {
 protected:
  void SetUp() override;
  void TearDown() override;

  std::unique_ptr<FlowProgrammer> flow_programmer_;
  std::unique_ptr<TrafficHelper> traffic_helper_;
  TestbedInterface testbed_interface_;
  Testbed testbed_;
  std::vector<std::unique_ptr<ComponentValidator>> component_validators_;
  std::unique_ptr<thinkit::SSHClient> ssh_client_;
};

}  // namespace pins_test

#endif  // PINS_TESTS_INTEGRATION_SYSTEM_NSF_NSF_ACL_FLOW_COVERAGE_TEST_H_
