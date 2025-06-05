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

#ifndef PINS_TESTS_INTEGRATION_SYSTEM_NSF_INTERFACES_TEST_PARAMS_H_
#define PINS_TESTS_INTEGRATION_SYSTEM_NSF_INTERFACES_TEST_PARAMS_H_

#include <functional>
#include <memory>
#include <string>
#include <vector>

#include "sai_p4/instantiations/google/instantiations.h"
#include "tests/integration/system/nsf/interfaces/component_validator.h"
#include "tests/integration/system/nsf/interfaces/flow_programmer.h"
#include "tests/integration/system/nsf/interfaces/image_config_params.h"
#include "tests/integration/system/nsf/interfaces/scenario.h"
#include "tests/integration/system/nsf/interfaces/testbed.h"
#include "tests/integration/system/nsf/interfaces/traffic_helper.h"
#include "thinkit/ssh_client.h"

namespace pins_test {

// Struct to hold test parameters to be injected in PINs NSF integration tests.
//
// Note that the `name` is used as the name of the instantiation of the
// parameterized NSF integration test.
struct NsfTestParams {
  std::string name;
  std::vector<ImageConfigParams> image_config_params;
  std::function<std::unique_ptr<FlowProgrammer>()> create_flow_programmer;
  std::function<std::unique_ptr<TrafficHelper>()> create_traffic_helper;
  std::function<TestbedInterface()> create_testbed_interface;
  std::function<std::vector<std::unique_ptr<ComponentValidator>>()>
      create_component_validators;
  std::function<std::unique_ptr<thinkit::SSHClient>()> create_ssh_client;
  std::function<std::vector<std::string>(NsfUpgradeScenario)> get_test_case_ids;
  bool enable_interface_validation_during_nsf = true;
  bool enable_dynamic_replay = false;
  sai::Instantiation sut_instantiation = sai::Instantiation::kTor;
};

}  // namespace pins_test

#endif  // PINS_TESTS_INTEGRATION_SYSTEM_NSF_INTERFACES_TEST_PARAMS_H_
