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

#include "tests/integration/system/nsf/interfaces/component_validator.h"
#include "tests/integration/system/nsf/interfaces/flow_programmer.h"
#include "tests/integration/system/nsf/interfaces/testbed.h"
#include "tests/integration/system/nsf/interfaces/traffic_helper.h"
#include "thinkit/ssh_client.h"

namespace pins_test {

// Struct to hold image label and config parameters to be injected in PINs NSF
// integration tests.
struct ImageConfigParams {
  std::string image_label;
  std::string gnmi_config;
  p4::config::v1::P4Info p4_info;
};

// Struct to hold test parameters to be injected in PINs NSF integration tests.
//
// Note that the `name` is used as the name of the instantiation of the
// parameterized NSF integration test.
struct NsfTestParams {
  std::string name;
  std::string test_case_id;
  std::vector<ImageConfigParams> image_config_params;
  std::function<std::unique_ptr<FlowProgrammer>()> create_flow_programmer;
  std::function<std::unique_ptr<TrafficHelper>()> create_traffic_helper;
  std::function<TestbedInterface()> create_testbed_interface;
  std::function<std::vector<std::unique_ptr<ComponentValidator>>()>
      create_component_validators;
  std::function<std::unique_ptr<thinkit::SSHClient>()> create_ssh_client;
  // TODO: This is a temporary workaround and
  // needs to be removed once the testbeds are ready.
  bool enable_interface_validation_during_nsf = true;
};

}  // namespace pins_test

#endif  // PINS_TESTS_INTEGRATION_SYSTEM_NSF_INTERFACES_TEST_PARAMS_H_
