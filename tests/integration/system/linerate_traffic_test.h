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

// Contains tests for validating switch traffic forwarding. Traffic is sent at
// line rate (maximum speed of the Ixia) from one ingress port to one egress
// port on the switch.
//
// The tests rely on an Ixia to generate test packets at line rate.

#ifndef PINS_TESTS_INTEGRATION_SYSTEM_LINERATE_TRAFFIC_TEST_H_
#define PINS_TESTS_INTEGRATION_SYSTEM_LINERATE_TRAFFIC_TEST_H_

#include "p4/config/v1/p4info.pb.h"
#include "tests/qos/qos_test_util.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/generic_testbed_fixture.h"

namespace pins_test {

// Parameters used by the tests. The fixture is *not* parameterized over a gNMI
// config and assumes that the switch is preconfigured and the testbed ports
// are up.
struct LineRateTestParams {
  thinkit::GenericTestbedInterface* testbed_interface;
  p4::config::v1::P4Info p4info;
};

class LineRateTrafficTest : public testing::TestWithParam<LineRateTestParams> {
 protected:
  void SetUp() override { GetParam().testbed_interface->SetUp(); }
  void TearDown() override { GetParam().testbed_interface->TearDown(); }
  ~LineRateTrafficTest() override { delete GetParam().testbed_interface; }
};

}  // namespace pins_test

#endif  // PINS_TESTS_INTEGRATION_SYSTEM_LINERATE_TRAFFIC_TEST_H_
