// Copyright 2025 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#ifndef PINS_TESTS_FORWARDING_CONFIGURE_MIRROR_TESTBED_TEST_H_
#define PINS_TESTS_FORWARDING_CONFIGURE_MIRROR_TESTBED_TEST_H_

#include <string>

#include "p4/config/v1/p4info.pb.h"
#include "thinkit/mirror_testbed_fixture.h"

namespace pins {

struct ConfigureMirrorTestbedTestParams {
  std::shared_ptr<thinkit::MirrorTestbedInterface> mirror_testbed;
  // The test assumes that the switches are pre-configured if no gNMI or P4Info
  // is given (default), or otherwise pushes the given configs.
  std::optional<std::string> sut_gnmi_config;
  std::optional<std::string> control_switch_gnmi_config;
  std::optional<p4::config::v1::P4Info> sut_p4info;
  std::optional<p4::config::v1::P4Info> control_switch_p4info;
};

// Optionally pushes P4Info or gNMI to SUT and/or control switch.
// TODO: Remove when installation_test also pushes P4Info.
class ConfigureMirrorTestbedTestFixture
    : public testing::TestWithParam<ConfigureMirrorTestbedTestParams> {
 protected:
  void SetUp() override { GetParam().mirror_testbed->SetUp(); }
  void TearDown() override { GetParam().mirror_testbed->TearDown(); }
};

}  // namespace pins

#endif  // PINS_TESTS_FORWARDING_CONFIGURE_MIRROR_TESTBED_TEST_H_
