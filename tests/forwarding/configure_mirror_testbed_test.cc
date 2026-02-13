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

#include "tests/forwarding/configure_mirror_testbed_test.h"

#include "absl/log/log.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "tests/lib/switch_test_setup_helpers.h"

namespace pins {
namespace {

TEST_P(ConfigureMirrorTestbedTestFixture, ConfigureMirrorTestbedTest) {
  LOG(INFO) << "Pushing P4Info/gNMI to the control switch";
  ASSERT_OK(pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
                GetParam().mirror_testbed->GetMirrorTestbed().ControlSwitch(),
                GetParam().control_switch_gnmi_config,
                GetParam().control_switch_p4info)
                .status());

  LOG(INFO) << "Pushing P4Info/gNMI to the SUT";
  ASSERT_OK(pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
                GetParam().mirror_testbed->GetMirrorTestbed().Sut(),
                GetParam().sut_gnmi_config, GetParam().sut_p4info)
                .status());
}

}  // namespace
}  // namespace pins
