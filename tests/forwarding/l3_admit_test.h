// Copyright 2024 Google LLC
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
#ifndef PINS_TESTS_FORWARDING_L3_ADMIT_TEST_H_
#define PINS_TESTS_FORWARDING_L3_ADMIT_TEST_H_

#include <memory>
#include <optional>
#include <tuple>

#include "gutil/status_matchers.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "thinkit/mirror_testbed_fixture.h"
#include "gmock/gmock.h"

namespace pins {

struct L3AdmitTestParams {
  thinkit::MirrorTestbedInterface *testbed_interface;
  p4::config::v1::P4Info p4info;
};

// This test assumes that the switch is set up with a gNMI config.
class L3AdmitTestFixture : public testing::TestWithParam<L3AdmitTestParams> {
protected:
  void SetUp() override {
    GetParam().testbed_interface->SetUp();

    // Initialize the connection and clear table entries for the SUT and Control
    // switch.
    ASSERT_OK_AND_ASSIGN(
        std::tie(sut_p4rt_session_, control_switch_p4rt_session_),
        pins_test::ConfigureSwitchPairAndReturnP4RuntimeSessionPair(
            GetParam().testbed_interface->GetMirrorTestbed().Sut(),
            GetParam().testbed_interface->GetMirrorTestbed().ControlSwitch(),
            /*gnmi_config=*/std::nullopt, GetParam().p4info));

    ASSERT_OK_AND_ASSIGN(ir_p4info_, pdpi::CreateIrP4Info(GetParam().p4info));
  }

  void TearDown() override { GetParam().testbed_interface->TearDown(); }

  ~L3AdmitTestFixture() override { delete GetParam().testbed_interface; }

  // This test runs on a mirror testbed setup so we open a P4RT connection to
  // both switches.
  std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt_session_;
  std::unique_ptr<pdpi::P4RuntimeSession> control_switch_p4rt_session_;

  pdpi::IrP4Info ir_p4info_;
};

} // namespace pins

#endif // PINS_TESTS_FORWARDING_L3_ADMIT_TEST_H_
