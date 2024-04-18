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
#ifndef PINS_TESTS_FORWARDING_TIMESTAMPING_TEST_H_
#define PINS_TESTS_FORWARDING_TIMESTAMPING_TEST_H_

#include <memory>

#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gutil/status_matchers.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "thinkit/mirror_testbed_fixture.h"

namespace pins {

class TimestampingTestFixture : public thinkit::MirrorTestbedFixture {
 protected:
  void SetUp() override {
    thinkit::MirrorTestbedFixture::SetUp();
    LOG(INFO) << "Control switch: "
              << GetMirrorTestbed().ControlSwitch().ChassisName();
    LOG(INFO) << "SUT: " << GetMirrorTestbed().Sut().ChassisName();

    // Timestamping test assumes a gNMI config is already installed on the
    // switch.
    pins_test::PinsConfigView config{
        .p4info = p4_info(),
    };
    ASSERT_OK(pins_test::ConfigureSwitchPair(GetMirrorTestbed().Sut(), config,
                                             GetMirrorTestbed().ControlSwitch(),
                                             config));

    // Open gNMI and P4RT connections for the tests to use.
    ASSERT_OK_AND_ASSIGN(sut_p4rt_session_, pdpi::P4RuntimeSession::Create(
                                                GetMirrorTestbed().Sut()));
    ASSERT_OK_AND_ASSIGN(
        control_p4rt_session_,
        pdpi::P4RuntimeSession::Create(GetMirrorTestbed().ControlSwitch()));
    ASSERT_OK_AND_ASSIGN(sut_gnmi_stub_,
                         GetMirrorTestbed().Sut().CreateGnmiStub());
    ASSERT_OK_AND_ASSIGN(control_gnmi_stub_,
                         GetMirrorTestbed().ControlSwitch().CreateGnmiStub());

    ASSERT_OK_AND_ASSIGN(ir_p4info_, pdpi::CreateIrP4Info(p4_info()));
  }

  std::unique_ptr<gnmi::gNMI::StubInterface> sut_gnmi_stub_;
  std::unique_ptr<gnmi::gNMI::StubInterface> control_gnmi_stub_;
  std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt_session_;
  std::unique_ptr<pdpi::P4RuntimeSession> control_p4rt_session_;

  pdpi::IrP4Info ir_p4info_;
};

}  // namespace pins

#endif  // PINS_TESTS_FORWARDING_TIMESTAMPING_TEST_H_
