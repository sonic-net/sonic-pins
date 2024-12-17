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

// Contains tests of the QoS features of the switch (rate limits,
// classification, scheduling) related to protecting the CPU from overload.
//
// Some tests rely on an Ixia to generate test packets at line rate.

#ifndef PINS_TESTS_CPU_QOS_TEST_H_
#define PINS_TESTS_CPU_QOS_TEST_H_

#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/generic_testbed_fixture.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/mirror_testbed_fixture.h"

namespace pins_test {

// Parameters used by the tests that don't require an Ixia.
struct ParamsForTestsWithoutIxia {
  thinkit::MirrorTestbedInterface* testbed_interface;
  std::string gnmi_config;
  p4::config::v1::P4Info p4info;
};

// Fixture of tests that do not require an Ixia. These test must be run on a
// testbed where the SUT is connected to a "control device" that can send and
// received packets.
class CpuQosTestWithoutIxia
    : public testing::TestWithParam<ParamsForTestsWithoutIxia> {
 protected:
  void SetUp() override {
    GetParam().testbed_interface->SetUp();

    // TODO: Port to thinkit::GenericTestbed.
    // // Pick a testbed where the SUT is connected to another device that can
    // send
    // // and receive packets.
    // ASSERT_OK_AND_ASSIGN(
    //     testbed_, GetParam().testbed_interface->GetTestbedWithRequirements(
    //                   gutil::ParseProtoOrDie<thinkit::TestRequirements>(R"pb(
    //                     interface_requirements {
    //                       interface_mode: CONTROL_INTERFACE
    //                       count: 1
    //                     }
    //                   )pb")));
    // ASSERT_OK_AND_ASSIGN(
    //     testbed_, GetParam().testbed_interface->GetMirrorTestbed());
  }

  thinkit::MirrorTestbed& Testbed() {
    return GetParam().testbed_interface->GetMirrorTestbed();
  }

  void TearDown() override { GetParam().testbed_interface->TearDown(); }

  ~CpuQosTestWithoutIxia() override { delete GetParam().testbed_interface; }

 private:
  std::unique_ptr<thinkit::MirrorTestbed> testbed_;
};

// Parameters used by the tests that require an Ixia.
struct ParamsForTestsWithIxia {
  thinkit::GenericTestbedInterface* testbed_interface;
  std::string gnmi_config;
  p4::config::v1::P4Info p4info;
  absl::optional<std::string> test_case_id;
  // This is be the minimum guaranteed bandwidth for control path to Tester in
  // the testbed. This is required to ensure the per queue rate limits to be
  // tested are within this guaranteed end to end bandwidth.
  int control_plane_bandwidth_bps;
};

class CpuQosTestWithIxia
    : public testing::TestWithParam<ParamsForTestsWithIxia> {
 protected:
  void SetUp() override { GetParam().testbed_interface->SetUp(); }

  void TearDown() override { GetParam().testbed_interface->TearDown(); }

  ~CpuQosTestWithIxia() override { delete GetParam().testbed_interface; }
};

}  // namespace pins_test
#endif  // PINS_TESTS_CPU_QOS_TEST_H_
