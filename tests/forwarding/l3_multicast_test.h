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

#ifndef PINS_TESTS_FORWARDING_L3_MULTICAST_TEST_H_
#define PINS_TESTS_FORWARDING_L3_MULTICAST_TEST_H_

#include <memory>
#include <optional>

#include "dvaas/dataplane_validation.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status_matchers.h"  // IWYU pragma: keep
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_runtime/p4_runtime_session.h"
#include "thinkit/mirror_testbed_fixture.h"

namespace pins_test {

struct L3MulticastTestParams {
  // Using a shared_ptr because parameterized tests require objects to be
  // copyable.
  std::shared_ptr<thinkit::MirrorTestbedInterface> mirror_testbed;
  // The test assumes that the switch is pre-configured if no `gnmi_config` is
  // given (default), or otherwise pushes the given config before starting.
  std::optional<std::string> gnmi_config;
  std::optional<p4::config::v1::P4Info> p4info;
  std::shared_ptr<dvaas::DataplaneValidator> dvaas;
};

class L3MulticastTestFixture
    : public testing::TestWithParam<L3MulticastTestParams> {
 public:
  void SetUp() override;
  void TearDown() override { GetParam().mirror_testbed->TearDown(); }

 protected:
  // This test runs on a mirror testbed setup, but we only need to configure
  // the SUT.
  std::unique_ptr<p4_runtime::P4RuntimeSession> sut_p4rt_session_;
  pdpi::IrP4Info ir_p4info_;
};

}  // namespace pins_test
#endif  // PINS_TESTS_FORWARDING_L3_MULTICAST_TEST_H_
