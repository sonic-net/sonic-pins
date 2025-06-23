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

#ifndef PINS_TESTS_FORWARDING_MULTICAST_FALLBACK_GROUP_TEST_H_
#define PINS_TESTS_FORWARDING_MULTICAST_FALLBACK_GROUP_TEST_H_

#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "gtest/gtest.h"
#include "lib/gnmi/openconfig.pb.h"
#include "lib/p4rt/p4rt_port.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_infra/p4_runtime/p4_runtime_session.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "tests/forwarding/packet_test_util.h"
#include "thinkit/mirror_testbed_fixture.h"

namespace pins {

// Holds the common params needed for multicast fallback group test.
struct MulticastFallbackGroupTestParams {
  thinkit::MirrorTestbedInterface* testbed;
  // The test assumes that the switch is pre-configured if no `gnmi_config` is
  // given (default), or otherwise pushes the given config before starting.
  std::optional<std::string> gnmi_config;
  // P4Info to be used based on a specific instantiation.
  p4::config::v1::P4Info p4_info;
  // Optional function that checks the multicast fallback duration against the
  // threshold and exports the data to perfgate.
  absl::optional<std::function<absl::Status(absl::string_view chassis_name,
                                            absl::Duration pruning_duration)>>
      check_and_export_duration;
};

// MulticastFallbackGroupTestFixture for testing multicast fallback action.
class MulticastFallbackGroupTestFixture
    : public testing::TestWithParam<MulticastFallbackGroupTestParams> {
 protected:
  void SetUp() override;

  void TearDown() override;

  absl::Status SetUpSut(const pdpi::IrP4Info& ir_p4info);

  pdpi::IrP4Info ir_p4info_;
  std::string test_config_key_;
  TestData test_data_;
  std::unique_ptr<p4_runtime::P4RuntimeSession> sut_p4_session_;
  std::unique_ptr<p4_runtime::P4RuntimeSession> control_p4_session_;
  std::unique_ptr<gnmi::gNMI::StubInterface> sut_gnmi_stub_;
  std::unique_ptr<gnmi::gNMI::StubInterface> control_gnmi_stub_;
  std::vector<pins_test::P4rtPortId> controller_port_ids_;
  std::vector<std::string> replica_ports_;

  // Captures the control interfaces at the start of the test. These may be
  // changed during testing to mirror those of the SUT. They will then be
  // returned to their previous state during teardown.
  pins_test::openconfig::Interfaces original_control_interfaces_;
};

}  // namespace pins

#endif  // PINS_TESTS_FORWARDING_MULTICAST_FALLBACK_GROUP_TEST_H_
