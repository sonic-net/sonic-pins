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

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "gtest/gtest.h"
#include "lib/gnmi/openconfig.pb.h"
#include "lib/p4rt/p4rt_port.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "tests/forwarding/packet_test_util.h"
#include "thinkit/mirror_testbed_fixture.h"

namespace pins {

// Holds the common params needed for multicast fallback group test.
struct MulticastFallbackGroupTestParams {
  thinkit::MirrorTestbedInterface* testbed;
  // The test assumes that the switch is pre-configured if no `gnmi_config` is
  // given (default), or otherwise pushes the given config before starting.
  std::optional<std::string> sut_config;
  std::optional<std::string> control_config;
  // P4Info to be used based on a specific instantiation
  p4::config::v1::P4Info sut_p4_info;
  p4::config::v1::P4Info control_p4_info;
  absl::flat_hash_map<std::string, std::string> control_to_sut_port_name_map;
  absl::flat_hash_map<pins_test::P4rtPortId, pins_test::P4rtPortId>
      control_to_sut_port_id_map;
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
  std::unique_ptr<pdpi::P4RuntimeSession> sut_p4_session_;
  std::unique_ptr<pdpi::P4RuntimeSession> control_p4_session_;
  std::unique_ptr<gnmi::gNMI::StubInterface> sut_gnmi_stub_;
  std::unique_ptr<gnmi::gNMI::StubInterface> control_gnmi_stub_;
  // The P4RT port IDs of the SUT interfaces.
  std::vector<pins_test::P4rtPortId> sut_port_ids_;
  // The P4RT port IDs of the control switch interfaces that are connected to
  // the SUT interfaces.
  std::vector<pins_test::P4rtPortId> control_port_ids_;
  // Replica ports for the multicast group on the SUT.
  std::vector<std::string> replica_ports_;
  // Replica ports for the multicast group on the SUT with the default port.
  std::vector<std::string> replica_ports_with_default_port_;
  // Replica ports for the multicast group on the control switch.
  std::vector<std::string> control_replica_ports_;
  // Map from SUT port ID to control switch port ID.
  absl::flat_hash_map<pins_test::P4rtPortId, pins_test::P4rtPortId>
      sut_to_control_port_id_map_;
  // Map from control switch port name to SUT port name.
  absl::flat_hash_map<std::string, std::string> control_to_sut_port_name_map_;
};

}  // namespace pins

#endif  // PINS_TESTS_FORWARDING_MULTICAST_FALLBACK_GROUP_TEST_H_
