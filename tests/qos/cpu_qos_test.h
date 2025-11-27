// Copyright 2025 Google LLC
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

#include <functional>
#include <vector>

#include "absl/strings/string_view.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "p4_pdpi/netaddr/mac_address.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/generic_testbed_fixture.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/mirror_testbed_fixture.h"
#include "thinkit/ssh_client.h"

namespace pins_test {
// Structure holds packet and expected target queue passed in to test as
// parameter.
struct PacketAndExpectedTargetQueue {
  absl::string_view packet_name;
  packetlib::Packet packet;
  absl::string_view target_queue;
};

// Parameters used by the tests that don't require an Ixia.
struct ParamsForTestsWithoutIxia {
  // Using a shared_ptr because parameterized tests require objects to be
  // copyable.
  std::shared_ptr<thinkit::MirrorTestbedInterface> testbed_interface;
  std::shared_ptr<thinkit::SSHClient> ssh_client_for_nsf;
  // If enabled, ensure punt traffic and QoS features are verified post NSF
  // Reboot and the traffic drop is within the expected NSF duration.
  bool nsf_reboot;
  // The test assumes that the switch is pre-configured if no `gnmi_config` is
  // given (default), or otherwise pushes the given config before starting.
  std::optional<std::string> gnmi_config;
  p4::config::v1::P4Info p4info;
  // Function to generate test packets and expected target queue passed into the
  // test for verification.
  std::function<std::vector<PacketAndExpectedTargetQueue>(
      absl::string_view gnmi_config,
      std::optional<sai::Instantiation> instantiation)>
      test_packet_generator_function;
  bool is_rate_mode_in_packets = true;  // If true, the rate limit is in packets
                                        // per second.
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
  thinkit::Switch& Sut() { return Testbed().Sut(); }
  thinkit::Switch& ControlSwitch() { return Testbed().ControlSwitch(); }

  void TearDown() override { GetParam().testbed_interface->TearDown(); }
};

// Reference for the ACL QoS table actions and attributes can be found in:

// ACL Ingress tables
constexpr absl::string_view kAclIngressTable = "acl_ingress_table";
constexpr absl::string_view kAclIngressQosTable = "acl_ingress_qos_table";

// ACL Ingress table actions.
constexpr absl::string_view kAclTrap = "acl_trap";
constexpr absl::string_view kAclCopy = "acl_copy";

// ACL Ingress QoS table actions.
constexpr absl::string_view kAclSetCpuQueueAndCancelCopyAboveRateLimit =
    "set_qos_queue_and_cancel_copy_above_rate_limit";
constexpr absl::string_view kAclSetCpuQueueAndDenyAboveRateLimit =
    "set_cpu_queue_and_deny_above_rate_limit";
constexpr absl::string_view kAclSetCpuQueueMulticastQueueAndDenyAboveRateLimit =
    "set_cpu_queue_multicast_queue_and_deny_above_rate_limit";

// ACL punt queue attribute name.
constexpr absl::string_view kCpuQosQueueAttributeName = "qos_queue";
constexpr absl::string_view kCpuQueueAttributeName = "cpu_queue";

struct AclIngressTablePuntFlowRateLimitAction {
  absl::string_view rate_limit_action;
  absl::string_view cpu_queue_attribute_name;
};

// Parameters used by the tests that require an Ixia.
struct ParamsForTestsWithIxia {
  thinkit::GenericTestbedInterface* testbed_interface;
  std::shared_ptr<thinkit::SSHClient> ssh_client_for_nsf;
  // If enabled, ensure punt traffic and QoS features are verified post NSF
  // Reboot and the traffic drop is within the expected NSF duration.
  bool nsf_reboot;
  p4::config::v1::P4Info p4info;
  // Number of pipes supported by Vendor across which the Buffer is split.
  int num_pipes;
  // This is be the minimum guaranteed bandwidth for control path to Tester in
  // the testbed. This is required to ensure the per queue rate limits to be
  // tested are within this guaranteed end to end bandwidth.
  int control_plane_bandwidth_bytes_per_second;

  // Optionally verify configuration on switch against expected queue rate limit
  // parameters. The Map holds queue names as keys and the expected rate limit
  // in "packets per second" for the queue as value.
  // When this parameter is passed in, the test will verify configuration on
  // switch matches expected config.
  absl::flat_hash_map<std::string, int> expected_queue_limit_config_pps;

  // Vector of actions to verify for Punt flow rate limit test.
  const std::vector<AclIngressTablePuntFlowRateLimitAction>
      acl_ingress_table_punt_flow_rate_limit_actions;
  bool is_rate_mode_in_packets = true;

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
