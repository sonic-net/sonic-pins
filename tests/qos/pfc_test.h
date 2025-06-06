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
#ifndef PINS_TESTS_QOS_PFC_TEST_H_
#define PINS_TESTS_QOS_PFC_TEST_H_

#include <cstdint>
#include <memory>
#include <optional>
#include <string>

#include "absl/container/flat_hash_map.h"
#include "gtest/gtest.h"
#include "lib/ixia_helper.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4_infra/packetlib/packetlib.pb.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/generic_testbed_fixture.h"
#include "thinkit/ssh_client.h"

namespace pins_test {

// Structure represents SUTs connections to Ixia.
// The QoS tests expects 2 Ixia `ingress_links` connected to Ixia to which
// traffic will be injected in order to oversubscribe the single `egress_link`.
struct IxiaLinks {
  ixia::IxiaLink ingress_links[2];
  ixia::IxiaLink egress_link;
};

struct TrafficItem {
  std::string traffic_name;
  std::string traffic_item;
};

// Parameters used by the pfc tests that require an Ixia.
struct ParamsForPfcTestsWithIxia {
  std::shared_ptr<thinkit::GenericTestbedInterface> testbed_interface;
  std::shared_ptr<thinkit::SSHClient> ssh_client_for_nsf;
  // If enabled, ensure pfc traffic is verified post NSF Reboot
  bool nsf_reboot;
  std::optional<p4::config::v1::P4Info> p4info;
  // `dscp_by`: provides the dscp to queue name mapping for the test.
  std::optional<absl::flat_hash_map<std::string, int>> dscp_by_queue;
  // `queue_by_pfc_priority`: provides the pfc priority to queue name mapping
  // for the test.
  std::optional<absl::flat_hash_map<int, std::string>> queue_by_pfc_priority;
  // PFC deadlock detection time.
  absl::Duration deadlock_detection_time;
  // PFC deadlock restoration time.
  absl::Duration deadlock_restoration_time;
};

constexpr int kNumQueues = 8;

class PfcTestWithIxia
    : public testing::TestWithParam<ParamsForPfcTestsWithIxia> {
 protected:
  std::unique_ptr<thinkit::GenericTestbed> generic_testbed_;
  std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt_session_;
  pdpi::IrP4Info sut_ir_p4info_;
  std::unique_ptr<gnmi::gNMI::StubInterface> gnmi_stub_;
  std::string ixia_connection_reference_;
  int64_t port_speed_bytes_per_second_;
  IxiaLinks ixia_links_;
  TrafficItem main_traffic_;
  ixia::TrafficParameters main_traffic_parameters_;
  TrafficItem pfc_traffic_;
  ixia::TrafficParameters pfc_traffic_parameters_;
  std::string kInitialPfcRxEnable;

  void SetUp() override;

  void TearDown() override;

  ~PfcTestWithIxia() = default;
};

}  // namespace pins_test

#endif  // PINS_TESTS_QOS_PFC_TEST_H_
