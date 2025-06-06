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

#ifndef PINS_TESTS_PUNT_QOS_TEST_H_
#define PINS_TESTS_PUNT_QOS_TEST_H_

#include "absl/strings/string_view.h"
#include "gtest/gtest.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4_infra/packetlib/packetlib.pb.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/generic_testbed_fixture.h"
#include "thinkit/ssh_client.h"

namespace pins_test {

// Parameters used by the tests that require an Ixia.
struct ParamsForTestsWithIxia {
  std::shared_ptr<thinkit::GenericTestbedInterface> testbed_interface;
  std::shared_ptr<thinkit::SSHClient> ssh_client_for_nsf;
  // If enabled, ensure punt traffic and QoS features are verified post NSF
  // Reboot and the traffic drop is within the expected NSF duration.
  bool nsf_reboot;
  p4::config::v1::P4Info p4info;

  // This is be the minimum guaranteed bandwidth for control path to Tester in
  // the testbed. This is required to ensure the per queue rate limits to be
  // tested are within this guaranteed end to end bandwidth.
  int control_plane_bandwidth_bytes_per_second;

  // Forwarding queues to be configured for flow.
  absl::string_view unicast_green_queue;
  absl::string_view unicast_red_queue;
  absl::string_view multicast_green_queue;
  absl::string_view multicast_red_queue;
};

struct IxiaSutLink {
  std::string ixia_tx_interface;
  std::string ixia_rx_interface;
  std::string ixia_mirror_interface;
  std::string ixia_mirror_backup_interface;
  std::string sut_tx_interface;
  std::string sut_rx_interface;
  std::string sut_mirror_interface;
  std::string sut_mirror_backup_interface;
};

class PuntQoSTestWithIxia
    : public testing::TestWithParam<ParamsForTestsWithIxia> {
 protected:
  std::string ixia_handle_;
  std::string ixia_traffic_handle_;
  std::string ixia_traffic_name_;
  std::unique_ptr<gnmi::gNMI::StubInterface> sut_gnmi_stub_;
  std::unique_ptr<pdpi::P4RuntimeSession> sut_p4_session_;
  std::string sut_gnmi_config_;
  std::unique_ptr<thinkit::GenericTestbed> generic_testbed_;
  absl::flat_hash_map<std::string, std::string> p4rt_id_by_interface_;
  IxiaSutLink ixia_sut_link_;

  void SetUp() override;

  void TearDown() override;
};

}  // namespace pins_test
#endif  // PINS_TESTS_PUNT_QOSTEST_H_
