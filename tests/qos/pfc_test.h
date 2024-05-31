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

#include <memory>
#include <optional>
#include <string>

#include "absl/container/flat_hash_map.h"
#include "gtest/gtest.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "thinkit/generic_testbed_fixture.h"
#include "thinkit/ssh_client.h"

namespace pins_test {

// Parameters used by the pfc tests that require an Ixia.
struct ParamsForPfcTestsWithIxia {
  std::shared_ptr<thinkit::GenericTestbedInterface> testbed_interface;
  std::shared_ptr<thinkit::SSHClient> ssh_client_for_nsf;
  // If enabled, ensure pfc traffic is verified post NSF Reboot
  bool nsf_reboot;
  std::optional<p4::config::v1::P4Info> p4info;
  // `queue_by_dscp`: provides the dscp to queue name mapping for the test.
  std::optional<absl::flat_hash_map<int, std::string>> queue_by_dscp;
  // `queue_by_pfc_priority`: provides the pfc priority to queue name mapping
  // for the test.
  std::optional<absl::flat_hash_map<int, std::string>> queue_by_pfc_priority;
};

class PfcTestWithIxia
    : public testing::TestWithParam<ParamsForPfcTestsWithIxia> {
 protected:
  void SetUp() override { GetParam().testbed_interface->SetUp(); }

  void TearDown() override { GetParam().testbed_interface->TearDown(); }

  ~PfcTestWithIxia() = default;
};

}  // namespace pins_test

#endif  // PINS_TESTS_QOS_PFC_TEST_H_
