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

#ifndef PINS_DVAAS_ARRIBA_TEST_VECTOR_VALIDATION_H_
#define PINS_DVAAS_ARRIBA_TEST_VECTOR_VALIDATION_H_

#include <optional>
#include <vector>

#include "absl/container/btree_set.h"
#include "absl/status/statusor.h"
#include "dvaas/packet_injection.h"
#include "dvaas/port_id_map.h"
#include "dvaas/test_run_validation.h"
#include "dvaas/test_vector.pb.h"
#include "dvaas/validation_result.h"
#include "lib/p4rt/p4rt_port.h"
#include "p4_pdpi/p4_runtime_session.h"

namespace dvaas {

// Parameters for validating a testbed against an ArribaTestVector.
struct ArribaTestVectorValidationParams {
  // Parameters to control the comparison between the actual switch
  // output and the expected switch output per each input packet.
  SwitchOutputDiffParams switch_output_diff_params = {
      // TODO: Remove when it is possible to reliably validate
      // target egress port.
      .ignored_packet_in_metadata = {"target_egress_port"},
  };

  // Max number of packets to send per second. If no rate is given, the test
  // send packets as quickly as it can.
  // TODO: Increase default packet injection rate when rate
  // limites are disabled.
  std::optional<int> max_packets_to_send_per_second = 100;

  // Optionally, can be used to override the default assumption that each SUT
  // port is connected to a control switch port with the same OpenConfig
  // interface name.
  // NOTE: Not required for valid mirror testbeds. This is a workaround for
  // non-standard testbeds only.
  std::optional<MirrorTestbedP4rtPortIdMap> mirror_testbed_port_map_override;

  // Add the rate of packets expected to pass with the test. For new
  // implementations, this value may be less than 1, ie, not all the packets
  // pass. The value should be <= 1.0.
  double expected_minimum_success_rate = 1.0;

  // For a packet in from SUT or control switch without a test tag (i.e. an
  // "unsolicited packet"), if this function return false, packet injection
  // fails immediately.
  IsExpectedUnsolicitedPacketFunctionType is_expected_unsolicited_packet =
      DefaultIsExpectedUnsolicitedPacket;
};

// Retrieves the set of P4RT ports used in the given `arriba_test_vector` (table
// entries and test packet).
absl::StatusOr<absl::btree_set<pins_test::P4rtPortId>> GetUsedP4rtPortIds(
    const ArribaTestVector& arriba_test_vector,
    const pdpi::IrP4Info& ir_p4_info);

// Validates the `sut` in the provided mirror testbed (`sut` and
// `control_switch`) against the given `arriba_test_vector`. It does so by
// installing the entries in the test vector (on SUT), injecting the input
// packets, collecting the output packets, and comparing the results with
// the expected outputs for each input packet.
//
// Pre-condition:
//   - The same P4Info and gNMI configs used in the generation of the given
//     `arriba_test_vector` are pushed on SUT and the control switch.
//   - SUT interfaces are mirrored on the control switch.
//   - The interface on both switches are Up.
// TODO: Remove pre-conditions or add checks for them.
//
// Post-condition (on a successful run):
//   - Control switch contains entries to punt all packets.
//   - SUT constains the entries in arriba_test_vector.ir_entries.
absl::StatusOr<ValidationResult> ValidateAgainstArribaTestVector(
    pdpi::P4RuntimeSession& sut, pdpi::P4RuntimeSession& control_switch,
    const ArribaTestVector& arriba_test_vector,
    const ArribaTestVectorValidationParams& params = {});

} // namespace dvaas

#endif // PINS_DVAAS_ARRIBA_TEST_VECTOR_VALIDATION_H_
