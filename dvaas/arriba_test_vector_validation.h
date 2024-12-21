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

#include <vector>

#include "absl/container/flat_hash_set.h"
#include "absl/status/statusor.h"
#include "dvaas/test_run_validation.h"
#include "dvaas/test_vector.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "thinkit/mirror_testbed.h"

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
};

// Validates the `sut` in the provided mirror testbed (`sut` and
// `control_switch`) against the given `arriba_test_vector`. It does so by
// installing the entries in the test vector (on SUT), injecting the input
// packets, collecting the output packets, and comparing the results with the
// expected outputs for each input packet.
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
absl::Status ValidateAgaistArribaTestVector(
    pdpi::P4RuntimeSession &sut, pdpi::P4RuntimeSession &control_switch,
    const ArribaTestVector &arriba_test_vector,
    const ArribaTestVectorValidationParams &params = {});

} // namespace dvaas

#endif // PINS_DVAAS_ARRIBA_TEST_VECTOR_VALIDATION_H_
