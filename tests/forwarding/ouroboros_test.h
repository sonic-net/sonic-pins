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

#ifndef PINS_TESTS_FORWARDING_OUROBOROS_TEST_H_
#define PINS_TESTS_FORWARDING_OUROBOROS_TEST_H_

#include <limits>
#include <memory>
#include <optional>
#include <string>

#include "absl/time/time.h"
#include "dvaas/dataplane_validation.h"
#include "dvaas/test_vector.pb.h"
#include "gtest/gtest.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_fuzzer/fuzzer_config.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesizer.pb.h"
#include "thinkit/mirror_testbed_fixture.h"

namespace pins_test {

struct OuroborosTestParams {
  // -- Basic Settings ---------------------------------------------------------
  std::shared_ptr<thinkit::MirrorTestbedInterface> mirror_testbed;
  // If present, the test installs the provided config on SUT and control
  // switch.
  std::optional<p4::v1::ForwardingPipelineConfig> config;

  // A set of entities that will be installed on the SUT before initiating
  // the main loop of the test.
  pdpi::IrEntities initial_sut_entities;

  // Target time for the test to run. This should not include testbed setup and
  // teardown.
  absl::Duration target_test_time = absl::Minutes(55);
  // Maximum number of iterations of fuzzing and dataplane testing. The actual
  // number of executed iterations will depend on the time taken in each
  // iteration and the value of `target_test_time`.
  int max_iterations = std::numeric_limits<int>::max();

  // -- Switch State Generation Settings ---------------------------------------
  // We use P4-Fuzzer to generate switch state updates.
  p4_fuzzer::FuzzerConfig fuzzer_config;
  // The minimum number of switch state updates to generate per Ouroboros loop.
  int min_num_updates_per_loop = 200;

  // -- Result Validation Settings ---------------------------------------------
  // Validates the dataplane behavior. Uses a shared_ptr because test parameters
  // must be copyable and DataplaneValidator is not.
  std::shared_ptr<dvaas::DataplaneValidator> validator;
  // Specifies user-facing parameters of DVaaS. See
  // dvaas::DataplaneValidationParams documentation for more details.
  // NOTE: `get_artifact_header` gets overwritten to print additional
  // information per iteration.
  dvaas::DataplaneValidationParams dvaas_params;

  // -- Obscure, Usually Unneeded Settings -------------------------------------
  // The test assumes that the switch is pre-configured if no `gnmi_config` is
  // given (default), or otherwise pushes the given config before starting.
  std::optional<std::string> gnmi_config;
};

// The Ouroboros test is designed to test all dataplane behavior on the switch,
// in the limit.
// The test has four components which it runs in a loop:
// - It generates and sends updates to the switch.
// - It generates test packets based on the entries on the switch.
// - It sends these packets to the switch collecting the switch's outputs.
// - It validates that the switch's outputs are correct w.r.t. the P4 program
//   and the entries installed on the switch.
//
// See go/ouroboros for more details.
class OuroborosTest : public testing::TestWithParam<OuroborosTestParams> {
 protected:
  void SetUp() override { GetParam().mirror_testbed->SetUp(); }
  void TearDown() override { GetParam().mirror_testbed->TearDown(); }
};

}  // namespace pins_test

#endif  // PINS_TESTS_FORWARDING_OUROBOROS_TEST_H_
