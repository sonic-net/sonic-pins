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

#include "tests/forwarding/arriba_test.h"

#include <cassert>
#include <optional>
#include <vector>

#include "absl/container/btree_set.h"
#include "absl/log/log.h"
#include "absl/strings/str_join.h"
#include "dvaas/arriba_test_vector_validation.h"
#include "dvaas/mirror_testbed_config.h"
#include "dvaas/validation_result.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "lib/p4rt/p4rt_port.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/p4_runtime_session_extras.h"

namespace pins_test {
namespace {

TEST_P(ArribaTest, SwitchUnderTestPassesArribaTestVector) {
  testing::Test::RecordProperty("description", GetParam().description);

  ASSERT_OK_AND_ASSIGN(dvaas::MirrorTestbedConfigurator configured_testbed,
                       dvaas::MirrorTestbedConfigurator::Create(
                           &GetParam().mirror_testbed->GetMirrorTestbed()));

  // Get the set of P4RT port IDs used in the test vector.
  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info ir_p4_info,
                       pdpi::GetIrP4Info(*configured_testbed.SutApi().p4rt));
  ASSERT_OK_AND_ASSIGN(
      absl::btree_set<pins_test::P4rtPortId> used_p4rt_port_ids,
      GetUsedP4rtPortIds(GetParam().arriba_test_vector, ir_p4_info));
  LOG(INFO) << used_p4rt_port_ids.size()
            << " P4RT port IDs used in the test vector: "
            << absl::StrJoin(used_p4rt_port_ids, ", ");
  // The CPU port in PINS has a special P4RT port ID. Given that the test
  // modifies the P4RT port ID of interfaces to match the IDs used in the
  // test vector, we remove the CPU port ID from the list of used port IDs to
  // avoid using this special ID on other interfaces.
  // TODO: Change when PINS uses better CPU port encoding.
  ASSERT_OK_AND_ASSIGN(
      const auto kCpuPortP4rtId,
      pins_test::P4rtPortId::MakeFromP4rtEncoding("4294967293"));
  if (used_p4rt_port_ids.erase(kCpuPortP4rtId) > 0) {
    LOG(INFO) << "Removing the special CPU port P4RT port ID ("
              << kCpuPortP4rtId.GetP4rtEncoding()
              << ") from the list of used port IDs to avoid configuring "
                 "non-CPU ports with it.";
  }


  // Check for explicit port map.
  const bool explicit_port_map =
      GetParam().validation_params.mirror_testbed_port_map_override.has_value();
  if (explicit_port_map) {
    LOG(INFO) << "Using the explicitly provided SUT<->CS port ID map to infer "
                 "connectivity.";
  } else {
    LOG(INFO) << "Assuming ports with the same OpenConfig interface names on "
                 "SUT and CS are connected to each other as no explicit port "
                 "map is provided.";
  }

  // Configure the testbed.
  ASSERT_OK(configured_testbed.ConfigureForForwardingTest({
      .p4rt_port_ids_to_configure = used_p4rt_port_ids,
      .mirror_sut_ports_ids_to_control_switch = !explicit_port_map,
      .original_port_map =
          GetParam().validation_params.mirror_testbed_port_map_override,
  }));

  dvaas::ArribaTestVectorValidationParams validation_params =
      GetParam().validation_params;
  // Update the port ID map in the validation params (if explicit).
  if (explicit_port_map) {
    ASSERT_OK_AND_ASSIGN(validation_params.mirror_testbed_port_map_override,
                         configured_testbed.GetConfiguredPortMap());
  }

  // Run the validation.
  ASSERT_OK_AND_ASSIGN(dvaas::ValidationResult validation_result,
                       dvaas::ValidateAgainstArribaTestVector(
                           *configured_testbed.SutApi().p4rt,
                           *configured_testbed.ControlSwitchApi().p4rt,
                           GetParam().arriba_test_vector, validation_params));
  validation_result.RecordStatisticsAsTestProperties();

  EXPECT_OK(validation_result.HasSuccessRateOfAtLeast(
      validation_params.expected_minimum_success_rate));

  // Restore testbed configuration.
  ASSERT_OK(configured_testbed.RestoreToOriginalConfiguration());
}

}  // namespace
}  // namespace pins_test
