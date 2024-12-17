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
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
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

  dvaas::MirrorTestbedConfigurator::Params testbed_config_params;
  if (GetParam()
          .validation_params.mirror_testbed_port_map_override.has_value()) {
    LOG(INFO)
        << "Using user-provided SUT<->CS P4RT port ID connection map override, "
           "assuming the arriba test vector uses a subset of SUT ports in the "
           "map";
    // TODO: Add a check instead of assuming.
    // The following is not strictly necessary because default parameter values
    // achieve the same thing. Making this explicit for ease of reading.
    testbed_config_params = {
        .p4rt_port_ids_to_configure = std::nullopt,
        .mirror_sut_ports_ids_to_control_switch = false,
    };
  } else {
    LOG(INFO) << "Configuring P4RT port IDs on SUT and mirroring to control "
                 "switch to match port IDs used in the test vector, assuming "
                 "ports with the same OpenConfig interface name are connected "
                 "to each other";
    testbed_config_params = {
        .p4rt_port_ids_to_configure = used_p4rt_port_ids,
        .mirror_sut_ports_ids_to_control_switch = true,
    };
  }

  ASSERT_OK(
      configured_testbed.ConfigureForForwardingTest(testbed_config_params));

  ASSERT_OK_AND_ASSIGN(
      dvaas::ValidationResult validation_result,
      dvaas::ValidateAgainstArribaTestVector(
          *configured_testbed.SutApi().p4rt,
          *configured_testbed.ControlSwitchApi().p4rt,
          GetParam().arriba_test_vector, GetParam().validation_params));

  EXPECT_OK(validation_result.HasSuccessRateOfAtLeast(
      GetParam().validation_params.expected_minimum_success_rate));

  ASSERT_OK(configured_testbed.RestoreToOriginalConfiguration());
}

}  // namespace
}  // namespace pins_test
