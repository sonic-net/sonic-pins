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
#include <vector>

#include "absl/container/btree_set.h"
#include "absl/log/log.h"
#include "dvaas/arriba_test_vector_validation.h"
#include "dvaas/mirror_testbed_config.h"
#include "dvaas/validation_result.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "lib/p4rt/p4rt_port.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4_infra/p4_pdpi/p4_runtime_session_extras.h"

namespace pins_test {
namespace {

TEST_P(ArribaTest, SwitchUnderTestPassesArribaTestVector) {
  testing::Test::RecordProperty("description", GetParam().description);

  ASSERT_OK_AND_ASSIGN(dvaas::MirrorTestbedConfigurator configured_testbed,
                       dvaas::MirrorTestbedConfigurator::Create(
                           &GetParam().mirror_testbed->GetMirrorTestbed()));

  std::vector<pdpi::IrTableEntry> used_entries_list(
      GetParam().arriba_test_vector.ir_table_entries().entries().begin(),
      GetParam().arriba_test_vector.ir_table_entries().entries().end());

  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info ir_p4_info,
                       pdpi::GetIrP4Info(*configured_testbed.SutApi().p4rt));

  ASSERT_OK_AND_ASSIGN(
      absl::btree_set<pins_test::P4rtPortId> used_p4rt_port_ids,
      GetUsedP4rtPortIds(GetParam().arriba_test_vector, used_entries_list,
                         ir_p4_info));
  LOG(INFO) << "Number of used P4rt port ids: " << used_p4rt_port_ids.size();

  ASSERT_OK(configured_testbed.ConfigureForForwardingTest({
      .p4rt_port_ids_to_configure = used_p4rt_port_ids,
      .mirror_sut_ports_ids_to_control_switch = true,
  }));

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
