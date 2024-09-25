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
#ifndef GOOGLE_P4_FUZZER_TEST_UTILS_H_
#define GOOGLE_P4_FUZZER_TEST_UTILS_H_

#include "absl/random/random.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_fuzzer/fuzzer_config.h"
#include "p4_fuzzer/switch_state.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/testing/test_p4info.h"
#include "sai_p4/instantiations/google/sai_p4info.h"

namespace p4_fuzzer {
// Captures the general state shared between most fuzzing functions for use in
// tests.
struct FuzzerTestState {
  absl::BitGen gen;
  FuzzerConfig config;
  SwitchState switch_state;
};

// Constructs a FuzzerTestState from an IrP4Info, only fuzzing tables with the
// given role.
FuzzerTestState ConstructFuzzerTestState(const pdpi::IrP4Info& ir_info,const std::string& role);

// Constructs a FuzzerTestState from a standard testing P4Info.
// By default, this test state should be used for all tests.
inline FuzzerTestState ConstructStandardFuzzerTestState() {
  return ConstructFuzzerTestState(pdpi::GetTestIrP4Info(), /*role=*/"");
}

// TODO: Deprecated. Do not use. New tests should not depend on a
// production P4 program. Old tests should be migrated to not rely on this
// function.
inline FuzzerTestState ConstructFuzzerTestStateFromSaiMiddleBlock() {
  return ConstructFuzzerTestState(
      sai::GetIrP4Info(sai::Instantiation::kMiddleblock),
      /*role=*/"sdn_controller");
}

// Helpers to get specific pieces of the IrP4Info.
// Gets a table that uses one-shot programming. Deterministic for a given
// IrP4Info.
absl::StatusOr<pdpi::IrTableDefinition> GetAOneShotTableDefinition(
    const pdpi::IrP4Info& info);

// Gets the Action Profile that implements the given table.
absl::StatusOr<pdpi::IrActionProfileDefinition>
GetActionProfileImplementingTable(const pdpi::IrP4Info& info,
                                  const pdpi::IrTableDefinition& table);

// Helpers to modify specific pieces of the IrP4Info.
void SetMaxGroupSizeInActionProfile(
    pdpi::IrP4Info& info, pdpi::IrActionProfileDefinition& action_profile,
    int max_group_size);
}  // namespace p4_fuzzer

#endif  // GOOGLE_P4_FUZZER_TEST_UTILS_H_
