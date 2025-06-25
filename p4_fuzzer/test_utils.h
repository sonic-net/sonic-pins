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
#ifndef PINS_P4_FUZZER_TEST_UTILS_H_
#define PINS_P4_FUZZER_TEST_UTILS_H_

#include "absl/random/random.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_fuzzer/fuzzer_config.h"
#include "p4_fuzzer/switch_state.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/test_p4info.h"
#include "sai_p4/instantiations/google/sai_p4info.h"

namespace p4_fuzzer {
// Captures the general state shared between most fuzzing functions for use in
// tests.
struct FuzzerTestState {
  absl::BitGen gen;
  FuzzerConfig config;
  SwitchState switch_state;
};

// Constructs a FuzzerTestState from a P4Info, only fuzzing tables with the
// given role.
// The FuzzerConfig will initially:
// - Have mutation probability set to 0.
// - Have >1 available ports.
// - Have >1 available queues with varied names.
// - Use the given role.
// - Otherwise, be default.
absl::StatusOr<FuzzerTestState> ConstructFuzzerTestState(
    const p4::config::v1::P4Info& info, const std::string& role);

// Constructs a FuzzerTestState from a standard testing P4Info.
// By default, this test state should be used for all tests.
// See the function above for details about the resulting FuzzerConfig.
inline FuzzerTestState ConstructStandardFuzzerTestState() {
  return ConstructFuzzerTestState(pdpi::GetTestP4Info(), /*role=*/"").value();
}

// TODO: Deprecated. Do not use. New tests should not depend on a
// production P4 program. Old tests should be migrated to not rely on this
// function.
inline FuzzerTestState ConstructFuzzerTestStateFromSaiMiddleBlock() {
  return ConstructFuzzerTestState(
             sai::GetP4Info(sai::Instantiation::kMiddleblock),
             /*role=*/"sdn_controller")
      .value();
}

// Gets a MatchField of a given type from a table definition. Deterministic for
// a given IrP4Info.
absl::StatusOr<pdpi::IrMatchFieldDefinition>
GetAMatchFieldDefinitionWithMatchType(
    const pdpi::IrTableDefinition &table_definition,
    p4::config::v1::MatchField::MatchType match_type);

// Gets a table that has a field with the given match type. Deterministic for a
// given IrP4Info.
absl::StatusOr<pdpi::IrTableDefinition> GetATableDefinitionWithMatchType(
    const FuzzerTestState &fuzzer_state,
    p4::config::v1::MatchField::MatchType match_type);

// Helpers to get specific pieces of the IrP4Info.
// Gets a table that uses one-shot programming. Deterministic for a given
// IrP4Info.
absl::StatusOr<pdpi::IrTableDefinition>
GetAOneShotTableDefinition(const pdpi::IrP4Info &info);

// Gets the Action Profile that implements the given table.
absl::StatusOr<pdpi::IrActionProfileDefinition>
GetActionProfileImplementingTable(const pdpi::IrP4Info &info,
                                  const pdpi::IrTableDefinition &table);

// Helpers to modify specific pieces of the FuzzerConfig.
absl::Status SetMaxGroupSizeInActionProfile(FuzzerConfig &config,
                                            int action_profile_id,
                                            int max_group_size);

} // namespace p4_fuzzer

#endif // PINS_P4_FUZZER_TEST_UTILS_H_
