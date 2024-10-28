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
// =============================================================================
// Handles p4-constraints support for the P4-Fuzzer.

#ifndef PINS_INFRA_P4_FUZZER_CONSTRAINTS_H_
#define PINS_INFRA_P4_FUZZER_CONSTRAINTS_H_

#include "absl/random/random.h"
#include "absl/status/statusor.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_fuzzer/fuzzer_config.h"
#include "p4_fuzzer/switch_state.h"
#include "p4_pdpi/ir.pb.h"

namespace p4_fuzzer {

// Checks whether a table uses P4-Constraints.
bool UsesP4Constraints(const pdpi::IrTableDefinition& table,
                       const FuzzerConfig& config);

// Checks whether a table uses P4-Constraints.
bool UsesP4Constraints(int table_id, const FuzzerConfig& config);

// Generates a valid table entry for a table that uses P4-Constraints. Fails if
// given a table for which `!UsesP4Constraints`.
absl::StatusOr<p4::v1::TableEntry> FuzzValidConstrainedTableEntry(
    const FuzzerConfig& config, const SwitchState& switch_state,
    const pdpi::IrTableDefinition& table, absl::BitGen& gen);

}  // namespace p4_fuzzer

#endif  // PINS_INFRA_P4_FUZZER_CONSTRAINTS_H_
