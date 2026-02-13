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

// Utility functions to determine if the switch is behaving correctly.  The main
// function takes a WriteRequest and a list of statuses, and returns whether
// that behavior is allowed by the switch according to the P4/P4RT
// specification.
#ifndef P4_FUZZER_ORACLE_UTIL_H_
#define P4_FUZZER_ORACLE_UTIL_H_

#include <string>
#include <vector>

#include "absl/types/span.h"
#include "gutil/status.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_fuzzer/fuzzer.pb.h"
#include "p4_fuzzer/switch_state.h"
#include "p4_pdpi/ir.pb.h"

namespace p4_fuzzer {

// An update and it's corresponding status.
struct UpdateStatus {
  AnnotatedUpdate update;
  pdpi::IrUpdateStatus status;
};

// An update with an index and it's corresponding status.
struct IndexUpdateStatus {
  int index;
  AnnotatedUpdate update;
  pdpi::IrUpdateStatus status;
};

// Is the given update well-formed according to the P4RT specification (e.g.,
// not missing a field)?
absl::Status IsWellformedUpdate(const pdpi::IrP4Info &ir_p4_info,
                                const p4::v1::Update &update);

// Is `status` a correct way to respond to the given update, when the switch is
// the given state?
absl::Status UpdateOracle(const pdpi::IrP4Info &ir_p4_info,
                          const p4::v1::Update &update,
                          const pdpi::IrUpdateStatus &status,
                          const SwitchState &state);

// Takes a batch and checks whether the way the switch responded is legal.  For
// now, batches are processed in sequence.  Returns nullopt if everything is
// valid, and a list of problems otherwise.
absl::optional<std::vector<std::string>>
WriteRequestOracle(const pdpi::IrP4Info &ir_p4_info,
                   const AnnotatedWriteRequest &request,
                   const absl::Span<const pdpi::IrUpdateStatus> &statuses,
                   const SwitchState &state);

} // namespace p4_fuzzer

#endif // P4_FUZZER_ORACLE_UTIL_H_
