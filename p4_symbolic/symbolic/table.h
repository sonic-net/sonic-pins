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

// Contains functions used to symbolically evaluate P4 tables and their entries.
// A table is turned into a sequence of if-conditions (one per entry),
// each condition corresponds to having that entry matched on, and the
// corresponding then body invokes the appropriate symbolic action expression
// with the parameters specified in the entry.

#ifndef P4_SYMBOLIC_SYMBOLIC_TABLE_H_
#define P4_SYMBOLIC_SYMBOLIC_TABLE_H_

#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesizer.pb.h"
#include "p4_symbolic/symbolic/context.h"
#include "p4_symbolic/symbolic/solver_state.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {
namespace table {

// Determines how table entries are prioritized based on the table match types.
enum class TableEntryPriorityType {
  kPositivePriority,           // The table has a range, ternary, or optional
                               // match, where the entry priority field must be
                               // positive.
  kPriorityZeroWithSingleLpm,  // The table has no range, ternary, or optional
                               // matches, and has exactly one LPM match with
                               // zero or more exact matches. The entry priority
                               // field must be zero and the prefix length of
                               // the LPM match must be positive.
  kPriorityZero,               // None of the above. (I.e., the table has only
                               // exact matches.) The entry priority field must
                               // be zero.
};

// P4-Symbolic models the default action as an entry with index -1.
constexpr int kDefaultActionEntryIndex = -1;

TableEntryPriorityType GetTableEntryPriorityType(const ir::Table &table);

absl::StatusOr<SymbolicTableMatches> EvaluateTable(
    const ir::Table &table, SolverState &state, SymbolicPerPacketState &headers,
    const z3::expr &guard);

// Evaluate Table using DFS style symbolic execution.
// This is currently being used to generate packets for path coverage
// (go/p4-symbolic-path-coverage).
absl::Status EvaluateTableDfs(
    const ir::Table &table, SolverState &state, SymbolicPerPacketState &headers,
    const std::string &pipeline_name,
    packet_synthesizer::PacketSynthesisResults &results);

}  // namespace table
}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_TABLE_H_
