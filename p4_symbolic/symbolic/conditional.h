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

// Contains functions used to symbolically evaluate P4 conditionals and their
// branches.

#ifndef P4_SYMBOLIC_SYMBOLIC_CONDITIONAL_H_
#define P4_SYMBOLIC_SYMBOLIC_CONDITIONAL_H_

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
namespace conditional {

absl::StatusOr<SymbolicTableMatches> EvaluateConditional(
    const ir::Conditional &conditional, SolverState &state,
    SymbolicPerPacketState &headers, const z3::expr &guard);

// Evaluate Conditional using DFS style symbolic execution.
// This is currently being used to generate packets for path coverage
// (go/p4-symbolic-path-coverage).
absl::Status EvaluateConditionalDfs(
    const ir::Conditional &conditional, SolverState &state,
    SymbolicPerPacketState &headers, const std::string &pipeline_name,
    packet_synthesizer::PacketSynthesisResults &results);

}  // namespace conditional
}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_CONDITIONAL_H_
