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

// This file is responsible for evaluating a control construct in a P4
// program flow. A control construct could be a table match or a conditional
// leading to a table match.
//
// Check the header file for a detailed explanation.

#include "p4_symbolic/symbolic/control.h"

#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "gutil/status.h"
#include "p4_symbolic/ir/ir.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/symbolic/conditional.h"
#include "p4_symbolic/symbolic/context.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/symbolic/table.h"
#include "z3++.h"

namespace p4_symbolic::symbolic::control {

absl::StatusOr<SymbolicTableMatches> EvaluatePipeline(
    const std::string &pipeline_name, SolverState &state,
    SymbolicPerPacketState *headers, const z3::expr &guard) {
  if (auto it = state.program.pipeline().find(pipeline_name);
      it != state.program.pipeline().end()) {
    return EvaluateControl(it->second.initial_control(), state, headers, guard);
  }
  return gutil::InvalidArgumentErrorBuilder()
         << "cannot evaluate unknown pipeline: '" << pipeline_name << "'";
}

absl::StatusOr<SymbolicTableMatches> EvaluateControl(
    const std::string &control_name, SolverState &state,
    SymbolicPerPacketState *headers, const z3::expr &guard) {
  // Base case: we got to the end of the evaluation, no more controls!
  if (control_name == ir::EndOfPipeline()) return SymbolicTableMatches();

  // Find out what type of control we need to evaluate.
  if (state.program.tables().contains(control_name)) {
    // Table: call EvaluateTable on table and its entries.
    const ir::Table &table = state.program.tables().at(control_name);
    return table::EvaluateTable(table, state, headers, guard);
  } else if (state.program.conditionals().contains(control_name)) {
    // Conditional: let EvaluateConditional handle it.
    const ir::Conditional &conditional =
        state.program.conditionals().at(control_name);
    return conditional::EvaluateConditional(conditional, state, headers, guard);
  } else {
    // Something else: unsupported.
    return absl::UnimplementedError(
        absl::StrCat("Unsupported control \"", control_name,
                     "\" is neither a table nor a conditional"));
  }
}

}  // namespace p4_symbolic::symbolic::control
