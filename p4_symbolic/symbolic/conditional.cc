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

#include "p4_symbolic/symbolic/conditional.h"

#include <string>

#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "gutil/status.h"
#include "p4_symbolic/ir/ir.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesizer.pb.h"
#include "p4_symbolic/symbolic/action.h"
#include "p4_symbolic/symbolic/context.h"
#include "p4_symbolic/symbolic/control.h"
#include "p4_symbolic/symbolic/operators.h"
#include "p4_symbolic/symbolic/solver_state.h"
#include "p4_symbolic/symbolic/util.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {
namespace conditional {

absl::StatusOr<SymbolicTableMatches> EvaluateConditional(
    const ir::Conditional &conditional, SolverState &state,
    SymbolicPerPacketState &headers, const z3::expr &guard) {
  // Evaluate the condition.
  action::ActionContext fake_context = {conditional.name(), {}};
  ASSIGN_OR_RETURN(
      z3::expr condition,
      action::EvaluateRValue(conditional.condition(), headers, fake_context,
                             *state.context.z3_context));

  auto get_next_control_for_branch = [&](const std::string &branch) {
    return branch ==
                   conditional.optimized_symbolic_execution_info().merge_point()
               ? ir::EndOfPipeline()  // Do not jump to the merge point (yet).
               : branch;
  };

    SymbolicPerPacketState if_headers = headers;
  SymbolicPerPacketState else_headers = headers;

  // Evaluate both branches with its own copy of the headers.
  // We use `true` as the guard when evaluating the branches and the actual
  // guard is applied when merging the results of the two branches (see below).
  ASSIGN_OR_RETURN(
      SymbolicTableMatches if_matches,
      control::EvaluateControl(
          get_next_control_for_branch(conditional.if_branch()), state,
          if_headers, state.context.z3_context->bool_val(true)));
  ASSIGN_OR_RETURN(
      SymbolicTableMatches else_matches,
      control::EvaluateControl(
          get_next_control_for_branch(conditional.else_branch()), state,
          else_headers, state.context.z3_context->bool_val(true)));

  // Merge the information from the two branches for every field in the headers.
  // Merge is done based on the condition of the conditional.
  // The resulting headers map is then constructed with the merged values.
  for (const auto &[field, _] : headers) {
    ASSIGN_OR_RETURN(z3::expr if_value, if_headers.Get(field));
    ASSIGN_OR_RETURN(z3::expr else_value, else_headers.Get(field));
    ASSIGN_OR_RETURN(z3::expr new_value,
                     operators::Ite(condition, if_value, else_value));
    RETURN_IF_ERROR(headers.Set(field, new_value, guard));
  }

  // Now we have two traces that need merging.
  ASSIGN_OR_RETURN(
      SymbolicTableMatches merged_matches,
      util::MergeMatchesOnCondition(condition, if_matches, else_matches,
                                    *state.context.z3_context));

  if (!conditional.optimized_symbolic_execution_info()
           .continue_to_merge_point()) {
    // The merge point is guaranteed to be evaluated through a different path
    // (see go/optimized-symbolic-execution).
    return merged_matches;
  } else {
    // Jump to the merge point and continue the execution from there.
    ASSIGN_OR_RETURN(
        SymbolicTableMatches result,
        control::EvaluateControl(
            conditional.optimized_symbolic_execution_info().merge_point(),
            state, headers, guard));

    // Merge the result of execution from the merge point with the result of
    // merged if/else branches.
    return util::MergeDisjointTableMatches(merged_matches, result);
  }
}

// Evaluate conditional using DFS style symbolic execution.
// This is currently being used to generate packets for path coverage
// (go/p4-symbolic-path-coverage).
absl::Status EvaluateConditionalDfs(
    const ir::Conditional &conditional, SolverState &state,
    SymbolicPerPacketState &headers, const std::string &pipeline_name,
    packet_synthesizer::PacketSynthesisResults &results) {
  // Evaluate the condition.
  action::ActionContext fake_context = {conditional.name(), {}};
  ASSIGN_OR_RETURN(
      z3::expr condition,
      action::EvaluateRValue(conditional.condition(), headers, fake_context,
                             *state.context.z3_context));
  ASSIGN_OR_RETURN(z3::expr negated_condition, operators::Not(condition));

  // Evaluate the conditional by checking if the branch with condition == true
  // is satisfiable. If there does not exist any solution, this means that no
  // packet would take this path and the path can be pruned. Else, the path is
  // taken and the execution moves to the next control point. The same is
  // repeated for the branch with condition == false.

  // Check for "condition == true" branch.
  state.solver->push();
  state.solver->add(condition);
  auto prune = (state.solver->check() == z3::unsat);
  if (!prune) {
    auto if_headers = headers;
    RETURN_IF_ERROR(control::EvaluateControlDfs(
        conditional.if_branch(), state, if_headers, pipeline_name, results));
  }
  state.solver->pop();

  // Check for "condition == false",
  // i.e., "negated_condition == true" branch.
  state.solver->push();
  state.solver->add(negated_condition);
  prune = (state.solver->check() == z3::unsat);
  if (!prune) {
    auto else_headers = headers;
    RETURN_IF_ERROR(control::EvaluateControlDfs(conditional.else_branch(),
                                                state, else_headers,
                                                pipeline_name, results));
  }
  state.solver->pop();

  return absl::OkStatus();
}

}  // namespace conditional
}  // namespace symbolic
}  // namespace p4_symbolic
