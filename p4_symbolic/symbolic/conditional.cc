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

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "gutil/status.h"
#include "p4_symbolic/ir/ir.h"
#include "p4_symbolic/symbolic/action.h"
#include "p4_symbolic/symbolic/operators.h"
#include "p4_symbolic/symbolic/util.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {
namespace conditional {

absl::StatusOr<SymbolicTableMatches> EvaluateConditional(
    const Dataplane &data_plane, const ir::Conditional &conditional,
    SymbolicPerPacketState *state, values::P4RuntimeTranslator *translator,
    const z3::expr &guard) {
  // Evaluate the condition.
  action::ActionContext fake_context = {conditional.name(), {}};
  ASSIGN_OR_RETURN(
      z3::expr condition,
      action::EvaluateRValue(conditional.condition(), *state, fake_context));
  ASSIGN_OR_RETURN(z3::expr negated_condition, operators::Not(condition));

  // Build new guards for each branch.
  ASSIGN_OR_RETURN(z3::expr if_guard, operators::And(guard, condition));
  ASSIGN_OR_RETURN(z3::expr else_guard,
                   operators::And(guard, negated_condition));

  auto get_next_control_for_branch = [&](const std::string &branch) {
    return branch ==
                   conditional.optimized_symbolic_execution_info().merge_point()
               ? ir::EndOfPipeline()  // Do not jump to the merge point (yet).
               : branch;
  };

  // Evaluate both branches.
  ASSIGN_OR_RETURN(
      SymbolicTableMatches if_matches,
      control::EvaluateControl(
          data_plane, get_next_control_for_branch(conditional.if_branch()),
          state, translator, if_guard));
  ASSIGN_OR_RETURN(
      SymbolicTableMatches else_matches,
      control::EvaluateControl(
          data_plane, get_next_control_for_branch(conditional.else_branch()),
          state, translator, else_guard));

  // Now we have two traces that need merging. The two traces are guaranteed to
  // contain different table matches (see go/optimized-symbolic-execution).
  ASSIGN_OR_RETURN(SymbolicTableMatches merged_matches,
                   util::MergeDisjointTableMatches(if_matches, else_matches));

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
            data_plane,
            conditional.optimized_symbolic_execution_info().merge_point(),
            state, translator, guard));

    // Merge the result of execution from the merge point with the result of
    // merged if/else branches.
    return util::MergeDisjointTableMatches(merged_matches, result);
  }
}

}  // namespace conditional
}  // namespace symbolic
}  // namespace p4_symbolic
