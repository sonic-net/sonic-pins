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

#include "p4_symbolic/symbolic/action.h"
#include "p4_symbolic/symbolic/operators.h"
#include "p4_symbolic/symbolic/util.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {
namespace conditional {

absl::StatusOr<SymbolicTrace> EvaluateConditional(
    const Dataplane data_plane, const ir::Conditional &conditional,
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

  // Evaluate both branches.
  ASSIGN_OR_RETURN(SymbolicTrace if_trace,
                   control::EvaluateControl(data_plane, conditional.if_branch(),
                                            state, translator, if_guard));
  ASSIGN_OR_RETURN(
      SymbolicTrace else_trace,
      control::EvaluateControl(data_plane, conditional.else_branch(), state,
                               translator, else_guard));

  // Now we have two traces that need merging.
  // We should merge in a way such that the value of a field in the trace is
  // the one from the if branch if the condition is true, and the else branch
  // otherwise.
  return util::MergeTracesOnCondition(condition, if_trace, else_trace);
}

}  // namespace conditional
}  // namespace symbolic
}  // namespace p4_symbolic
