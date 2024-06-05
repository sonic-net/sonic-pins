// Copyright 2020 Google LLC
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

#include "gutil/status.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/symbolic/control.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/symbolic/values.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {
namespace conditional {

absl::StatusOr<SymbolicTrace> EvaluateConditional(
    const Dataplane data_plane, const ir::Conditional &conditional,
    SymbolicPerPacketState *state, values::P4RuntimeTranslator *translator,
    const z3::expr &guard);

}  // namespace conditional
}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_CONDITIONAL_H_
