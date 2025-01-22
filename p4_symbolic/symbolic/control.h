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
// The bmv2 format suggests it can also be a direct action call, but that is
// unsupported by our IR and this file, supporting it should be easy if the
// need arise.
//
// This file is responsible for evaluating that control on the current
// evaluation state (essentially an assignment of header fields to symbolic
// values).
//
// Evaluating the control (e.g. via table::EvaluateTable(...)) returns a suffix
// SymbolicTrace: a trace that contains new values to header fields, as well as,
// table matches, for the control that was evaluated, and all next controls
// evaluated after it. This file returns that suffix trace as is. It is the
// responsibility of the calling code to extend that suffix to cover previous
// controls.
//
// Note that the first call to this file will return a complete trace.
//
// Control evaluation functions (e.g. table::EvaluateTable(...)) are responsible
// for calling this file again on the next control constructs that should be
// evaluated after they are evaluated.
//
// Example:
// Table A is described in BMV2 JSON so that after it is matched, the next
// control is Table B, which has no next control.
// Our symbolic pipeline will call this file on table A, which calls
// EvaluateTable(A, ...), which will evaluate A, and then call this file again
// on table B, which then calls EvaluateTable(B, ...).
// EvaluateTable(B, ...) will return a suffix trace to this file, consisting of
// the header fields values after B is evaluated, as well as the symbolic match
// for B. Our file will return it to EvaluateTable(A, ...), which will add the
// symbolic match for table A to it, and then return it the very first call,
// resulting in a complete trace.
//
// Conditionals operate similarly, but instead of appending a symbolic match
// to the suffix trace, they call this file on two controls corresponding to
// the conditional's two branches, then merge the two suffixes using symbolic
// if-then-else on a symbolic condition equivalent to that conditional.

#ifndef P4_SYMBOLIC_SYMBOLIC_CONTROL_H_
#define P4_SYMBOLIC_SYMBOLIC_CONTROL_H_

#include <string>

#include "absl/status/statusor.h"
#include "p4_symbolic/symbolic/context.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {
namespace control {

// Evaluate the passed pipeline.
absl::StatusOr<SymbolicTableMatches> EvaluatePipeline(
    const std::string &pipeline_name, SolverState &state,
    SymbolicPerPacketState *headers, const z3::expr &guard);

// Evaluate the passed control construct.
absl::StatusOr<SymbolicTableMatches> EvaluateControl(
    const std::string &control_name, SolverState &state,
    SymbolicPerPacketState *headers, const z3::expr &guard);

} // namespace control
} // namespace symbolic
} // namespace p4_symbolic

#endif // P4_SYMBOLIC_SYMBOLIC_CONTROL_H_
