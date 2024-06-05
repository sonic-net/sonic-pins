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

// Helpful utilities for managing symbolic and concrete headers and values.

#ifndef P4_SYMBOLIC_SYMBOLIC_UTIL_H_
#define P4_SYMBOLIC_SYMBOLIC_UTIL_H_

#include <string>
#include <unordered_map>

#include "google/protobuf/map.h"
#include "gutil/status.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/symbolic/values.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {
namespace util {

// Free (unconstrained) symbolic headers consisting of free symbolic variables
// for every field in every header instance defined in the P4 program.
absl::StatusOr<std::unordered_map<std::string, z3::expr>> FreeSymbolicHeaders(
    const google::protobuf::Map<std::string, ir::HeaderType> &headers);

// Returns an symbolic table match containing default values.
// The table match expression is false, the index is -1, and the value is
// undefined.
SymbolicTableMatch DefaultTableMatch();

// Extract a concrete context by evaluating every component's corresponding
// expression in the model.
absl::StatusOr<ConcreteContext> ExtractFromModel(
    SymbolicContext context, z3::model model,
    const values::P4RuntimeTranslator &translator);

// Merges two symbolic traces into a single trace. A field in the new trace
// has the value of the changed trace if the condition is true, and the value
// of the original one otherwise.
// Assertion: both traces must contain matches for the same set of table names.
absl::StatusOr<SymbolicTrace> MergeTracesOnCondition(
    const z3::expr &condition, const SymbolicTrace &true_trace,
    const SymbolicTrace &false_trace);

}  // namespace util
}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_UTIL_H_
