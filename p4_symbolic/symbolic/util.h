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

// Helpful utilities for managing symbolic and concrete headers and values.

#ifndef P4_SYMBOLIC_SYMBOLIC_UTIL_H_
#define P4_SYMBOLIC_SYMBOLIC_UTIL_H_

#include <string>

#include "absl/container/btree_map.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "google/protobuf/map.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/symbolic/values.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {
namespace util {

// Free (unconstrained) symbolic headers consisting of free symbolic variables
// for every field in every header instance defined in the P4 program.
absl::StatusOr<absl::btree_map<std::string, z3::expr>> FreeSymbolicHeaders(
    const google::protobuf::Map<std::string, ir::HeaderType> &headers);

// Returns an symbolic table match containing default values.
// The table match expression is false, the index is -1, and the value is
// undefined.
SymbolicTableMatch DefaultTableMatch();

// Extract a concrete context by evaluating every component's corresponding
// expression in the model.
absl::StatusOr<ConcreteContext> ExtractFromModel(
    const SymbolicContext &context, z3::model model,
    const values::P4RuntimeTranslator &translator);

// Merges two maps of table matches into a single map. A field in the returned
// map has the value of `true_matches` if the condition is true, and the
// value of `false_matches` otherwise.
// The two maps must contain disjoint keys, otherwise an error is returned.
absl::StatusOr<SymbolicTableMatches>
MergeMatchesOnCondition(const z3::expr &condition,
                        const SymbolicTableMatches &true_matches,
                        const SymbolicTableMatches &false_matches);

// Merges two maps of table matches into a single map. The two maps must contain
// disjoint keys, otherwise an error is returned.
absl::StatusOr<SymbolicTableMatches>
MergeDisjointTableMatches(const SymbolicTableMatches &lhs,
                          const SymbolicTableMatches &rhs);

// Extracts the bit-width of the field with name `field_name` in the given
// `program`.
absl::StatusOr<int> GetFieldBitwidth(absl::string_view field_name,
                                     const ir::P4Program &program);

} // namespace util
} // namespace symbolic
} // namespace p4_symbolic

#endif // P4_SYMBOLIC_SYMBOLIC_UTIL_H_
