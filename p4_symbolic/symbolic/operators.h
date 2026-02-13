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

// Defines a wrapper around z3 c++ API operators.
// The wrappers ensure sort compatibility, and pad bitvectors when needed, and
// automatically convert between bool and bit<1>.
// Additionally, they use absl::Status to convey sort compatibility failures
// instead of runtime crashes.

#ifndef P4_SYMBOLIC_SYMBOLIC_OPERATORS_H_
#define P4_SYMBOLIC_SYMBOLIC_OPERATORS_H_

#include <string>

#include "gutil/status.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {
namespace operators {

// Check that the two expressions have compatible sorts, and return an absl
// error otherwise. If the expressions are bitvector, the shortest will be
// padded to match the longest.
absl::StatusOr<std::pair<z3::expr, z3::expr>> SortCheckAndPad(
    const z3::expr &a, const z3::expr &b);

// If both `target` and `value` are bit-vectors, truncates the given `value` to
// the same size as the given `target` if `value` is longer, retaining the least
// significant bits. Otherwise this function has no effect. For example, if
// `value` is 0x0042 and `target` has only 8 bits, `value` becomes 0x42.
absl::Status TruncateBitVectorToFit(const z3::expr &target, z3::expr &value);

// Free variable.
absl::StatusOr<z3::expr> FreeVariable(const std::string &variable_base_name,
                                      const z3::sort &sort);

// Arithmetic operations.
absl::StatusOr<z3::expr> Plus(const z3::expr &a, const z3::expr &b);
absl::StatusOr<z3::expr> Minus(const z3::expr &a, const z3::expr &b);
absl::StatusOr<z3::expr> Times(const z3::expr &a, const z3::expr &b);

// Relational operations.
absl::StatusOr<z3::expr> Eq(const z3::expr &a, const z3::expr &b);
absl::StatusOr<z3::expr> Neq(const z3::expr &a, const z3::expr &b);
absl::StatusOr<z3::expr> Lt(const z3::expr &a, const z3::expr &b);
absl::StatusOr<z3::expr> Lte(const z3::expr &a, const z3::expr &b);
absl::StatusOr<z3::expr> Gt(const z3::expr &a, const z3::expr &b);
absl::StatusOr<z3::expr> Gte(const z3::expr &a, const z3::expr &b);

// Boolean operations.
absl::StatusOr<z3::expr> Not(const z3::expr &a);
absl::StatusOr<z3::expr> And(const z3::expr &a, const z3::expr &b);
absl::StatusOr<z3::expr> Or(const z3::expr &a, const z3::expr &b);

// Binary operations.
absl::StatusOr<z3::expr> BitNeg(const z3::expr &a);
absl::StatusOr<z3::expr> BitAnd(const z3::expr &a, const z3::expr &b);
absl::StatusOr<z3::expr> BitOr(const z3::expr &a, const z3::expr &b);
absl::StatusOr<z3::expr> BitXor(const z3::expr &a, const z3::expr &b);
absl::StatusOr<z3::expr> LShift(const z3::expr &bits, const z3::expr &shift);
absl::StatusOr<z3::expr> RShift(const z3::expr &bits, const z3::expr &shift);

// If-then-else.
absl::StatusOr<z3::expr> Ite(const z3::expr &condition,
                             const z3::expr &true_value,
                             const z3::expr &false_value);

// Converts the given expression to a boolean expression.
absl::StatusOr<z3::expr> ToBoolSort(const z3::expr &a);
// Converts the given expression to a bit vector expression.
absl::StatusOr<z3::expr> ToBitVectorSort(const z3::expr &a, unsigned int size);

// Prefix equality: this is the basis for evaluating LPMs.
absl::StatusOr<z3::expr> PrefixEq(const z3::expr &a, const z3::expr &b,
                                  unsigned int prefix_size);

}  // namespace operators
}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_OPERATORS_H_
