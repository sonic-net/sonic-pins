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
// The wrappers ensure sort compatibility, and pad bitvectors when needed.
// Additionally, they use absl::Status to convey sort compatibility failures
// instead of runtime crashes.

#include "p4_symbolic/symbolic/operators.h"

#include <string>
#include <utility>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "gutil/status.h"
#include "z3++.h"
#include "z3_api.h"

namespace p4_symbolic {
namespace symbolic {
namespace operators {

namespace {

// Pads bitvector with padsize-many zero bits
// will fail with a runtime error if bitvector is not of bv sort, use after
// checking that the sort is correct.
z3::expr Pad(const z3::expr &bitvector, int pad_size) {
  if (pad_size > 0) {
    return z3::concat(bitvector.ctx().bv_val(0, pad_size), bitvector);
  }
  return bitvector;
}

// Extract the suffix (e.g. the portion on the least significant bit side) of
// the bitvector of the given size.
// If suffix_size is larger than the bitvector size, the bitvector is returned
// as is.
// Precondition: suffix_size > 0, bitvector is of sort bv.
z3::expr Suffix(const z3::expr &bitvector, unsigned int suffix_size) {
  unsigned int bitvector_size = bitvector.get_sort().bv_size();
  if (suffix_size < bitvector_size) {
    // ".extract(hi, lo)" is inclusive on both ends.
    return bitvector.extract(suffix_size - 1, 0);
  }
  return bitvector;
}

}  // namespace

// Check that the two expressions have compatible sorts, and return an
// absl error otherwise.
// If the expressions are bitvector, the shortest will be padded to match
// the longest.
absl::StatusOr<std::pair<z3::expr, z3::expr>> SortCheckAndPad(
    const z3::expr &a, const z3::expr &b) {
  // Coerce bit<1> to bool.
  if (a.is_bool() && b.is_bv() && b.get_sort().bv_size() == 1) {
    return std::make_pair(a, b == 1);
  }
  if (b.is_bool() && a.is_bv() && a.get_sort().bv_size() == 1) {
    return std::make_pair(a == 1, b);
  }
  // Totally incompatible sorts (e.g. int and bitvector).
  if (a.get_sort().sort_kind() != b.get_sort().sort_kind()) {
    return absl::InvalidArgumentError(absl::StrFormat(
        "Incompatible sorts '%s' and '%s' in expressions '%s' and '%s'",
        a.get_sort().to_string(), b.get_sort().to_string(), a.to_string(),
        b.to_string()));
  }
  // If bit vectors, pad to the largest size.
  if (a.get_sort().is_bv()) {
    int a_len = a.get_sort().bv_size();
    int b_len = b.get_sort().bv_size();
    return std::make_pair(Pad(a, b_len - a_len), Pad(b, a_len - b_len));
  }
  return std::make_pair(a, b);
}

// Check that the two expressions have compatible sorts, and return an
// absl error otherwise.
// If the expressions are bitvector, the longest will be trimmed to match
// the shortest, by dropping/cutting of a portion of the most significant bits.
// I.e. by extracting the suffix of the same size as the shortest bitvector.
absl::StatusOr<std::pair<z3::expr, z3::expr>> SortCheckAndExtract(
    const z3::expr &a, const z3::expr &b) {
  // Totally incompatible sorts (e.g. int and bitvector).
  if (a.get_sort().sort_kind() != b.get_sort().sort_kind()) {
    return absl::InvalidArgumentError(
        absl::StrCat("Incompatible sorts \"", a.get_sort().to_string(),
                     "\" and \"", b.get_sort().to_string(), "\""));
  }
  // If bit vectors, pad to the largest size.
  if (a.get_sort().is_bv()) {
    unsigned int a_len = a.get_sort().bv_size();
    unsigned int b_len = b.get_sort().bv_size();
    return std::make_pair(Suffix(a, b_len), Suffix(b, a_len));
  }
  return std::make_pair(z3::expr(a), z3::expr(b));
}

absl::Status TruncateBitVectorToFit(const z3::expr &target, z3::expr &value) {
  if (target.is_bv() && value.is_bv() &&
      target.get_sort().bv_size() < value.get_sort().bv_size()) {
    value = value.extract(target.get_sort().bv_size() - 1, 0);
  }

  return absl::OkStatus();
}

// Free Variable.
absl::StatusOr<z3::expr> FreeVariable(const std::string &variable_base_name,
                                      const z3::sort &sort) {
  static unsigned int counter = 0;
  std::string variable_name =
      absl::StrFormat("%s.%d", variable_base_name, counter++);
  switch (sort.sort_kind()) {
    case Z3_BOOL_SORT: {
      return sort.ctx().bool_const(variable_name.c_str());
    }
    case Z3_INT_SORT: {
      return sort.ctx().int_const(variable_name.c_str());
    }
    case Z3_BV_SORT: {
      return sort.ctx().bv_const(variable_name.c_str(), sort.bv_size());
    }
    default:
      return absl::InvalidArgumentError(
          absl::StrCat("Unsupported sort in free variable ", sort.to_string()));
  }
}

// Arithmetic.
absl::StatusOr<z3::expr> Plus(const z3::expr &a, const z3::expr &b) {
  ASSIGN_OR_RETURN(auto pair,
                   p4_symbolic::symbolic::operators::SortCheckAndPad(a, b));
  auto &[a_expr, b_expr] = pair;
  return a_expr + b_expr;
}
absl::StatusOr<z3::expr> Minus(const z3::expr &a, const z3::expr &b) {
  ASSIGN_OR_RETURN(auto pair,
                   p4_symbolic::symbolic::operators::SortCheckAndPad(a, b));
  auto &[a_expr, b_expr] = pair;
  return a_expr - b_expr;
}
absl::StatusOr<z3::expr> Times(const z3::expr &a, const z3::expr &b) {
  ASSIGN_OR_RETURN(auto pair,
                   p4_symbolic::symbolic::operators::SortCheckAndPad(a, b));
  auto &[a_expr, b_expr] = pair;
  return a_expr * b_expr;
}
absl::StatusOr<z3::expr> Eq(const z3::expr &a, const z3::expr &b) {
  ASSIGN_OR_RETURN(auto pair,
                   p4_symbolic::symbolic::operators::SortCheckAndPad(a, b));
  auto &[a_expr, b_expr] = pair;
  return a_expr == b_expr;
}
absl::StatusOr<z3::expr> Neq(const z3::expr &a, const z3::expr &b) {
  ASSIGN_OR_RETURN(auto pair,
                   p4_symbolic::symbolic::operators::SortCheckAndPad(a, b));
  auto &[a_expr, b_expr] = pair;
  return a_expr != b_expr;
}
absl::StatusOr<z3::expr> Lt(const z3::expr &a, const z3::expr &b) {
  ASSIGN_OR_RETURN(auto pair,
                   p4_symbolic::symbolic::operators::SortCheckAndPad(a, b));
  auto &[a_expr, b_expr] = pair;
  return z3::ult(a_expr, b_expr);
}
absl::StatusOr<z3::expr> Lte(const z3::expr &a, const z3::expr &b) {
  ASSIGN_OR_RETURN(auto pair,
                   p4_symbolic::symbolic::operators::SortCheckAndPad(a, b));
  auto &[a_expr, b_expr] = pair;
  return z3::ule(a_expr, b_expr);
}
absl::StatusOr<z3::expr> Gt(const z3::expr &a, const z3::expr &b) {
  ASSIGN_OR_RETURN(auto pair,
                   p4_symbolic::symbolic::operators::SortCheckAndPad(a, b));
  auto &[a_expr, b_expr] = pair;
  return z3::ugt(a_expr, b_expr);
}
absl::StatusOr<z3::expr> Gte(const z3::expr &a, const z3::expr &b) {
  ASSIGN_OR_RETURN(auto pair,
                   p4_symbolic::symbolic::operators::SortCheckAndPad(a, b));
  auto &[a_expr, b_expr] = pair;
  return z3::uge(a_expr, b_expr);
}
absl::StatusOr<z3::expr> Not(const z3::expr &a) { return !a; }
absl::StatusOr<z3::expr> And(const z3::expr &a, const z3::expr &b) {
  return a && b;
}
absl::StatusOr<z3::expr> Or(const z3::expr &a, const z3::expr &b) {
  return a || b;
}
absl::StatusOr<z3::expr> BitNeg(const z3::expr &a) { return ~a; }

// Unlike the other operators, BitAnd does not pad to the maximum bitsize
// of the two operands. Instead, it truncates to the min (by dropping the most
// significant x bits).
//
// First, we show why this preserves correctness, then we discuss why it's
// necessary.
//
// Imagine we have an expression on the form "x & y" where x is of size 10 and y
// is of size 5. Padding y to 10 would result in adding 0 zeros to its left.
// This causes the final output to be on the form "00000(x5&y5)...(x1&y1)".
// In generality, padding the shorter operand results in an output that has
// just as many zeros to the left, because this is an &.
//
// On the other hand, trimming to the shortest size will result in the 5 most
// significant bits in x being removed, and an output "(x5&y5)...(x1&y1)".
// Note that this output is equivlanet to the padding output semantically.
// Furthermore, our symbolic pipeline allows shorter operands to be padded
// to larger lengths anywhere, by appending zeros to the left, meaning that
// this output can be used equivalently in any context that the padding output
// could have been used in (this also applies to nested &).
//
// This is important because of a bmv2 quirk: extraction in p4
// (e.g. header.field[0:n]), is translated to a mask bit and by the bmv2 p4c
// backend (e.g. header.field & 1...1 (n times)). Clearly, the desired output of
// the extraction is of size n < header.field size. However, if our & pads to
// the maximum, it will output something of size |header.field| with
// |header.field| - n leading zeros. This output, while semantically equivlanet,
// cannot be used in certain contexts that expect the bitvector size to be n,
// since our semantics do not allow arbitrary extraction to smaller sizes, but
// do allow arbitrary padding.
absl::StatusOr<z3::expr> BitAnd(const z3::expr &a, const z3::expr &b) {
  // Coerce bool to bit<1>.
  if (a.is_bool() && b.is_bv() && b.get_sort().bv_size() == 1) {
    return z3::ite(a, b, a.ctx().bv_val(0, 1));
  }
  if (b.is_bool() && a.is_bv() && a.get_sort().bv_size() == 1) {
    return z3::ite(b, a, b.ctx().bv_val(0, 1));
  }
  ASSIGN_OR_RETURN(auto pair,
                   p4_symbolic::symbolic::operators::SortCheckAndExtract(a, b));
  auto &[a_expr, b_expr] = pair;
  return a_expr & b_expr;
}

absl::StatusOr<z3::expr> BitOr(const z3::expr &a, const z3::expr &b) {
  ASSIGN_OR_RETURN(auto pair,
                   p4_symbolic::symbolic::operators::SortCheckAndPad(a, b));
  auto &[a_expr, b_expr] = pair;
  return a_expr | b_expr;
}
absl::StatusOr<z3::expr> BitXor(const z3::expr &a, const z3::expr &b) {
  ASSIGN_OR_RETURN(auto pair,
                   p4_symbolic::symbolic::operators::SortCheckAndPad(a, b));
  auto &[a_expr, b_expr] = pair;
  return a_expr ^ b_expr;
}
absl::StatusOr<z3::expr> LShift(const z3::expr &bits, const z3::expr &shift) {
  ASSIGN_OR_RETURN(auto pair, SortCheckAndPad(bits, shift));
  auto &[a_expr, b_expr] = pair;
  return z3::shl(a_expr, b_expr);
}
absl::StatusOr<z3::expr> RShift(const z3::expr &bits, const z3::expr &shift) {
  ASSIGN_OR_RETURN(auto pair, SortCheckAndPad(bits, shift));
  auto &[a_expr, b_expr] = pair;
  return z3::lshr(a_expr, b_expr);
}

// If then else.
absl::StatusOr<z3::expr> Ite(const z3::expr &condition,
                             const z3::expr &true_value,
                             const z3::expr &false_value) {
  // The sort of the condition must be bool. Otherwise z3::ite() will throw an
  // assertion failure.
  if (!condition.is_bool()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "The condition of an if-then-else operation must be boolean. "
              "Found: "
           << condition.to_string();
  }

  // Optimization: if both branches are the same *syntactically*
  // then we can just use the branch expression directly and no need
  // for an if-then-else statement.
  if (z3::eq(true_value, false_value)) {
    return true_value;
  }

  // Values in both cases must have the same sort and signedness.
  ASSIGN_OR_RETURN(auto pair, SortCheckAndPad(true_value, false_value));
  auto &[a_expr, b_expr] = pair;
  return z3::ite(condition, a_expr, b_expr);
}

// Conversions.
absl::StatusOr<z3::expr> ToBoolSort(const z3::expr &a) {
  if (a.get_sort().is_bool()) {
    return a;
  } else if (a.get_sort().is_bv()) {
    return Gte(a, a.ctx().bv_val(1, 1));
  } else if (a.get_sort().is_int()) {
    return a >= a.ctx().int_val(1);
  } else {
    return absl::InvalidArgumentError("Illegal conversion to bool sort");
  }
}
absl::StatusOr<z3::expr> ToBitVectorSort(const z3::expr &a, unsigned int size) {
  if (a.get_sort().is_bool()) {
    z3::expr bits = z3::ite(a, a.ctx().bv_val(1, 1), a.ctx().bv_val(0, 1));
    return Pad(bits, size - 1);
  } else if (a.get_sort().is_bv()) {
    if (a.get_sort().bv_size() <= size) {
      return Pad(a, size - a.get_sort().bv_size());
    }
  }
  return absl::InvalidArgumentError("Illegal conversion to bitvector sort");
}

// Prefix equality.
absl::StatusOr<z3::expr> PrefixEq(const z3::expr &a, const z3::expr &b,
                                  unsigned int prefix_size) {
  if (!a.get_sort().is_bv() || !b.get_sort().is_bv()) {
    return absl::InvalidArgumentError("PrefixEq is only valid for bitvectors");
  }

  unsigned int a_size = a.get_sort().bv_size();
  unsigned int b_size = b.get_sort().bv_size();
  z3::expr a_expr = a;
  z3::expr b_expr = b;

  // Pad short bit vectors to be at least as large as the prefix to extract.
  if (a_size < prefix_size) {
    a_expr = Pad(a, prefix_size - a_size);
    a_size = prefix_size;
  }
  if (b_size < prefix_size) {
    b_expr = Pad(b, prefix_size - b_size);
    b_size = prefix_size;
  }

  // Extract prefix from bit vectors.
  if (a_size > prefix_size) {
    // Note: extract(hi, lo) is inclusive on both ends.
    a_expr = a_expr.extract(a_size - 1, a_size - prefix_size);
  }
  if (b_size > prefix_size) {
    b_expr = b_expr.extract(b_size - 1, b_size - prefix_size);
  }

  return a_expr == b_expr;
}

}  // namespace operators
}  // namespace symbolic
}  // namespace p4_symbolic
