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

#ifndef PINS_P4_SYMBOLIC_Z3_UTIL_H_
#define PINS_P4_SYMBOLIC_Z3_UTIL_H_

#include <cstddef>
#include <cstdint>
#include <string>

#include "absl/numeric/int128.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/types/optional.h"
#include "p4_infra/p4_pdpi/string_encodings/bit_string.h"
#include "z3++.h"

namespace p4_symbolic {

// -- Evaluation ---------------------------------------------------------------

// Evaluates the given `bool_expr` to a boolean value based on the given
// `model`. Returns an error if the given expression is not a boolean
// expression.
absl::StatusOr<bool> EvalZ3Bool(const z3::expr& bool_expr,
                                const z3::model& model);

// Evaluates the given `int_expr` to an integer value based on the given
// `model`. Returns an error if the given expression is not an integer
// expression.
absl::StatusOr<int> EvalZ3Int(const z3::expr& int_expr, const z3::model& model);

// Evaluates the given `bv_expr` bit-vector and appends the value to the
// `output` bit-string based on the given `model`. Returns an error if the given
// expression is not a bit-vector.
absl::Status EvalAndAppendZ3BitvectorToBitString(pdpi::BitString& output,
                                                 const z3::expr& bv_expr,
                                                 const z3::model& model);

// Evaluates the given `bv_expr` bit-vector to uint64_t based on the given
// `model`. Returns an error if the given expression is not a bit-vector or if
// the size is over 64 bits.
absl::StatusOr<uint64_t> EvalZ3BitvectorToUInt64(const z3::expr& bv_expr,
                                                 const z3::model& model);

// Evaluates the given `bv_expr` bit-vector to absl::uint128 based on the given
// `model`. Returns an error if the given expression is not a bit-vector or if
// the size is over 128 bits.
absl::StatusOr<absl::uint128> EvalZ3BitvectorToUInt128(const z3::expr& bv_expr,
                                                       const z3::model& model);

// -- Constructing Z3 expressions ----------------------------------------------

// Returns Z3 bitvector of the given `hex_string` value.
// If no bitwidth is given, the size of the bitvector is derived from
// `hex_string`.
absl::StatusOr<z3::expr> HexStringToZ3Bitvector(
    z3::context& context, const std::string& hex_string,
    absl::optional<int> bitwidth = absl::nullopt);

// -- Misc. --------------------------------------------------------------------

// Turns the given z3 extracted value (as a string) to a uint64_t.
// Z3 returns an extracted value as either a binary, hex, or decimal strings
// depending on the size of the value and the formatting flags it is initialized
// with.
// Note: This function assumes that the input is well-formatted and the result
// fits in uint64_t (otherwise an exception will be thrown).
uint64_t Z3ValueStringToInt(const std::string& value);

// Appends exactly `num_bits` bits to the `result` PDPI bit string from the
// evaluated Z3 string `value`. Returns an error if the `value` is not a valid
// Z3 bit-vector value (i.e., if it is not a hex string starting with "#x" and
// not a binary bit string starting with "#b").
absl::Status AppendZ3ValueStringToBitString(pdpi::BitString& result,
                                            absl::string_view value,
                                            size_t num_bits);

// == END OF PUBLIC INTERFACE ==================================================

}  // namespace p4_symbolic

#endif  // PINS_P4_SYMBOLIC_Z3_UTIL_H_
