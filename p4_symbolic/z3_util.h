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

#include "absl/status/statusor.h"
#include "p4_pdpi/string_encodings/bit_string.h"
#include "z3++.h"

namespace p4_symbolic {

// Returns the global z3::context used for creating symbolic expressions during
// symbolic evaluation. If parameter `renew` is set to true, it deletes the
// older context and returns a new one.
// TODO: `renew` is a workaround for using a global context.
z3::context &Z3Context(bool renew = false);

// -- Evaluation ---------------------------------------------------------------

absl::StatusOr<bool> EvalZ3Bool(const z3::expr &bool_expr,
                                const z3::model &model);

absl::StatusOr<int> EvalZ3Int(const z3::expr &int_expr, const z3::model &model);

absl::Status EvalAndAppendZ3BitvectorToBitString(pdpi::BitString& output,
                                                 const z3::expr& bv_expr,
                                                 const z3::model& model);

// -- Constructing Z3 expressions ----------------------------------------------

// Returns Z3 bitvector of the given `hex_string` value.
// If no bitwidth is given, the size of the bitvector is derived from
// `hex_string`.
absl::StatusOr<z3::expr>
HexStringToZ3Bitvector(z3::context &context, const std::string &hex_string,
                       absl::optional<int> bitwidth = absl::nullopt);

// -- Misc. --------------------------------------------------------------------

// Turns the given z3 extracted value (as a string) to a uint64_t.
// Z3 returns an extracted value as either a binary, hex, or decimal strings
// depending on the size of the value and the formatting flags it is initialized
// with.
// Note: This function assumes that the input is well-formatted and the result
// fits in uint64_t (otherwise an exception will be thrown).
uint64_t Z3ValueStringToInt(const std::string &value);

// == END OF PUBLIC INTERFACE ==================================================

}  // namespace p4_symbolic

#endif // PINS_P4_SYMBOLIC_Z3_UTIL_H_
