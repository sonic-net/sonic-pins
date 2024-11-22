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
#include "p4_symbolic/z3_util.h"

#include "absl/status/statusor.h"
#include "gmpxx.h"
#include "gutil/status.h"
#include "p4_pdpi/string_encodings/hex_string.h"
#include "z3++.h"

namespace p4_symbolic {

z3::context& Z3Context(bool renew) {
  static z3::context* z3_context = new z3::context();

  if (renew) {
    delete z3_context;
    z3_context = new z3::context();
  }

  return *z3_context;
}

absl::StatusOr<bool> EvalZ3Bool(const z3::expr& bool_expr,
                                const z3::model& model) {
  // TODO: Ensure this doesn't crash by checking sort first.
  auto value = model.eval(bool_expr, true).bool_value();
  switch (value) {
    case Z3_L_FALSE:
      return false;
    case Z3_L_TRUE:
      return true;
    default:
      break;
  }
  return gutil::InternalErrorBuilder()
         << "boolean expression '" << bool_expr
         << "' evaluated to unexpected Boolean value " << value;
}

absl::StatusOr<int> EvalZ3Int(const z3::expr& int_expr,
                              const z3::model& model) {
  // TODO: Ensure this doesn't crash by checking sort first.
  return model.eval(int_expr, true).get_numeral_int();
}

absl::StatusOr<z3::expr> HexStringToZ3Bitvector(z3::context& context,
                                                const std::string& hex_string,
                                                absl::optional<int> bitwidth) {
  // TODO: Insert check to ensure this won't throw an exception.
  mpz_class integer = mpz_class(hex_string, /*base=*/0);
  std::string decimal = integer.get_str(/*base=*/10);
  if (!bitwidth.has_value()) {
    bitwidth = integer.get_str(/*base=*/2).size();
  }
  return context.bv_val(decimal.c_str(), *bitwidth);
}

uint64_t Z3ValueStringToInt(const std::string& value) {
  if (absl::StartsWith(value, "#x")) {
    return std::stoull(value.substr(2), /*idx=*/nullptr, /*base=*/16);
  }
  if (absl::StartsWith(value, "#b")) {
    return std::stoull(value.substr(2), /*idx=*/nullptr, /*base=*/2);
  }

  // Boolean or integer values.
  if (value == "true") {
    return 1;
  } else if (value == "false") {
    return 0;
  } else {
    // Must be a base 10 number.
    return std::stoull(value, /*idx=*/nullptr, /*base=*/10);
  }
}

}  // namespace p4_symbolic
