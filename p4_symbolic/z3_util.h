#ifndef PINS_P4_SYMBOLIC_Z3_UTIL_H_
#define PINS_P4_SYMBOLIC_Z3_UTIL_H_

#include <bitset>

#include "absl/status/statusor.h"
#include "absl/strings/strip.h"
#include "gutil/status.h"
#include "p4_pdpi/string_encodings/hex_string.h"
#include "z3++.h"

namespace p4_symbolic {

// Global z3::context used for creating symbolic expressions during symbolic
// evaluation.
z3::context& Z3Context();

// -- Evaluation ---------------------------------------------------------------

absl::StatusOr<bool> EvalZ3Bool(const z3::expr& bool_expr,
                                const z3::model& model);

absl::StatusOr<int> EvalZ3Int(const z3::expr& int_expr, const z3::model& model);

template <size_t num_bits>
absl::StatusOr<std::bitset<num_bits>> EvalZ3Bitvector(const z3::expr& bv_expr,
                                                      const z3::model& model);

// -- Constructing Z3 expressions ----------------------------------------------

// Returns Z3 bitvector of the given `hex_string` value.
// If no bitwidth is
absl::StatusOr<z3::expr> HexStringToZ3Bitvector(
    const std::string& hex_string,
    absl::optional<int> bitwidth = absl::nullopt);

// == END OF PUBLIC INTERFACE ==================================================

template <size_t num_bits>
absl::StatusOr<std::bitset<num_bits>> EvalZ3Bitvector(const z3::expr& bv_expr,
                                                      const z3::model& model) {
  if (!bv_expr.is_bv() || bv_expr.get_sort().bv_size() != num_bits) {
    return gutil::InvalidArgumentErrorBuilder()
           << "expected bitvector of " << num_bits << " bits, but got "
           << bv_expr.get_sort() << ": " << bv_expr;
  }

  std::string value_with_prefix = model.eval(bv_expr, true).to_string();
  absl::string_view value = value_with_prefix;
  if (absl::ConsumePrefix(&value, "#x")) {
    return pdpi::HexStringToBitset<num_bits>(absl::StrCat("0x", value));
  }
  if (absl::ConsumePrefix(&value, "#b")) {
    return std::bitset<num_bits>(std::string(value));
  }
  return gutil::InvalidArgumentErrorBuilder()
         << "invalid Z3 bitvector value '" << value_with_prefix << "'";
}

}  // namespace p4_symbolic

#endif  // PINS_P4_SYMBOLIC_Z3_UTIL_H_
