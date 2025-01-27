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

#include <cstddef>
#include <cstdint>
#include <string>

#include "absl/numeric/int128.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/strings/strip.h"
#include "absl/types/optional.h"
#include "gmpxx.h"
#include "gutil/gutil/status.h"
#include "p4_infra/p4_pdpi/string_encodings/bit_string.h"
#include "p4_infra/p4_pdpi/string_encodings/hex_string.h"
#include "z3++.h"
#include "z3_api.h"

namespace p4_symbolic {

namespace {

// Appends exactly `num_bits` bits to the `result` PDPI bit string from the
// given `bit_char_string`. Returns an error if the bit-width of the
// `bit_char_string` exceeds `num_bits`. If the bit-width of the
// `bit_char_string` is less than `num_bits`, pads leading zero bits before
// appending `bit_char_string`.
// Note that we assume network (big) endianness for all bit strings and packet
// fields. When interpreted to integers, preceding bits are more significant.
absl::Status AppendBitCharStringToPDPIBitString(
    pdpi::BitString& result, const absl::string_view& bit_char_string,
    size_t num_bits) {
  // The bit string length should not exceed the specified number of bits.
  if (bit_char_string.size() > num_bits) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Bit string length exceeds the specified size (" << num_bits
           << " bits): '" << bit_char_string << "'";
  }

  // Pad leading 0s if the bit string is shorter than the specified size.
  for (size_t i = 0; i < num_bits - bit_char_string.size(); ++i) {
    result.AppendBit(0);
  }

  // Append the bits to the result bit string based on the given value.
  for (const char& c : bit_char_string) {
    switch (c) {
      case '1': {
        result.AppendBit(1);
        break;
      }
      case '0': {
        result.AppendBit(0);
        break;
      }
      default: {
        return gutil::InvalidArgumentErrorBuilder()
               << "Bit string must contain either 1s or 0s. Found: "
               << bit_char_string;
      }
    }
  }

  return absl::OkStatus();
}

// Appends exactly `num_bits` bits to the `result` PDPI bit string from the
// given `hex_char_string`. Returns an error if the bit-width of the
// `hex_char_string` exceeds `num_bits`. If the bit-width of the
// `hex_char_string` is less than `num_bits`, pads leading zero bits before
// appending `hex_char_string`.
// Note that we assume network (big) endianness for all bit strings and packet
// fields. When interpreted to integers, preceding bits are more significant.
absl::Status AppendHexCharStringToPDPIBitString(
    pdpi::BitString& result, const absl::string_view& hex_char_string,
    size_t num_bits) {
  // The hex string length should not exceed the specified number of bits.
  if (hex_char_string.size() * 4 > num_bits) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Hex string length exceeds the specified size (" << num_bits
           << " bits): '" << hex_char_string << "'";
  }

  // Pad leading 0s if the hex string is shorter than the specified size.
  for (size_t i = 0; i < num_bits - hex_char_string.size() * 4; ++i) {
    result.AppendBit(0);
  }

  std::string hex_string = std::string(hex_char_string);

  // If the hex string has an uneven length, convert the first hex character and
  // then convert the rest of the hex string with an even length.
  if (hex_string.size() % 2 == 1) {
    // Convert the first hex character and append to the result bit string.
    ASSIGN_OR_RETURN(const int digit, pdpi::HexCharToDigit(hex_string.at(0)));
    for (int i = 3; i >= 0; --i) {
      result.AppendBit((digit >> i) % 2);
    }

    // Remove the appended hex character to form an even hex string.
    hex_string = hex_string.substr(1);
  }

  return result.AppendHexString(absl::StrCat("0x", hex_string));
}

}  // namespace

absl::StatusOr<bool> EvalZ3Bool(const z3::expr& bool_expr,
                                const z3::model& model) {
  if (!bool_expr.is_bool()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Expected a boolean expression, found '" << bool_expr << "'";
  }

  auto value = model.eval(bool_expr, /*model_completion=*/true).bool_value();
  switch (value) {
    case Z3_L_FALSE:
      return false;
    case Z3_L_TRUE:
      return true;
    default:
      return gutil::InternalErrorBuilder()
             << "boolean expression '" << bool_expr
             << "' evaluated to unexpected Boolean value " << value;
  }
}

absl::StatusOr<int> EvalZ3Int(const z3::expr& int_expr,
                              const z3::model& model) {
  if (!int_expr.is_int()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Expected an integer expression, found '" << int_expr << "'";
  }

  return model.eval(int_expr, /*model_completion=*/true).get_numeral_int();
}

absl::Status EvalAndAppendZ3BitvectorToBitString(pdpi::BitString& output,
                                                 const z3::expr& bv_expr,
                                                 const z3::model& model) {
  if (!bv_expr.is_bv()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Expected a bitvector, found '" << bv_expr << "'";
  }

  const std::string value =
      model.eval(bv_expr, /*model_completion=*/true).to_string();
  return AppendZ3ValueStringToBitString(output, value,
                                        bv_expr.get_sort().bv_size());
}

absl::StatusOr<uint64_t> EvalZ3BitvectorToUInt64(const z3::expr& bv_expr,
                                                 const z3::model& model) {
  if (!bv_expr.is_bv()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Expected a bitvector, found '" << bv_expr << "'";
  }

  if (bv_expr.get_sort().bv_size() > 64) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Expected a bitvector within 64 bits, found "
           << bv_expr.get_sort().bv_size() << " bits";
  }

  const std::string value =
      model.eval(bv_expr, /*model_completion=*/true).to_string();
  return Z3ValueStringToInt(value);
}

absl::StatusOr<absl::uint128> EvalZ3BitvectorToUInt128(const z3::expr& bv_expr,
                                                       const z3::model& model) {
  if (!bv_expr.is_bv()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Expected a bitvector, found '" << bv_expr << "'";
  }

  if (bv_expr.get_sort().bv_size() > 128) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Expected a bitvector within 128 bits, found "
           << bv_expr.get_sort().bv_size() << " bits";
  }

  const std::string value_string =
      model.eval(bv_expr, /*model_completion=*/true).to_string();
  absl::string_view value = value_string;
  absl::uint128 result;

  if (absl::ConsumePrefix(&value, "#x")) {
    if (!absl::SimpleHexAtoi(value, &result)) {
      return gutil::InvalidArgumentErrorBuilder()
             << "Unable to convert hex string '" << value << "' to uint128";
    }
  } else if (absl::ConsumePrefix(&value, "#b")) {
    uint64_t hi = 0;
    uint64_t lo = 0;

    if (value.size() > 64) {
      hi = std::stoull(std::string(value.substr(0, value.size() - 64)),
                       /*idx=*/nullptr, /*base=*/2);
      lo = std::stoull(std::string(value.substr(value.size() - 64)),
                       /*idx=*/nullptr, /*base=*/2);
    } else {
      lo = std::stoull(std::string(value), /*idx=*/nullptr, /*base=*/2);
    }

    result = absl::MakeUint128(hi, lo);
  } else {
    return gutil::InvalidArgumentErrorBuilder()
           << "Invalid Z3 bitvector value '" << value << "'";
  }

  return result;
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

absl::Status AppendZ3ValueStringToBitString(pdpi::BitString& result,
                                            absl::string_view value,
                                            size_t num_bits) {
  if (absl::ConsumePrefix(&value, "#x")) {
    RETURN_IF_ERROR(
        AppendHexCharStringToPDPIBitString(result, value, num_bits));
  } else if (absl::ConsumePrefix(&value, "#b")) {
    RETURN_IF_ERROR(
        AppendBitCharStringToPDPIBitString(result, value, num_bits));
  } else {
    return gutil::InvalidArgumentErrorBuilder()
           << "Invalid Z3 bitvector value '" << value << "'";
  }

  return absl::OkStatus();
}

}  // namespace p4_symbolic
