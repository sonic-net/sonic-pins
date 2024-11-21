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

// This file is responsible for parsing values from the bmv2 json and table
// entries.
// It is also responsible for translating any string values to corresponding
// bitvectors and back, for fields that have the @p4runtime_translation
// annotation.

#include "p4_symbolic/symbolic/values.h"

#include <locale>
#include <optional>
#include <sstream>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/strings/strip.h"
#include "absl/strings/substitute.h"
#include "gmpxx.h"
#include "gutil/status.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/netaddr/ipv4_address.h"
#include "p4_pdpi/netaddr/ipv6_address.h"
#include "p4_pdpi/netaddr/mac_address.h"
#include "p4_pdpi/string_encodings/byte_string.h"
#include "p4_pdpi/utils/ir.h"
#include "p4_symbolic/symbolic/operators.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/z3_util.h"

namespace p4_symbolic {
namespace symbolic {
namespace values {

namespace {

// Finds the minimum bit size required for representing the given value.
unsigned int FindBitsize(uint64_t value) {
  unsigned int bitsize = 0;
  uint64_t pow = 1;
  while (bitsize <= 64 && pow <= value) {
    pow = pow * 2;
    bitsize++;
  }
  return (bitsize > 1 ? bitsize : 1);  // At least 1 bit.
}

}  // namespace

absl::StatusOr<pdpi::IrValue> ParseIrValue(const std::string &value) {
  // Format according to type.
  if (absl::StartsWith(value, "0x")) {
    return pdpi::FormattedStringToIrValue(value, pdpi::Format::HEX_STRING);
  } else {
    // Some unsupported format!
    return absl::InvalidArgumentError(
        absl::StrCat("Literal value \"", value, "\" has unknown format!"));
  }
}

absl::StatusOr<z3::expr> FormatP4RTValue(z3::context &context,
                                         const std::string &field_name,
                                         const std::string &type_name,
                                         const pdpi::IrValue &value,
                                         int bitwidth,
                                         P4RuntimeTranslator *translator) {
  switch (value.format_case()) {
    case pdpi::IrValue::kStr: {
      // Mark that this field is a string translatable field, and map it
      // to its custom type name (e.g. vrf_id => vrf_t).
      if (!field_name.empty()) {
        translator->fields_p4runtime_type[field_name] = type_name;
      }

      // Must translate the string into a bitvector according to the field type.
      const std::string &string_value = value.str();
      
      // If there is no IdAllocator for the given type (implying no static
      // mapping was provided), create a new dynamic IdAllocator.
      translator->p4runtime_translation_allocators.try_emplace(
          type_name, IdAllocator(TranslationData{
                         .static_mapping = {},
                         .dynamic_translation = true,
                     }));
      IdAllocator &allocator =
          translator->p4runtime_translation_allocators.at(type_name);

      ASSIGN_OR_RETURN(uint64_t int_value, allocator.AllocateId(string_value));
      if (bitwidth == 0) {
        bitwidth = FindBitsize(int_value);
      } else {
        return absl::InvalidArgumentError(absl::Substitute(
            "Translated type '$0' is expected to have bitwidth 0, got $1",
            type_name, bitwidth));
      }

      return context.bv_val(int_value, bitwidth);
    }
    default: {
      if (translator->fields_p4runtime_type.count(field_name)) {
        return absl::InvalidArgumentError(absl::StrCat(
            "A table entry provides a non-string value ", value.DebugString(),
            "to a string translated field", field_name));
      }

      // Rely on PDPI to convert the value since its logic is non-trivial and
      // may change from time to time. Specifically, use PDPI to convert to
      // NormalizedByteString and back into IR as a pdpi::HEX_STRING.
      ASSIGN_OR_RETURN(const std::string byte_string,
                       pdpi::IrValueToNormalizedByteString(value, bitwidth));
      ASSIGN_OR_RETURN(const pdpi::IrValue normalized_value,
                       pdpi::ArbitraryByteStringToIrValue(
                           pdpi::HEX_STRING, bitwidth, byte_string));
      // Now convert the hex string internally.
      return HexStringToZ3Bitvector(context, normalized_value.hex_str(),
                                    bitwidth);
    }
  }
}

absl::StatusOr<std::string> TranslateValueToP4RT(
    const std::string &field_name, const std::string &value,
    const P4RuntimeTranslator &translator) {
  // Not translatable: identity function.
  if (!translator.fields_p4runtime_type.count(field_name)) {
    return value;
  }

  // Translatable: do the reverse translation via the type name.
  const std::string &field_type_name =
      translator.fields_p4runtime_type.at(field_name);
  const IdAllocator &allocator =
      translator.p4runtime_translation_allocators.at(field_type_name);

  // Turn the value from a string to an int.
  uint64_t int_value = Z3ValueStringToInt(value);
  ASSIGN_OR_RETURN(std::string p4rt_value, allocator.IdToString(int_value),
                   _.SetPrepend()
                       << "failed to translate dataplane value of field '"
                       << field_name << "' to P4Runtime representation: ");
  return p4rt_value;
}

IdAllocator::IdAllocator(const TranslationData &translation_data)
    : translation_data_(translation_data) {
  for (const auto &[string_value, id] : translation_data_.static_mapping) {
    string_to_id_map_[string_value] = id;
    id_to_string_map_[id] = string_value;
  }
}

absl::StatusOr<uint64_t> IdAllocator::AllocateId(
    const std::string &string_value) {
  // If previously allocated, return the same bitvector value.
  if (this->string_to_id_map_.count(string_value)) {
    return this->string_to_id_map_.at(string_value);
  }

  if (translation_data_.dynamic_translation) {
    // If dynamic allocation is enabled, allocate new bitvector value and store
    // it in mapping.

    // Get the next unused ID value.
    while (id_to_string_map_.find(next_id_) != id_to_string_map_.end()) {
      ++next_id_;
    }

    // Allocate it for the string value.
    string_to_id_map_[string_value] = next_id_;
    id_to_string_map_[next_id_] = string_value;
    return next_id_;
  } else {
    return absl::InvalidArgumentError(
        absl::StrCat("Cannot translate string value '", string_value,
                     "' to a bitvector with the given static mapping."));
  }
}

absl::StatusOr<std::string> IdAllocator::IdToString(uint64_t value) const {
  // Normalize the bitvector and look it up in the reverse mapping.
  if (this->id_to_string_map_.count(value)) {
    return this->id_to_string_map_.at(value);
  }

  // Could not find the bitvector in reverse map!
  return absl::InvalidArgumentError(absl::StrCat(
      "Cannot translate bitvector '", value, "' to a string value."));
}

}  // namespace values
}  // namespace symbolic
}  // namespace p4_symbolic
