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

#include <cstdint>
#include <optional>
#include <string>
#include <utility>

#include "absl/container/btree_set.h"
#include "absl/numeric/bits.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "gmpxx.h"
#include "gutil/status.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/string_encodings/bit_string.h"
#include "p4_pdpi/utils/ir.h"
#include "p4_symbolic/z3_util.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {
namespace values {

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

absl::StatusOr<z3::expr> FormatP4RTValue(
    const pdpi::IrValue &value, const std::optional<std::string> &field_name,
    const std::string &type_name, int bitwidth, z3::context &context,
    P4RuntimeTranslator &translator) {
  switch (value.format_case()) {
    case pdpi::IrValue::kStr: {
      // Mark that this field is a string translatable field, and map it
      // to its custom type name (e.g. vrf_id => vrf_t).
      if (field_name.has_value() && !field_name->empty()) {
        translator.fields_p4runtime_type[*field_name] = type_name;
      }

      // Must translate the string into a bitvector according to the field type.
      const std::string &string_value = value.str();

      // If there is no IdAllocator for the given type (implying no static
      // mapping was provided), create a new dynamic IdAllocator.
      translator.p4runtime_translation_allocators.try_emplace(
          type_name, IdAllocator(TranslationData{
                         .static_mapping = {},
                         .dynamic_translation = true,
                     }));
      IdAllocator &allocator =
          translator.p4runtime_translation_allocators.at(type_name);

      ASSIGN_OR_RETURN(uint64_t int_value, allocator.AllocateId(string_value));
      if (bitwidth == 0) {
        bitwidth = int_value == 0 ? 1 : absl::bit_width(int_value);
      } else {
        return absl::InvalidArgumentError(absl::Substitute(
            "Translated type '$0' is expected to have bitwidth 0, got $1",
            type_name, bitwidth));
      }

      return context.bv_val(int_value, bitwidth);
    }
    default: {
      if (field_name.has_value() &&
          translator.fields_p4runtime_type.count(*field_name)) {
        return absl::InvalidArgumentError(absl::StrCat(
            "A table entry provides a non-string value ", value.DebugString(),
            "to a string translated field", *field_name));
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

absl::StatusOr<std::pair<std::string, bool>> TranslateZ3ValueStringToP4RT(
    const std::string &value, const std::optional<std::string> &field_name,
    const std::optional<std::string> &type_name,
    const P4RuntimeTranslator &translator, std::optional<pdpi::Format> format) {
  // Use `type_name` as the default field type.
  std::string field_type;
  if (type_name.has_value() && !type_name->empty()) field_type = *type_name;

  // If `field_name` is found in the mapping to P4Runtime translated field
  // types, use the field type based on the `field_name`.
  if (field_name.has_value() && !field_name->empty()) {
    if (auto it = translator.fields_p4runtime_type.find(*field_name);
        it != translator.fields_p4runtime_type.end()) {
      field_type = it->second;
    }
  }

  // Get the allocator based on the field type.
  auto it = translator.p4runtime_translation_allocators.find(field_type);
  if (it == translator.p4runtime_translation_allocators.end()) {
    if (format.has_value() && *format == pdpi::Format::STRING) {
      // With symbolic table entries, it is possible for a field type to not be
      // registered in the translator. For such cases, we simply use the string
      // representation of the numeric value. We can do this because from
      // `FormatP4RTValue` we see that previously unknown field types are all
      // translated dynamically. Therefore, as long as the mapping is bijective
      // and consistent, things should be fine.
      return std::make_pair(std::to_string(Z3ValueStringToInt(value)), true);
    } else {
      // Not translatable: identity function.
      return std::make_pair(value, false);
    }
  }

  // Translatable: do the reverse translation via the type name.
  const IdAllocator &allocator = it->second;

  // Turn the value from a string to an int.
  uint64_t int_value = Z3ValueStringToInt(value);
  ASSIGN_OR_RETURN(std::string p4rt_value, allocator.IdToString(int_value),
                   _.SetPrepend()
                       << "Failed to translate dataplane value of type '"
                       << field_type << "' to P4Runtime representation: ");
  return std::make_pair(p4rt_value, true);
}

absl::StatusOr<pdpi::IrValue> TranslateZ3ValueStringToIrValue(
    const std::string &value, int bitwidth,
    const std::optional<std::string> &field_name,
    const std::optional<std::string> &type_name,
    const P4RuntimeTranslator &translator, const pdpi::Format &format) {
  ASSIGN_OR_RETURN(auto translated_value,
                   values::TranslateZ3ValueStringToP4RT(
                       value, field_name, type_name, translator, format));
  const std::string &p4rt_value = translated_value.first;
  bool translated = translated_value.second;
  std::string byte_string;

  if (translated) {
    byte_string = p4rt_value;
  } else {
    pdpi::BitString bit_string;
    int bitstring_width = bitwidth;
    // Round up the bitwidth to the nearest multiple of 8 for converting to IR
    // value via byte strings.
    if (bitwidth % 8 != 0) {
      bitstring_width += 8 - (bitwidth % 8);
    }
    RETURN_IF_ERROR(
        AppendZ3ValueStringToBitString(bit_string, value, bitstring_width));
    ASSIGN_OR_RETURN(byte_string, bit_string.ToByteString());
  }

  if (format == pdpi::Format::STRING) {
    pdpi::IrValue ir_value;
    ir_value.set_str(byte_string);
    return ir_value;
  }

  return pdpi::ArbitraryByteStringToIrValue(format, bitwidth, byte_string);
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

  if (translation_data_.dynamic_translation) {
    // With symbolic table entries, it is possible for a dynamically translated
    // type to not have the mapping for a particular value, in which case we
    // simply use the string representation of the numeric value.
    return std::to_string(value);
  } else {
    // But for statically translated types (e.g., port_t), return an internal
    // error if no mapping is found in the reverse map.
    return gutil::InternalErrorBuilder()
           << "Cannot translate bitvector '" << value << "' to a string value.";
  }
}

absl::btree_set<uint64_t> IdAllocator::GetAllocatedIds() const {
  absl::btree_set<uint64_t> translated_ids;
  for (const auto &[id, string_value] : id_to_string_map_) {
    translated_ids.insert(id);
  }
  return translated_ids;
}

bool IdAllocator::IsDynamicAllocationEnabled() const {
  return translation_data_.dynamic_translation;
}

}  // namespace values
}  // namespace symbolic
}  // namespace p4_symbolic
