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

#ifndef P4_SYMBOLIC_SYMBOLIC_VALUES_H_
#define P4_SYMBOLIC_SYMBOLIC_VALUES_H_

#include <cstdint>
#include <optional>
#include <string>
#include <unordered_map>

#include "gutil/status.h"
#include "p4_pdpi/ir.pb.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {
namespace values {

// Translation data for a certain (P4RT translated) P4 type.
struct TranslationData {
  // Static mapping between string values and ids.
  std::vector<std::pair<std::string, uint64_t>> static_mapping;
  // Indicates if the allocator should dynamically assign new Ids to new string
  // values (i.e. values not present in the static mapping).
  // Note: If a translation is purely static (i.e. dynamic_translation = false),
  // the domain of the possible values for any variable with that type is
  // restricted to to values static_mapping (see symbolic.cc). In the future, we
  // might want to add a parameter to make this configurable by the user.
  bool dynamic_translation = false;
};

// This class is responsible for translating string values into consistent
// numberic ids, that can then be used to create bitvector values to use in
// z3.
// It also handles the reverse translation of previously allocated ids to
// their corresponding string value.
class IdAllocator {
 public:
  IdAllocator(const TranslationData &translation_data);

  // Allocates an integer ID to this string identifier. If a static mapping is
  // provided, the value from that mapping is used. If there is no static
  // mapping for the string value and dynamic allocation is enabled, an
  // arbitrary ID is used. Otherwise, returns an error. In case of dynamic
  // allocation, the chosen ID is guaranteed to be consistent (the same
  // bitvector is allocated to equal strings), and unique per instance of this
  // class.
  absl::StatusOr<uint64_t> AllocateId(const std::string &string_value);

  // Reverse translation of an allocated bit vector to the string value for
  // which it was allocated.
  absl::StatusOr<std::string> IdToString(uint64_t value) const;

 private:
  // A mapping from string values to bitvector values.
  std::unordered_map<std::string, uint64_t> string_to_id_map_;

  // A mapping from bitvector values to string values.
  std::unordered_map<uint64_t, std::string> id_to_string_map_;

  TranslationData translation_data_;
  // Used to come up with new values per new allocation.
  uint64_t next_id_ = 0;
};

// This struct stores all the state that is required to translate string values
// to internal bitvectors per custom p4 type (e.g. vrf_t), and reverse translate
// bitvector values of fields of such a custom type to a string value.
struct P4RuntimeTranslator {
  // Maps a type name to an allocator responsible for translating values for
  // that type.
  // We have an instance of the allocator class per translatable type.
  // The generated ids are unique only per type, different types may re-use
  // the same id.
  std::unordered_map<std::string, IdAllocator> p4runtime_translation_allocators;
  // Maps field name to a type name, only for fields we were able to detect had
  // a custom p4 type with a @p4runtime_translation annotation attached to it.
  // This information is not available in the bmv2 file, since it strips away
  // type aliases and  annotations, so we must build it ourselves with a best
  // effort approach.
  std::unordered_map<std::string, std::string> fields_p4runtime_type;
};

// Transforms a hex string literal from bmv2 json to a pdpi::IrValue
absl::StatusOr<pdpi::IrValue> ParseIrValue(const std::string &value);

// Transforms a value read from a table entry to a z3::expr.
// On top of formatting ipv4, ipv6, hexstrings, and macs as bitvectors,
// this function also translates string values to unique bitvectors.
// The mapping of strings to bitvectors is stored in the translator state,
// and used to map the same string to the same consistent bitvector, and to
// do a reverse-translation when extracting values for headers and fields from
// the z3 model.
// Parameter `bitwidth` is the width of the underlying PI value. For runtime
// translated values (i.e. string IrValues) the bitwidth MUST be 0, in which
// case we use the minimum number of bits to encode the resulting translated
// value.
absl::StatusOr<z3::expr> FormatP4RTValue(const std::string &field_name,
                                         const std::string &type_name,
                                         const pdpi::IrValue &value,
                                         int bitwidth,
                                         P4RuntimeTranslator *translator);

// Reverse translation: operates opposite to FormatP4RTValue().
// If the given field was not detected to be translatable (perhaps it is indeed
// not translatable), the function returns the value unchanged.
// If the given field was detected to be translatable (e.g. some values for it
// were previously translated by a call to FormatP4RTValue), then the value
// is looked up using the reverse mapping inside the given translator, if that
// look fails, an absl error is returned.
absl::StatusOr<std::string> TranslateValueToP4RT(
    const std::string &field_name, const std::string &value,
    const P4RuntimeTranslator &translator);

}  // namespace values
}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_VALUES_H_
