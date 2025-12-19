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

// Defines our SymbolicGuardedMap class.

#include "p4_symbolic/symbolic/guarded_map.h"

#include <string>

#include "absl/container/btree_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "gutil/status.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/symbolic/operators.h"
#include "p4_symbolic/symbolic/util.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {

absl::StatusOr<SymbolicGuardedMap> SymbolicGuardedMap::CreateSymbolicGuardedMap(
    z3::context &z3_context,
    const google::protobuf::Map<std::string, ir::HeaderType> &headers) {
  ASSIGN_OR_RETURN(auto map, util::FreeSymbolicHeaders(z3_context, headers));
  return SymbolicGuardedMap(map);
}

bool SymbolicGuardedMap::ContainsKey(absl::string_view key) const {
  return this->map_.contains(key);
}

absl::StatusOr<z3::expr> SymbolicGuardedMap::Get(absl::string_view key) const {
  if (auto it = this->map_.find(key); it != this->map_.end()) {
    return it->second;
  }

  return absl::InvalidArgumentError(
      absl::StrCat("Cannot find key \"", key, "\" in SymbolicGuardedMap!"));
}

absl::StatusOr<z3::expr> SymbolicGuardedMap::Get(
    absl::string_view header_name, absl::string_view field_name) const {
  std::string key = absl::StrFormat("%s.%s", header_name, field_name);
  return Get(key);
}

absl::Status SymbolicGuardedMap::Set(absl::string_view key, z3::expr value,
                                     const z3::expr &guard) {
  if (!this->ContainsKey(key)) {
    return absl::InvalidArgumentError(absl::StrCat(
        "Cannot assign to key \"", key, "\" in SymbolicGuardedMap!"));
  }

  // Simple simplification in case the guard is true.
  if (guard.is_true()) return UnguardedSet(key, value);

  z3::expr &old_value = this->map_.at(key);

  // Ite will pad bitvectors to the same size, but this is not the right
  // semantics if we assign a larger bitvector into a smaller one. Instead, the
  // assigned value needs to be truncated to the bitsize of the assignee.
  RETURN_IF_ERROR(operators::TruncateBitVectorToFit(old_value, value));

  // This will return an absl error if the sorts are incompatible, and will pad
  // shorter bit vectors.
  ASSIGN_OR_RETURN(old_value, operators::Ite(guard, value, old_value));
  return absl::OkStatus();
}

absl::Status SymbolicGuardedMap::Set(absl::string_view header_name,
                                     absl::string_view field_name,
                                     z3::expr value, const z3::expr &guard) {
  std::string key = absl::StrFormat("%s.%s", header_name, field_name);
  return Set(key, value, guard);
}

absl::Status SymbolicGuardedMap::UnguardedSet(absl::string_view key,
                                              z3::expr value) {
  if (!this->ContainsKey(key)) {
    return absl::InvalidArgumentError(absl::StrCat(
        "Cannot assign to key \"", key, "\" in SymbolicGuardedMap!"));
  }

  z3::expr &old_value = this->map_.at(key);

  // Padding shorter bit-vectors is not the right semantics if we assign a
  // larger bitvector into a smaller one. Instead, the assigned value needs to
  // be truncated to the bitsize of the assignee.
  RETURN_IF_ERROR(operators::TruncateBitVectorToFit(old_value, value));

  // This will return an absl error if the sorts are incompatible, and will pad
  // shorter bit vectors.
  ASSIGN_OR_RETURN(auto pair, operators::SortCheckAndPad(value, old_value));
  old_value = pair.first;
  return absl::OkStatus();
}
absl::Status SymbolicGuardedMap::UnguardedSet(absl::string_view header_name,
                                              absl::string_view field_name,
                                              z3::expr value) {
  std::string key = absl::StrFormat("%s.%s", header_name, field_name);
  return UnguardedSet(key, value);
}

}  // namespace symbolic
}  // namespace p4_symbolic
