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

#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "p4_symbolic/symbolic/operators.h"
#include "p4_symbolic/symbolic/util.h"

namespace p4_symbolic {
namespace symbolic {

absl::StatusOr<SymbolicGuardedMap> SymbolicGuardedMap::CreateSymbolicGuardedMap(
    const google::protobuf::Map<std::string, ir::HeaderType> &headers) {
  ASSIGN_OR_RETURN(auto map, util::FreeSymbolicHeaders(headers));
  return SymbolicGuardedMap(map);
}

bool SymbolicGuardedMap::ContainsKey(const std::string &key) const {
  return this->map_.count(key) == 1;
}

absl::StatusOr<z3::expr> SymbolicGuardedMap::Get(const std::string &key) const {
  if (this->ContainsKey(key)) {
    return this->map_.at(key);
  }

  return absl::InvalidArgumentError(
      absl::StrCat("Cannot find key \"", key, "\" in SymbolicGuardedMap!"));
}

absl::Status SymbolicGuardedMap::Set(const std::string &key,
                                     const z3::expr &value,
                                     const z3::expr &guard) {
  if (!this->ContainsKey(key)) {
    return absl::InvalidArgumentError(absl::StrCat(
        "Cannot assign to key \"", key, "\" in SymbolicGuardedMap!"));
  }

  z3::expr &old_value = this->map_.at(key);

  // operators::Ite will check for sort compatibility and pad when needed.
  // However, Ite() does not have a notion of pre-defined size, and will padd
  // to the maximum bitsize of the two operands. We perform that check
  // explicitly here.
  if (old_value.get_sort().is_bv() && value.get_sort().is_bv()) {
    unsigned int new_size = value.get_sort().bv_size();
    unsigned int old_size = old_value.get_sort().bv_size();
    if (new_size > old_size) {
      return absl::InvalidArgumentError(
          absl::StrFormat("Cannot assign to key \"%s\" a value whose bit size "
                          "%d is greater than the pre-defined bit size %d in "
                          "SymbolicGuardedMap!",
                          key, new_size, old_size));
    }
  }

  // This will return an absl error if the sorts are incompatible, and will pad
  // shorter bit vectors.
  ASSIGN_OR_RETURN(old_value, operators::Ite(guard, value, old_value));
  return absl::OkStatus();
}

}  // namespace symbolic
}  // namespace p4_symbolic
