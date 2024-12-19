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

#ifndef P4_SYMBOLIC_SYMBOLIC_GUARDED_MAP_H_
#define P4_SYMBOLIC_SYMBOLIC_GUARDED_MAP_H_

#include <string>

#include "absl/container/btree_map.h"
#include "absl/status/status.h"
#include "google/protobuf/map.h"
#include "gutil/status.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {

// This class wraps around an internal absl::btree_map instance,
// while enforcing the following:
// 1. This class can only be instantiated with an instance of the IR
//    header definitions. The resulting instance will be initialized
//    to have exactly the same keys as the fields defined in those header
//    definitions. These keys are initially mapped to free symbolic variables,
//    with the same sort (including bitsize) described in the definitions.
// 2. This class supports a const reference .Get(<key>), which returns
//    an absl error if the key is not found in the map.
// 3. This class allows mutation via .Set(<key>, <value>, <guard>), which
//    sets the value of the key to z3::ite(<guard>, <value>, <old value>),
//    after checking that the sort of <value> matches the sort of <old value>
//    modulo padding.
//
// As such, this class provides the following safety properties:
// 1. Once initialized, the class has a fixed set of keys.
// 2. A value mapped by a key always has the same sort.
// 3. A value can only be assigned to a key given a guard.
//
class SymbolicGuardedMap {
 public:
  // Constructor requires passing the headers definition and will fill the map
  // with a free symbolic variable per header field.
  static absl::StatusOr<SymbolicGuardedMap> CreateSymbolicGuardedMap(
      const google::protobuf::Map<std::string, ir::HeaderType> &headers);

  // Explicitly copyable and movable!
  SymbolicGuardedMap(const SymbolicGuardedMap &other) = default;
  SymbolicGuardedMap(SymbolicGuardedMap &&other) = default;

  // Not assignable.
  SymbolicGuardedMap &operator=(const SymbolicGuardedMap &other) = delete;
  SymbolicGuardedMap &operator=(SymbolicGuardedMap &&other) = delete;

  // Getters.
  bool ContainsKey(absl::string_view key) const;
  absl::StatusOr<z3::expr> Get(absl::string_view key) const;
  absl::StatusOr<z3::expr> Get(absl::string_view header_name,
                               absl::string_view field_name) const;

  // Guarded setters.
  // Returns an error if the assigned value has incompatible sort with the
  // predefined value.
  absl::Status Set(absl::string_view key, z3::expr value,
                   const z3::expr &guard);
  absl::Status Set(absl::string_view header_name, absl::string_view field_name,
                   z3::expr value, const z3::expr &guard);

  // Unguarded setters.
  // Returns an error if the assigned value has incompatible sort with the
  // predefined value. These overwrite the old values in the map. Use with
  // caution!
  absl::Status UnguardedSet(absl::string_view key, z3::expr value);
  absl::Status UnguardedSet(absl::string_view header_name,
                            absl::string_view field_name, z3::expr value);

  // Constant iterators.
  using const_iterator = absl::btree_map<std::string, z3::expr>::const_iterator;
  const_iterator begin() const noexcept { return this->map_.cbegin(); }
  const_iterator end() const noexcept { return this->map_.cend(); }

 private:
  // The underlying map storing the keys and their values.
  absl::btree_map<std::string, z3::expr> map_;

  // Private constructor used by factory.
  explicit SymbolicGuardedMap(absl::btree_map<std::string, z3::expr> map)
      : map_(map) {}
};

}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_GUARDED_MAP_H_
