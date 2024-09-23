// Copyright 2021 Google LLC
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
#ifndef P4_FUZZER_TABLE_ENTRY_KEY_H_
#define P4_FUZZER_TABLE_ENTRY_KEY_H_

#include <algorithm>
#include <vector>

#include "absl/hash/hash.h"
#include "p4/v1/p4runtime.pb.h"

namespace p4_fuzzer {

class TableEntryKey {
 public:
  TableEntryKey(const p4::v1::TableEntry& entry);

  template <typename H>
  friend H AbslHashValue(H h, const TableEntryKey& key);

  bool operator==(const TableEntryKey& other) const {
    // Note: this must match the implementation of hash value below.
    if ((table_id_ != other.table_id_) || (priority_ != other.priority_) ||
        matches_.size() != other.matches_.size()) {
      return false;
    }

    for (int i = 0; i < matches_.size(); i++) {
      const auto& a = matches_[i];
      const auto& b = other.matches_[i];
      if (a.field_id() != b.field_id() ||
          a.exact().value() != b.exact().value() ||
          a.ternary().value() != b.ternary().value() ||
          a.ternary().mask() != b.ternary().mask() ||
          a.lpm().value() != b.lpm().value() ||
          a.lpm().prefix_len() != b.lpm().prefix_len() ||
          a.range().low() != b.range().low() ||
          a.range().high() != b.range().high() ||
          a.optional().value() != b.optional().value())
        return false;
    }
    return true;
  }

 private:
  uint32_t table_id_;
  int32_t priority_;
  std::vector<p4::v1::FieldMatch> matches_;
};

template <typename H>
H AbslHashValue(H h, const TableEntryKey& key) {
  h = H::combine(std::move(h), key.table_id_, key.priority_);

  for (const auto& field : key.matches_) {
    // Since protobufs yield a default value for an unset field and since {
    // exact, ternary, lpm, range, optional } are all part of the oneof
    // directive (i,e only one of them will be set at a given time), we can get
    // a correct hash by combining all fields without checking which one is set.
    h = H::combine(std::move(h), field.field_id(), field.exact().value(),
                   field.ternary().value(), field.ternary().mask(),
                   field.lpm().value(), field.lpm().prefix_len(),
                   field.range().low(), field.range().high(),
                   field.optional().value());
  }

  return h;
}

}  // namespace p4_fuzzer

#endif  // P4_FUZZER_TABLE_ENTRY_KEY_H_
