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
#ifndef PINS_GUTIL_TABLE_ENTRY_KEY_H_
#define PINS_GUTIL_TABLE_ENTRY_KEY_H_

#include <algorithm>
#include <string>
#include <string_view>
#include <vector>

#include "absl/hash/hash.h"
#include "p4/v1/p4runtime.pb.h"

namespace gutil {

class TableEntryKey {
 public:
  TableEntryKey(const p4::v1::TableEntry& entry);
  TableEntryKey() = default;

  template <typename H>
  friend H AbslHashValue(H h, const TableEntryKey& key);

  bool operator==(const TableEntryKey& other) const;

  bool operator<(const TableEntryKey& other) const;

  // Returns vector of non-key field paths in PI TableEntry proto.
  static std::vector<std::string_view> NonKeyFieldPaths();

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

}  // namespace gutil

#endif  // PINS_GUTIL_TABLE_ENTRY_KEY_H_
