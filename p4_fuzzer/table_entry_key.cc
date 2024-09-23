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
#include "p4_fuzzer/table_entry_key.h"

#include <algorithm>

#include "google/protobuf/util/message_differencer.h"

namespace p4_fuzzer {

using ::p4::v1::FieldMatch;
using ::p4::v1::TableEntry;

TableEntryKey::TableEntryKey(const p4::v1::TableEntry& entry) {
  table_id_ = entry.table_id();
  priority_ = entry.priority();

  auto match = entry.match();
  matches_ = std::vector<FieldMatch>(match.begin(), match.end());
  // Sort matches by field to ensure consistent keys.
  std::sort(matches_.begin(), matches_.end(),
            [](const FieldMatch& a, const FieldMatch& b) {
              return a.field_id() < b.field_id();
            });
}

}  // namespace p4_fuzzer
