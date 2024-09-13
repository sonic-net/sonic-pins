#include "p4_fuzzer/table_entry_key.h"

#include <algorithm>

#include "google/protobuf/util/message_differencer.h"

namespace p4_fuzzer {

using ::google::protobuf::util::MessageDifferencer;
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
