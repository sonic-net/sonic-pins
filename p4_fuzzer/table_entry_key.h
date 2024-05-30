#ifndef P4_FUZZER_TABLE_ENTRY_KEY_H_
#define P4_FUZZER_TABLE_ENTRY_KEY_H_

#include <vector>

#include "absl/hash/hash.h"
#include "p4/v1/p4runtime.pb.h"

namespace p4_fuzzer {

class TableEntryKey {
 public:
  TableEntryKey(const p4::v1::TableEntry& entry);

  template <typename H>
  friend H AbslHashValue(H h, const TableEntryKey& key);

  bool operator==(const TableEntryKey& other) const;

 private:
  uint32_t table_id_;
  int32_t priority_;
  std::vector<p4::v1::FieldMatch> matches_;
};

template <typename H>
H AbslHashValue(H h, const TableEntryKey& key) {
  h = H::combine(std::move(h), key.table_id_, key.priority_);

  for (auto field : key.matches_) {
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
