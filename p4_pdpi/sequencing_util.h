#ifndef PINS_INFRA_P4_PDPI_SEQUENCING_UTIL_H_
#define PINS_INFRA_P4_PDPI_SEQUENCING_UTIL_H_
#include <string>
#include <utility>
#include <vector>

#include "absl/container/btree_set.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_join.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"

// TODO rename this file to reachability_util.h once reachability
// analysis replaces p4 sequencing.
namespace pdpi {

// Struct to represent a concrete match field with a value that could be
// referred to by another table entry. For example, it is used as a concrete
// match field in a ReferredTableEntry.
struct ReferredField {
  std::string match_field_name;
  std::string value;

  bool operator==(const ReferredField& rhs) const {
    return match_field_name == rhs.match_field_name && value == rhs.value;
  }
  bool operator!=(const ReferredField& rhs) const { return !(*this == rhs); }
  bool operator<(const ReferredField& rhs) const {
    return match_field_name < rhs.match_field_name ||
           (match_field_name == rhs.match_field_name && value < rhs.value);
  }

  // The hash is a concatenation of match field name and match field value.
  // See https://abseil.io/docs/cpp/guides/hash for details about making a
  // struct hashable.
  template <typename H>
  friend H AbslHashValue(H h, const ReferredField& field) {
    return H::combine(std::move(h), field.match_field_name, field.value);
  }
  template <typename Sink>
  friend void AbslStringify(Sink& sink, const ReferredField& referred_field) {
    absl::Format(&sink, "ReferredField{match_field_name: %s,field_value: %s}",
                 referred_field.match_field_name, referred_field.value);
  }
};

// Struct to represent a table entry that can (or is) referred to.
struct ReferredTableEntry {
  std::string table;
  absl::btree_set<ReferredField> referred_fields;

  bool operator==(const ReferredTableEntry& rhs) const {
    return table == rhs.table && referred_fields == rhs.referred_fields;
  }
  bool operator!=(const ReferredTableEntry& rhs) const {
    return !(*this == rhs);
  }
  bool operator<(const ReferredTableEntry& rhs) const {
    return table < rhs.table ||
           (table == rhs.table && referred_fields < rhs.referred_fields);
  }

  // hash value is a concatenation of hash of the table name, match fields names
  // and match fields values.
  // See https://abseil.io/docs/cpp/guides/hash for details about making a
  // struct hashable.
  template <typename H>
  friend H AbslHashValue(H h, const ReferredTableEntry& table_entry) {
    h = H::combine(std::move(h), table_entry.table);
    for (const ReferredField& referred_field : table_entry.referred_fields) {
      h = H::combine(std::move(h), referred_field.match_field_name,
                     referred_field.value);
    }
    return h;
  }

  template <typename Sink>
  friend void AbslStringify(Sink& sink, const ReferredTableEntry& table_entry) {
    absl::Format(
        &sink,
        "ReferredTableEntry{table_name: %s, match_fields and values: [%s]}",
        table_entry.table, absl::StrJoin(table_entry.referred_fields, ", "));
  }
};

// Returns a vector of ReferredTableEntries that `table_entry` refers to.
// What table entries `table_entry` refers to depends on `ir_p4info`'s reference
// fields for the match fields and actions plus the value of the match fields
// and actions.
// This function assumes each `table_entry` can at most refer to 1
// table entry for each table type.
absl::StatusOr<std::vector<ReferredTableEntry>> EntriesReferredToByTableEntry(
    const p4::v1::TableEntry& table_entry, const IrP4Info& ir_p4info);

}  // namespace pdpi

#endif  // PINS_INFRA_P4_PDPI_SEQUENCING_UTIL_H_
