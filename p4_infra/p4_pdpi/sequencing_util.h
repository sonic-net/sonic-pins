// Copyright 2025 Google LLC
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

#ifndef PINS_P4_INFRA_P4_PDPI_SEQUENCING_UTIL_H_
#define PINS_P4_INFRA_P4_PDPI_SEQUENCING_UTIL_H_

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "absl/container/btree_set.h"
#include "absl/container/flat_hash_map.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_join.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"

// TODO rename this file to reachability_util.h once reachability
// analysis replaces p4 sequencing.
namespace pdpi {

struct ReferenceRelationKey {
  // TODO Add referring table id to handle cases where two or
  // more tables refer to the same table and need to form a ReferenceRelationKey
  // for each referring table.
  uint32_t referred_table_id;

  bool operator==(const ReferenceRelationKey& rhs) const {
    return referred_table_id == rhs.referred_table_id;
  }
  bool operator!=(const ReferenceRelationKey& rhs) const {
    return !(*this == rhs);
  }
  bool operator<(const ReferenceRelationKey& rhs) const {
    return referred_table_id < rhs.referred_table_id;
  }
  template <typename H>
  friend H AbslHashValue(H h, const ReferenceRelationKey& key) {
    return H::combine(std::move(h), key.referred_table_id);
  }
  template <typename Sink>
  friend void AbslStringify(Sink& sink, const ReferenceRelationKey& key) {
    absl::Format(&sink, "ReferenceRelationKey{referred_table_id: %v}",
                 key.referred_table_id);
  }
};

// Struct to represent a reference relationship.
// It contains a btree_set of match field ids.
struct ReferenceRelation {
  absl::btree_set<uint32_t> match_field_ids;
  template <typename Sink>
  friend void AbslStringify(Sink& sink, const ReferenceRelation& relation) {
    absl::Format(&sink, "ReferenceRelation{match_field_ids: [%v]}",
                 absl::StrJoin(relation.match_field_ids, ", "));
  }
};

// Struct to represent a concrete match field with a value that could be
// referred to by another table entry. For example, it is used as a concrete
// match field in a ReferredTableEntry.
struct ReferredField {
  uint32_t match_field_id;
  std::string value;

  bool operator==(const ReferredField& rhs) const {
    return match_field_id == rhs.match_field_id && value == rhs.value;
  }
  bool operator!=(const ReferredField& rhs) const { return !(*this == rhs); }
  bool operator<(const ReferredField& rhs) const {
    return match_field_id < rhs.match_field_id ||
           (match_field_id == rhs.match_field_id && value < rhs.value);
  }

  // The hash is a concatenation of match field name and match field value.
  template <typename H>
  friend H AbslHashValue(H h, const ReferredField& field) {
    return H::combine(std::move(h), field.match_field_id, field.value);
  }
  template <typename Sink>
  friend void AbslStringify(Sink& sink, const ReferredField& referred_field) {
    absl::Format(&sink, "ReferredField{match_field_id: %v,field_value: %v}",
                 referred_field.match_field_id, referred_field.value);
  }
};

// Struct to represent a table entry that can (or is) referred to.
struct ReferredTableEntry {
  uint32_t table_id;
  absl::btree_set<ReferredField> referred_fields;

  bool operator==(const ReferredTableEntry& rhs) const {
    return table_id == rhs.table_id && referred_fields == rhs.referred_fields;
  }
  bool operator!=(const ReferredTableEntry& rhs) const {
    return !(*this == rhs);
  }
  bool operator<(const ReferredTableEntry& rhs) const {
    return table_id < rhs.table_id ||
           (table_id == rhs.table_id && referred_fields < rhs.referred_fields);
  }

  // hash value is a concatenation of hash of the table id, match fields names
  // and match fields values.
  template <typename H>
  friend H AbslHashValue(H h, const ReferredTableEntry& table_entry) {
    h = H::combine(std::move(h), table_entry.table_id);
    for (const ReferredField& referred_field : table_entry.referred_fields) {
      h = H::combine(std::move(h), referred_field.match_field_id,
                     referred_field.value);
    }
    return h;
  }

  template <typename Sink>
  friend void AbslStringify(Sink& sink, const ReferredTableEntry& table_entry) {
    absl::Format(
        &sink,
        "ReferredTableEntry{table_id: %v, match_fields and values: [%v]}",
        table_entry.table_id, absl::StrJoin(table_entry.referred_fields, ", "));
  }
};

// Returns a map from table ids to the match fields that the table contains
// that can be referred to.
absl::flat_hash_map<ReferenceRelationKey, ReferenceRelation>
CreateReferenceRelations(const IrP4Info& ir_p4info);

// Returns a vector of ReferredTableEntries that `table_entry` refers to.
// What table entries `table_entry` refers to depends on `ir_p4info`'s reference
// fields for the match fields and actions plus the value of the match fields
// and actions.
// This function assumes each `table_entry` can at most refer to 1
// table entry for each table type.
absl::StatusOr<std::vector<ReferredTableEntry>> EntriesReferredToByTableEntry(
    const IrP4Info& ir_p4info, const p4::v1::TableEntry& table_entry);

// Returns a ReferredTableEntry representation of `table_entry` that could be
// referred to by other table entries based on `reference_relations`.
// If `table_entry` can't be referred to by any table, returns an error.
absl::StatusOr<ReferredTableEntry> CreateReferrableTableEntry(
    const IrP4Info& ir_p4info,
    const absl::flat_hash_map<ReferenceRelationKey, ReferenceRelation>&
        reference_relations,
    const p4::v1::TableEntry& table_entry);

}  // namespace pdpi

#endif  // PINS_P4_INFRA_P4_PDPI_SEQUENCING_UTIL_H_
