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
#ifndef P4_FUZZER_SWITCH_STATE_H_
#define P4_FUZZER_SWITCH_STATE_H_

#include <cstdio>
#include <functional>
#include <optional>
#include <string>
#include <unordered_map>
#include <vector>

#include "absl/container/btree_map.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/types/optional.h"
#include "glog/logging.h"
#include "gutil/status.h"
#include "gutil/collections.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/entity_keys.h"
#include "p4_pdpi/ir.pb.h"

namespace p4_fuzzer {

// Only a subset of the fields of TableEntry are used for equality in P4Runtime
// (as part of the class TableEntryKey). We use an instance of TableEntryKey
// generated from a TableEntry as the key in an absl::btree_map.
// Therefore, the class SwitchState must preserve the invariant that:
//   forall t1, t2. table_[t1] = t2  ==> t1 = TableEntryKey(t2)
//   TableEntryKey() here is the constructor for the class TableEntryKey.
// Btree copy used for deterministic ordering.
using OrderedTableEntries =
    absl::btree_map<pdpi::TableEntryKey, p4::v1::TableEntry>;
// Copy of above used for fast lookups.
using UnorderedTableEntries =
    absl::flat_hash_map<pdpi::TableEntryKey, p4::v1::TableEntry>;

using ::gutil::FindOrDie;

// A map from table key field names to their values in a singular entry. Used
// to determine valid references for use with @refers_to annotations.
using ReferableEntry = absl::flat_hash_map<std::string, std::string>;

// Returns the canonical form of `entry` according to the P4 Runtime Spec
// https://s3-us-west-2.amazonaws.com/p4runtime/ci/main/P4Runtime-Spec.html#sec-bytestrings.
// TODO: Canonical form is achieved by performing an IR roundtrip
// translation. This ties correctness to IR functionality. Local
// canonicalization would be preferred.
absl::StatusOr<p4::v1::TableEntry> CanonicalizeTableEntry(
    const pdpi::IrP4Info& info, const p4::v1::TableEntry& entry, bool key_only);

// Tracks the state of a switch, with methods to apply updates or query the
// current state. The class assumes all calls are valid (e.g table_ids must all
// exist). Crashes if that is not the case.
class SwitchState {
 public:
  // SwitchState needs to know the (PDPI internal representation of the) P4Info
  // of the P4 program P4 fuzzer is fuzzing in order to implement its functions
  // in a program independent manner.
  SwitchState(pdpi::IrP4Info ir_p4info);

  // Returns true if the table is at its resource limit. This means that there
  // is no guarantee that any further entry will fit into this table. Whether
  // or not a table is full, may depend on the entries in other tables as well.
  bool IsTableFull(const uint32_t table_id) const;

  // Checks whether the given set of table entries is empty.
  bool AllTablesEmpty() const;

  // Returns true if the table is empty.
  bool IsTableEmpty(const uint32_t table_id) const;

  // Returns true iff the given table can accommodate at least n more entries.
  bool CanAccommodateInserts(const uint32_t table_id, const int n) const;

  // Returns `OrderedTableEntries` map for given `table_id`. Returns const ref
  // to map representation to avoid copying entries. If an invalid id is
  // provided, program will crash.
  const OrderedTableEntries& GetTableEntries(const uint32_t table_id) const {
    return gutil::FindOrDie(ordered_tables_, table_id);
  }

  // Returns all table entries in a given canonical table.
  std::vector<p4::v1::TableEntry> GetCanonicalTableEntries(
      const uint32_t table_id) const;

  // Returns the number of table entries in a given table.
  int64_t GetNumTableEntries(const uint32_t table_id) const;

  // Returns the total number of table entries in all tables.
  int64_t GetNumTableEntries() const;

  // Returns the current state of a table entry (or nullopt if it is not
  // present).  Only the uniquely identifying fields of entry are considered.
  std::optional<p4::v1::TableEntry> GetTableEntry(
      const p4::v1::TableEntry& entry) const;

  // Returns the current state of a canonical table entry (or nullopt if it is
  // not present). Only the uniquely identifying fields of entry are considered.
  std::optional<p4::v1::TableEntry> GetCanonicalTableEntry(
      const p4::v1::TableEntry& entry) const;

  // Returns the list of all non-const table IDs in the underlying P4 program.
  const std::vector<uint32_t> AllTableIds() const;

  // Applies the given update to the given table entries. Assumes that all
  // updates can actually be applied successfully e.g for INSERT, an entry
  // cannot already be present, and returns an error otherwise.
  absl::Status ApplyUpdate(const p4::v1::Update& update);

  // Updates all tables to match the given set of table entries.
  absl::Status SetTableEntries(
      absl::Span<const p4::v1::TableEntry> table_entries);

  // Clears all table entries. Equivalent to constructing a new `SwitchState`
  // object.
  void ClearTableEntries();

  // Returns a summary of the state.
  std::string SwitchStateSummary() const;

  // Returns a vector of `ReferableEntries` in `table`. Used when a match key or
  // action refers to a set of `fields` in `table`. Returns an error if:
  // 1) `table` does not exist in p4 info.
  // 2) `fields` is empty.
  // 3) `fields` contains a field that does not exist in `table`.
  // 4) `fields` contains a field that is not of type exact or optional.
  absl::StatusOr<std::vector<ReferableEntry>> GetReferableEntries(
      absl::string_view table,
      const absl::flat_hash_set<std::string>& fields) const;

  // Returns a vector of `ReferableEntries` in `table`. Used when a match key or
  // action refers to a set of `fields` in `table`. Returns an error if:
  // 1) `table` does not exist in p4 info.
  // 2) `fields` is empty.
  // 3) `fields` contains a field that does not exist in `table`.
  // 4) `fields` contains a field that is not of type exact or optional.
  absl::StatusOr<std::vector<ReferableEntry>> GetReferableEntries(
      absl::string_view table,
      const absl::flat_hash_set<std::string>& fields) const;

  pdpi::IrP4Info GetIrP4Info() const { return ir_p4info_; }

  // Used in testing to check that SwitchState is always consistent by:
  // - Ensuring that the standard and canonical table states are in sync.
  absl::Status CheckConsistency() const;

  // Returns OK if the set of elements in `switch_entries` is equal to
  // the set of all canonical entries in SwitchState. Returns
  // FailedPreconditionError if there are differences. Status message records 3
  // types of differences:
  //   1. Entry is in `switch_entries`, but not in fuzzer state.
  //   2. Entry key is present in both, but value is different.
  //   3. Entry is not in `switch_entries`, but in fuzzer state.
  // Returns InvalidArgumentError if any difference cannot be translated to an
  // IR representation.
  // An optional functor `TreatAsEqualDueToKnownBug` can be used to mask known
  // bugs when comparing entries with the same `TableEntryKey`.
  absl::Status AssertEntriesAreEqualToState(
      const std::vector<p4::v1::TableEntry>& switch_entries,
      std::optional<std::function<bool(const pdpi::IrTableEntry&,
                                       const pdpi::IrTableEntry&)>>
          TreatAsEqualDueToKnownBug = std::nullopt) const;

 private:
  // A map from table ids to the entries they store.
  // Invariant: An entry, `e`, is represented in `tables_` <=> canonical(e) is
  // represented in `canonical_tables_`.
  absl::flat_hash_map<int, OrderedTableEntries> ordered_tables_;
  absl::flat_hash_map<int, UnorderedTableEntries> unordered_tables_;
  pdpi::IrP4Info ir_p4info_;
};

}  // namespace p4_fuzzer

#endif  // P4_FUZZER_SWITCH_STATE_H_
