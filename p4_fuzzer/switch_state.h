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
#ifndef P4_FUZZER_SWITCH_STATE_H_
#define P4_FUZZER_SWITCH_STATE_H_

#include <cstdint>
#include <cstdio>
#include <functional>
#include <optional>
#include <string>
#include <unordered_map>
#include <vector>

#include "absl/container/btree_map.h"
#include "absl/container/flat_hash_map.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/types/optional.h"
#include "absl/types/span.h"
#include "gutil/collections.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/entity_keys.h"
#include "p4_pdpi/ir.pb.h"

namespace p4_fuzzer {

// Statistics to track current resource usage.
struct ResourceStatistics {
  // Statistic used by all tables.
  int entries = 0;
  // Statistic used by tables with action profiles and multicast group entries.
  int total_members = 0;
  // Statistic only used by tables with action profiles.
  int total_weight = 0;
};

// Statistics to track peak resource usage for each table.
struct PeakResourceStatistics {
  // Statistic used by all tables.
  int entries = 0;
  // Statistics used by tables with action profiles and multicast group entries.
  int total_members = 0;
  int max_members_per_group = 0;
  // Statistics only used by tables with action profiles.
  int total_weight = 0;
  int max_group_weight = 0;
};

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
// A map from table key field names to their values in a singular entry. Used
// to determine valid references for use with @refers_to annotations.
using ReferableEntry = absl::flat_hash_map<std::string, std::string>;

// Returns the canonical form of `entry` according to the P4 Runtime Spec
// https://s3-us-west-2.amazonaws.com/p4runtime/ci/main/P4Runtime-Spec.html#sec-bytestrings.
// TODO: Canonical form is achieved by performing an IR roundtrip
// translation. This ties correctness to IR functionality. Local
// canonicalization would be preferred.
absl::StatusOr<p4::v1::TableEntry>
CanonicalizeTableEntry(const pdpi::IrP4Info &info,
                       const p4::v1::TableEntry &entry, bool key_only);

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

  // Returns OK if applying the `pi_update` into its table  could cause a
  // resource exhaustion, and a FailedPrecondition error if the update should
  // fit within the table's resources.
  //
  // Keep in mind sizes for P4 tables are minimum guarantees. So while this
  // method may suggest seeing a ResourceExhausted is expected (i.e. return OK),
  // an actual switch may still accept the update.
  absl::Status ResourceExhaustedIsAllowed(
      const p4::v1::Update& pi_update) const;

  // Checks whether all P4 tables are empty.
  bool AllP4TablesEmpty() const;

  // Returns true if the table is empty.
  bool IsTableEmpty(const uint32_t table_id) const;

  // Returns true iff the given table can accommodate at least n more entries.
  bool CanAccommodateInserts(const uint32_t table_id, const int n) const;

  // Returns `OrderedTableEntries` map for given `table_id`. Returns const ref
  // to map representation to avoid copying entries. If an invalid id is
  // provided, program will crash.
  const OrderedTableEntries &GetTableEntries(const uint32_t table_id) const {
    return gutil::FindOrDie(ordered_tables_, table_id);
  }

  // Returns the number of table entries in a given table.
  int64_t GetNumTableEntries(const uint32_t table_id) const;

  // Returns the total number of table entries in all tables.
  int64_t GetNumTableEntries() const;

  // Returns the number of multicast group entries.
  int64_t GetNumMulticastEntries() const {
    return ordered_multicast_entries_.size();
  };

  // Returns the current state of an entity (or nullopt if it is not
  // present).  Only the uniquely identifying fields of `entity` are considered.
  std::optional<p4::v1::Entity> GetEntity(const p4::v1::Entity &entity) const;

  // Returns the current state of a table entry (or nullopt if it is not
  // present).  Only the uniquely identifying fields of entry are considered.
  std::optional<p4::v1::TableEntry>
  GetTableEntry(const p4::v1::TableEntry &entry) const;

  // Returns the current state of a multicast group entry (or nullopt if it is
  // not present). Only multicast_group_id is considered when retrieving entry.
  std::optional<p4::v1::MulticastGroupEntry>
  GetMulticastGroupEntry(const p4::v1::MulticastGroupEntry &entry) const;

  // Returns all multicast group entries.
  const absl::btree_map<int, p4::v1::MulticastGroupEntry> &
  GetMulticastGroupEntries() const {
    return ordered_multicast_entries_;
  }

  // Returns the list of all non-const table IDs in the underlying P4 program.
  std::vector<uint32_t> AllTableIds() const;

  // Applies the given update to the given table entries. Assumes that all
  // updates can actually be applied successfully e.g for INSERT, an entry
  // cannot already be present, and returns an error otherwise. If this function
  // returns an error, switch state will be in an inconsistent state and no
  // longer valid.
  absl::Status ApplyUpdate(const p4::v1::Update &update);

  // Returns the max resource statistics for table with id `table_id`. Returns
  // error if such a table does not exist.
  absl::StatusOr<PeakResourceStatistics>
  GetPeakResourceStatistics(int table_id) const;

  // Returns the peak multicast group table resource statistics.
  PeakResourceStatistics GetPeakMulticastResourceStatistics() const {
    return peak_multicast_resource_statistics_;
  }

  // Returns max number of entries seen on the switch.
  int GetMaxEntriesSeen() const { return peak_entries_seen_; }

  // Updates all tables to match the given set of entities.
  absl::Status SetEntities(absl::Span<const p4::v1::Entity> entities);

  // Clears all table entries.
  void ClearTableEntries();

  // Returns a summary of the state.
  std::string SwitchStateSummary() const;

  pdpi::IrP4Info GetIrP4Info() const { return ir_p4info_; }

  // Used in testing to check that SwitchState is always consistent by:
  // - Ensuring that the ordered and unordered table states are in sync.
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
      const std::vector<p4::v1::TableEntry> &switch_entries,
      std::optional<std::function<bool(const pdpi::IrTableEntry &,
                                       const pdpi::IrTableEntry &)>>
          TreatAsEqualDueToKnownBug = std::nullopt) const;

private:
  // A map from table ids to the entries they store.
  // Invariant: An entry, `e`, is represented in `ordered_tables_` <=> e is also
  // represented in `unordered_tables_`.
  // TODO: b/316624852 - Update underlying map structures so guarantee
  // supporting 2^64 entries.
  absl::flat_hash_map<int, OrderedTableEntries> ordered_tables_;
  absl::flat_hash_map<int, UnorderedTableEntries> unordered_tables_;

  absl::Status UpdateResourceStatistics(const p4::v1::TableEntry &entry,
                                        p4::v1::Update::Type type);

  // Tracks current resource usage by table.
  absl::flat_hash_map<int, ResourceStatistics> current_resource_statistics_;
  int current_entries_ = 0;
  // Tracks peak resource usage by table.
  absl::flat_hash_map<int, PeakResourceStatistics> peak_resource_statistics_;
  // Tracks peak resource usage of entire switch.
  int peak_entries_seen_ = 0;

  absl::Status UpdateMulticastResourceStatistics(
      const p4::v1::MulticastGroupEntry& entry, p4::v1::Update::Type type);

  // Tracks current multicast resource usage.
  ResourceStatistics current_multicast_resource_statistics_;
  // Tracks peak multicast resource usage.
  PeakResourceStatistics peak_multicast_resource_statistics_;

  // Internal overload used to apply multicast updates.
  absl::Status ApplyMulticastUpdate(const p4::v1::Update &update);
  // Multicast group entries are keyed by their multicast group id.
  // Btree copy used for deterministic ordering.
  absl::btree_map<int, p4::v1::MulticastGroupEntry> ordered_multicast_entries_;
  // Copy of above used for fast lookups.
  absl::flat_hash_map<int, p4::v1::MulticastGroupEntry>
      unordered_multicast_entries_;

  pdpi::IrP4Info ir_p4info_;
};

} // namespace p4_fuzzer

#endif // P4_FUZZER_SWITCH_STATE_H_
