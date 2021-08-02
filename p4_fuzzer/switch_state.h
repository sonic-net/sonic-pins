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
#include <string>
#include <unordered_map>

#include "absl/container/flat_hash_map.h"
#include "absl/container/node_hash_map.h"
#include "absl/status/status.h"
#include "absl/types/optional.h"
#include "glog/logging.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_fuzzer/table_entry_key.h"
#include "p4_pdpi/ir.pb.h"

namespace p4_fuzzer {

// Only a subset of the fields of TableEntry are used for equality in P4Runtime
// (as part of the class TableEntryKey). We use an instance of TableEntryKey
// generated from a TableEntry as the key in an absl::node_hash_map.
// Therefore, the class SwitchState must preserve the invariant that:
//   forall t1, t2. table_[t1] = t2  ==> t1 = TableEntryKey(t2)
//   TableEntryKey() here is the constructor for the class TableEntryKey.
using TableEntries = absl::node_hash_map<TableEntryKey, p4::v1::TableEntry>;

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

  // Returns all table entries in a given table.
  std::vector<p4::v1::TableEntry> GetTableEntries(
      const uint32_t table_id) const;

  // Returns the number of table entries in a given table.
  int64_t GetNumTableEntries(const uint32_t table_id) const;

  // Returns the total number of table entries in all tables.
  int64_t GetNumTableEntries() const;

  // Returns the current state of a table entry (or nullopt if it is not
  // present).  Only the uniquely identifying fields of entry are considered.
  absl::optional<p4::v1::TableEntry> GetTableEntry(
      p4::v1::TableEntry entry) const;

  // Returns the list of all non-const table IDs in the underlying P4 program.
  const std::vector<uint32_t> AllTableIds() const;

  // Applies the given update to the given table entries. Assumes that all
  // updates can actually be applied successfully e.g for INSERT, an entry
  // cannot already be present, and returns an error otherwise.
  absl::Status ApplyUpdate(const p4::v1::Update& update);

  // Returns a summary of the state.
  std::string SwitchStateSummary() const;

 private:
  // A map from table ids to the entries they store.
  absl::flat_hash_map<int, TableEntries> tables_;

  pdpi::IrP4Info ir_p4info_;
};

}  // namespace p4_fuzzer

#endif  // P4_FUZZER_SWITCH_STATE_H_
