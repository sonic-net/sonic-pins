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

// This file defines the API for transforming a bmv2 protobuf (representing
// the input bmv2 json file) together with a pdpi protobuf (representing the
// p4info file) into our IR protobuf for consumption.

#ifndef P4_SYMBOLIC_IR_IR_H_
#define P4_SYMBOLIC_IR_IR_H_

#include <cstddef>
#include <optional>
#include <string>

#include "absl/log/log.h"
#include "absl/status/statusor.h"
#include "google/protobuf/repeated_ptr_field.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_symbolic/bmv2/bmv2.pb.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/ir/table_entries.h"

namespace p4_symbolic::ir {

// The dataplane configuration of the switch.
// Used as input to our symbolic pipeline.
struct Dataplane {
  P4Program program;
  // Maps the full name of a table to a list of its entries.
  TableEntries entries;
};

struct TableEntryPriorityParams {
  // Must be set to a non-zero value if and only if the match key includes a
  // P4Runtime optional, ternary, or range match.
  int priority = 0;
  // Must be set if and only if `priority == 0` and the match key includes
  // exactly 1 P4Runtime LPM match. If set, must have a non-negative value.
  std::optional<size_t> prefix_length;
};

// A special control name indicating the end of execution in a pipeline
// in P4-Symbolic's IR.
inline std::string EndOfPipeline() { return "__END_OF_PIPELINE__"; }

// A special parse state name indicating the end of execution in a parser in
// P4-Symbolic's IR. We decided to keep the parser CFG separated from the
// pipeline CFG for the symbolic evaluation.
inline std::string EndOfParser() { return "__END_OF_PARSER__"; }

// For any table application, BMv2 JSON (and P4-Symbolic IR) use a map from
// actions that may be executed as a result of table application to the next
// table/control that must be evaluated if the corresponding action is executed.
// This encodes conditionals on the result of table applications in P4 code.
// There are also two special action names that refer to whether any table
// entry was hit (table hit) or no table entry was hit (table miss). The
// following two functions return those special action names.
inline std::string TableHitAction() { return "__HIT__"; }
inline std::string TableMissAction() { return "__MISS__"; }

// Transforms bmv2 protobuf and pdpi protobuf into our IR protobuf.
absl::StatusOr<P4Program> Bmv2AndP4infoToIr(const bmv2::P4Program& bmv2,
                                            const pdpi::IrP4Info& pdpi);

// Returns a fully symbolic IR table entry for the given `table`.
// All matches will be specified as a symbolic match.
// If the given `table` has ternary or optional matches,
// `priority_params.priority` must be provided with a positive value, and it is
// set concretely in the table entry for deterministic entry priority. Otherwise
// the priority must be 0. If the given `table` has no ternary or optional
// matches, and has exactly 1 LPM match with zero or more exact matches,
// `priority_params.prefix_length` must be provided with a non-negative value,
// and it is set concretely in the table entry for deterministic entry priority.
absl::StatusOr<ir::SymbolicTableEntry> CreateSymbolicIrTableEntry(
    int table_entry_index, const ir::Table& table,
    const TableEntryPriorityParams& priority_params = {});

// The original index of this entry within the user-provided list of entries,
// restricted to entries in the same table only.
// Useful as a unique ID in formula generation and in user-facing messages.
int GetIndex(const TableEntry& entry);

std::string GetTableName(const TableEntry& entry);
std::string GetTableName(const ConcreteTableEntry& entry);
std::string GetTableName(const SymbolicTableEntry& entry);

// The priority of the given table entry, or 0 if the table doesn't support
// priorities.
int GetPriority(const TableEntry& entry);

}  // namespace p4_symbolic::ir

#endif  // P4_SYMBOLIC_IR_IR_H_
