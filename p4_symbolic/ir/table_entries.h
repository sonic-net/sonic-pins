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

// This file parses table entries attached to a p4 program, and fills them
// into the IR of that program.

#ifndef P4_SYMBOLIC_IR_TABLE_ENTRIES_H_
#define P4_SYMBOLIC_IR_TABLE_ENTRIES_H_

#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "gutil/status.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_symbolic/ir/ir.pb.h"

namespace p4_symbolic {
namespace ir {

// Table entries by table name.
using TableEntries =
    std::unordered_map<std::string, std::vector<pdpi::IrTableEntry>>;

// Returns table entries in PDPI IR representation, keyed by table name.
absl::StatusOr<TableEntries> ParseTableEntries(
    const pdpi::IrP4Info &p4info, absl::Span<const p4::v1::TableEntry> entries);

}  // namespace ir
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_IR_TABLE_ENTRIES_H_
