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

#include "p4_symbolic/ir/table_entries.h"

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_split.h"
#include "gutil/io.h"
#include "gutil/status.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"

namespace p4_symbolic {
namespace ir {

namespace {

absl::Status UseFullyQualifiedTableName(const pdpi::IrP4Info &p4info,
                                        pdpi::IrTableEntry &entry) {
  auto &alias = entry.table_name();
  RET_CHECK(p4info.tables_by_name().count(alias) == 1)
      << "where alias = '" << alias << "' and IR table entry =\n"
      << entry.DebugString();
  auto &full_name = p4info.tables_by_name().at(alias).preamble().name();
  entry.set_table_name(full_name);
  return absl::OkStatus();
}

absl::Status UseFullyQualifiedActionName(const pdpi::IrP4Info &p4info,
                                         pdpi::IrActionInvocation &action) {
  auto &alias = action.name();
  RET_CHECK(p4info.actions_by_name().count(alias) == 1)
      << "where alias = '" << alias;
  auto &full_name = p4info.actions_by_name().at(alias).preamble().name();
  action.set_name(full_name);
  return absl::OkStatus();
}

absl::Status UseFullyQualifiedNamesInEntry(const pdpi::IrP4Info &info,
                                           pdpi::IrTableEntry &entry) {
  RETURN_IF_ERROR(UseFullyQualifiedTableName(info, entry));
  switch (entry.type_case()) {
    case pdpi::IrTableEntry::kAction:
      return UseFullyQualifiedActionName(info, *entry.mutable_action());
    case pdpi::IrTableEntry::kActionSet:
      for (auto &action : *entry.mutable_action_set()->mutable_actions()) {
        RETURN_IF_ERROR(
            UseFullyQualifiedActionName(info, *action.mutable_action()));
      }
      return absl::OkStatus();
    default:
      break;
  }
  return gutil::InvalidArgumentErrorBuilder()
         << "unexpected or missing action in table entry: "
         << entry.DebugString();
}

}  // namespace

absl::StatusOr<TableEntries> ParseTableEntries(
    const pdpi::IrP4Info &p4info,
    absl::Span<const p4::v1::TableEntry> entries) {
  // Use pdpi to transform each plain p4.v1.TableEntry to the pd representation
  // pdpi.ir.IrTableEntry.
  TableEntries output;
  for (const p4::v1::TableEntry &pi_entry : entries) {
    ASSIGN_OR_RETURN(pdpi::IrTableEntry pdpi_entry,
                     pdpi::PiTableEntryToIr(p4info, pi_entry));
    RETURN_IF_ERROR(UseFullyQualifiedNamesInEntry(p4info, pdpi_entry));
    output[pdpi_entry.table_name()].push_back(pdpi_entry);
  }
  return output;
}

}  // namespace ir
}  // namespace p4_symbolic
