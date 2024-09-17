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
#include "gutil/proto.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_symbolic/util/io.h"

namespace p4_symbolic {
namespace ir {

absl::StatusOr<TableEntries> ParseAndFillEntries(
    const pdpi::IrP4Info &p4info, const std::string &entries_path) {
  // Parse table entries as a plain p4.v1.TableEntry proto.
  p4::v1::WriteRequest entries_file;
  RETURN_IF_ERROR(
      gutil::ReadProtoFromFile(entries_path.c_str(), &entries_file));

  // Use pdpi to transform each plain p4.v1.TableEntry to the pd representation
  // pdpi.ir.IrTableEntry.
  TableEntries output;
  for (const p4::v1::Update &update : entries_file.updates()) {
    // Make sure update is of type insert.
    if (update.type() != p4::v1::Update::INSERT) {
      return absl::InvalidArgumentError(
          absl::StrCat("Table entries file contains a non-insert update ",
                       update.DebugString()));
    }

    // Make sure the entity is a table entry.
    const p4::v1::Entity &entity = update.entity();
    if (entity.entity_case() != p4::v1::Entity::kTableEntry) {
      return absl::InvalidArgumentError(
          absl::StrCat("Table entries file contains a non-table entry entity ",
                       entity.DebugString()));
    }

    // Read table entry as a program-independent P4RT protobuf.
    // Transform it to a program dependent pdpi protobuf.
    const p4::v1::TableEntry &pi_entry = entity.table_entry();
    ASSIGN_OR_RETURN(pdpi::IrTableEntry pdpi_entry,
                     pdpi::PiTableEntryToIr(p4info, pi_entry));

    // Replace table and action aliases with their respective full name.
    const std::string &table_alias = pdpi_entry.table_name();
    const std::string &action_alias = pdpi_entry.action().name();

    // Make sure both table and action referred to by entry exist.
    RET_CHECK(p4info.tables_by_name().count(table_alias) == 1);
    RET_CHECK(p4info.actions_by_name().count(action_alias) == 1);

    const std::string &table_name =
        p4info.tables_by_name().at(table_alias).preamble().name();
    const std::string &action_name =
        p4info.actions_by_name().at(action_alias).preamble().name();

    pdpi_entry.mutable_action()->set_name(action_name);
    pdpi_entry.set_table_name(table_name);
    output[pdpi_entry.table_name()].push_back(pdpi_entry);
  }
  return output;
}

}  // namespace ir
}  // namespace p4_symbolic
