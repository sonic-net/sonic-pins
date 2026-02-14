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

#include <string>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/types/span.h"
#include "gutil/gutil/status.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/names.h"
#include "p4_symbolic/ir/ir.pb.h"

namespace p4_symbolic {
namespace ir {

namespace {

absl::Status UseFullyQualifiedTableName(const pdpi::IrP4Info &p4info,
                                        pdpi::IrTableEntry &entry) {
  auto &alias = entry.table_name();
  RET_CHECK(p4info.tables_by_name().count(alias) == 1)
      << "where alias = '" << alias << "' and IR table entry =\n"
      << absl::StrCat(entry);
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
         << absl::StrCat(entry);
}

absl::Status UseFullyQualifiedNamesInEntity(const pdpi::IrP4Info &info,
                                            pdpi::IrEntity &entity) {
  switch (entity.entity_case()) {
    case pdpi::IrEntity::kTableEntry:
      return UseFullyQualifiedNamesInEntry(info, *entity.mutable_table_entry());
    default:
      return absl::OkStatus();
  }
}

}  // namespace

absl::StatusOr<TableEntries> ParseTableEntries(
    const pdpi::IrP4Info &p4info, absl::Span<const p4::v1::Entity> entities) {
  // Use pdpi to transform each plain p4.v1.TableEntry to the pd representation
  // pdpi.ir.IrTableEntry.
  TableEntries output;
  for (const p4::v1::Entity &pi_entity : entities) {
    ASSIGN_OR_RETURN(
        pdpi::IrEntity ir_entity,
        pdpi::PiEntityToIr(p4info, pi_entity, {.allow_unsupported = true}));
    // TODO: Consider removing this function call if we switch to
    // using aliases as table/action names in P4-Symbolic.
    RETURN_IF_ERROR(UseFullyQualifiedNamesInEntity(p4info, ir_entity));
    ASSIGN_OR_RETURN(std::string table_name,
                     pdpi::EntityToTableName(ir_entity));

    std::vector<TableEntry> &output_entries = output[std::move(table_name)];
    int index = output_entries.size();
    ConcreteTableEntry &output_entry =
        *output_entries.emplace_back().mutable_concrete_entry();
    output_entry.set_index(index);
    *output_entry.mutable_pdpi_ir_entity() = std::move(ir_entity);
  }
  return output;
}

}  // namespace ir
}  // namespace p4_symbolic
