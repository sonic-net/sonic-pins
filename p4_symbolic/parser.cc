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

#include "p4_symbolic/parser.h"

#include "gutil/proto.h"
#include "p4_symbolic/bmv2/bmv2.h"
#include "p4_symbolic/ir/ir.h"
#include "p4_symbolic/ir/pdpi_driver.h"
#include "p4_symbolic/util/io.h"

namespace p4_symbolic {

absl::StatusOr<symbolic::Dataplane> ParseToIr(
    const std::string &bmv2_json_path, const std::string &p4info_path,
    const std::string &table_entries_path) {
   // Parse table entries.
   p4::v1::WriteRequest write_request;
   if (!table_entries_path.empty()) {
     RETURN_IF_ERROR(
         gutil::ReadProtoFromFile(table_entries_path.c_str(), &write_request))
             .SetPrepend()
         << "While trying to parse table entry file '" << table_entries_path
         << "': ";
   }
   std::vector<p4::v1::TableEntry> table_entries;
   for (const auto &update : write_request.updates()) {
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
     table_entries.push_back(std::move(entity.table_entry()));
   }
   return ParseToIr(bmv2_json_path, p4info_path, table_entries);
}

absl::StatusOr<symbolic::Dataplane> ParseToIr(
    const std::string &bmv2_json_path, const std::string &p4info_path,
    absl::Span<const p4::v1::TableEntry> table_entries) {
  // Parse bmv2 json file into our initial bmv2 protobuf.
  ASSIGN_OR_RETURN(std::string bmv2_json, util::ReadFile(bmv2_json_path));

  // Parse p4info file into pdpi format.
  ASSIGN_OR_RETURN(pdpi::IrP4Info p4info,
                   p4_symbolic::ir::ParseP4InfoFile(p4info_path),
                   _.SetPrepend() << "While trying to parse p4info file '"
                                  << p4info_path << "': ");
  return ParseToIr(bmv2_json, p4info, table_entries);
}

absl::StatusOr<symbolic::Dataplane> ParseToIr(
    const std::string &bmv2_json, const pdpi::IrP4Info &p4info,
    absl::Span<const p4::v1::TableEntry> table_entries) {
  ASSIGN_OR_RETURN(bmv2::P4Program bmv2, bmv2::ParseBmv2JsonString(bmv2_json),
                   _.SetPrepend() << "While trying to parse BMv2 JSON: ");
  ASSIGN_OR_RETURN(ir::P4Program program, ir::Bmv2AndP4infoToIr(bmv2, p4info));
  ASSIGN_OR_RETURN(ir::TableEntries ir_table_entries,
                   ir::ParseTableEntries(p4info, table_entries));
  return p4_symbolic::symbolic::Dataplane{program, ir_table_entries};
}

}  // namespace p4_symbolic
