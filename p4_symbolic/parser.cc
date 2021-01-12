// Copyright 2020 Google LLC
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

#include "p4_symbolic/bmv2/bmv2.h"
#include "p4_symbolic/ir/ir.h"
#include "p4_symbolic/ir/pdpi_driver.h"

namespace p4_symbolic {

absl::StatusOr<symbolic::Dataplane> ParseToIr(
    const std::string &bmv2_path, const std::string &p4info_path,
    const std::string &table_entries_path) {
  // Parse p4info file into pdpi format.
  ASSIGN_OR_RETURN(pdpi::IrP4Info p4info,
                   p4_symbolic::ir::ParseP4InfoFile(p4info_path),
                   _.SetPrepend() << "While trying to parse p4info file '"
                                  << p4info_path << "': ");

  // Parse bmv2 json file into our initial bmv2 protobuf.
  ASSIGN_OR_RETURN(bmv2::P4Program bmv2, bmv2::ParseBmv2JsonFile(bmv2_path),
                   _.SetPrepend() << "While trying to parse BMv2 json file '"
                                  << bmv2_path << "': ");

  // Parse table entries.
  p4_symbolic::ir::TableEntries table_entries;
  if (!table_entries_path.empty()) {
    ASSIGN_OR_RETURN(
        table_entries, ir::ParseAndFillEntries(p4info, table_entries_path),
        _.SetPrepend() << "While trying to parse table entry file '"
                       << table_entries_path << "': ");
  }

  // Transform all above into our IR.
  ASSIGN_OR_RETURN(ir::P4Program program, ir::Bmv2AndP4infoToIr(bmv2, p4info));

  return p4_symbolic::symbolic::Dataplane{program, table_entries};
}

}  // namespace p4_symbolic
