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

#ifndef PINS_SAI_P4_INSTANTIATIONS_GOOGLE_TEST_TOOLS_TABLE_ENTRY_GENERATOR_H_
#define PINS_SAI_P4_INSTANTIATIONS_GOOGLE_TEST_TOOLS_TABLE_ENTRY_GENERATOR_H_

// This file implements simple TableEntryGenerators for each table defined in
// each instantiation P4Info.

#include "absl/status/statusor.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "sai_p4/instantiations/google/test_tools/table_entry_generator_helper.h"

namespace sai {
// Returns a table entry generator for the given table.
// Returns Unimplemented error if the table is known and not supported.
// Returns an Unknown error if the table is unknown.
absl::StatusOr<TableEntryGenerator>
GetGenerator(const pdpi::IrTableDefinition &table);

} // namespace sai
  
#endif // PINS_SAI_P4_INSTANTIATIONS_GOOGLE_TEST_TOOLS_TABLE_ENTRY_GENERATOR_H_
