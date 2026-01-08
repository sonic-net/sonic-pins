/*
 * Copyright 2020 Google LLC
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#ifndef PINS_P4RT_APP_UTILS_TABLE_UTILITY_H_
#define PINS_P4RT_APP_UTILS_TABLE_UTILITY_H_

#include <string>
#include <vector>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "google/protobuf/map.h"
#include "p4_pdpi/ir.pb.h"

namespace p4rt_app {
namespace table {

// Individual table types that may require different processing.
enum class Type {
  kAcl,               // ACL pipeline table
  kFixed,             // Fixed pipeline table
  kExt,               // Extended pipeline table
  kAclDefinition,     // Pipeline table definitions table (Required for ACLs)
  kTblsDefinitionSet, // tables definition set table
};

// Returns a string representation of the table type.
std::string TypeName(Type type);

// If a valid Type name is provided, returns the corresponding type.
// Otherwise, returns an error.
absl::StatusOr<Type> TypeParse(absl::string_view type_name);

} // namespace table

// Returns the table type of the provided table.
absl::StatusOr<table::Type>
GetTableType(const pdpi::IrTableDefinition &ir_table);

// Looks at the bitwidth for all match fields in a table and returns an ordered
// list of table definitions in decreasing order.
std::vector<const pdpi::IrTableDefinition*> OrderTablesBySize(
    const google::protobuf::Map<std::string, pdpi::IrTableDefinition>&
        tables_by_name);

void OrderTablesBySize(std::vector<const pdpi::IrTableDefinition*>& tables);

absl::StatusOr<std::string> DuplicateTable(pdpi::IrP4Info& ir_p4info,
                                           absl::string_view table_name);

}  // namespace p4rt_app

#endif // PINS_P4RT_APP_UTILS_TABLE_UTILITY_H_
