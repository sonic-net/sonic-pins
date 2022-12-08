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

#ifndef GOOGLE_P4RT_APP_UTILS_TABLE_UTILITY_H_
#define GOOGLE_P4RT_APP_UTILS_TABLE_UTILITY_H_

#include <string>

#include "absl/strings/string_view.h"
#include "gutil/status.h"
#include "p4_pdpi/ir.pb.h"


namespace p4rt_app {
namespace table {

// Individual table types that may require different processing.
enum class Type {
  kAcl,        // ACL pipeline table
  kFixed,      // Fixed pipeline table
  kExt,        // Extended pipeline table
  kAclDefinition,  // Pipeline table definitions table (Required for ACLs)
  kTblsDefinitionSet,  // tables definition set table
};

// Returns a string representation of the table type.
std::string TypeName(Type type);

// If a valid Type name is provided, returns the corresponding type.
// Otherwise, returns an error.
absl::StatusOr<Type> TypeParse(absl::string_view type_name);

}  // namespace table

// Returns the table type of the provided table.
absl::StatusOr<table::Type> GetTableType(
    const pdpi::IrTableDefinition& ir_table);

}  // namespace p4rt_app

#endif  // GOOGLE_P4RT_APP_UTILS_TABLE_UTILITY_H_
