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
// =============================================================================
// This file contains functions for translating between proto enum and string
// representation for `pdpi::IrBuiltTable` and `pdpi::IrBuiltInField` (defined
// in ir.proto). It also contains functions for checking the validity of
// built-in table and field pairings.

#ifndef PINS_P4_PDPI_UTILS_BUILT_INS_H_
#define PINS_P4_PDPI_UTILS_BUILT_INS_H_

#include <string>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "p4_pdpi/ir.pb.h"

namespace pdpi {

// Returns true if `table_name` is a known built_in table.
// Useful for branching on table type.
bool IsBuiltInTable(absl::string_view table_name);

// Returns true if built-in `table` has built-in `field`.
bool BuiltInTableHasField(IrBuiltInTable table, IrBuiltInField field);

// Returns string representation of built-in `table`.
// Returns InvalidArgumentError if built-in `table` holds invalid/unknown enum.
absl::StatusOr<std::string> IrBuiltInTableToString(IrBuiltInTable table);

// Returns enum `IrBuiltInTable` whose string representation is `table_name`.
// Returns InvalidArgumentError if no `IrBuiltInTable` has string representation
// `table_name` (i.e. if `IsBuiltInTable(table_name)` is false).
absl::StatusOr<IrBuiltInTable> StringToIrBuiltInTable(
    absl::string_view table_name);

// Returns string representation of built-in `field`.
// Returns InvalidArgumentError if built-in `field` holds invalid/unknown enum.
absl::StatusOr<std::string> IrBuiltInFieldToString(IrBuiltInField field);

// Returns enum `IrBuiltInField` whose string representation is `field_name`.
// Returns InvalidArgumentError if no IrBuiltInField has string representation
// `field_name`.
absl::StatusOr<IrBuiltInField> StringToIrBuiltInField(
    absl::string_view field_name);

}  // namespace pdpi

#endif  // PINS_P4_PDPI_UTILS_BUILT_INS_H_
