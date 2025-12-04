// Copyright 2025 Google LLC
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

#ifndef PINS_P4_INFRA_P4_PDPI_BUILT_INS_H_
#define PINS_P4_INFRA_P4_PDPI_BUILT_INS_H_

#include <string>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "p4_infra/p4_pdpi/ir.pb.h"

namespace pdpi {

// Returns the PDPI name for the multicast group table.
std::string GetMulticastGroupTableName();

// Returns the PDPI name for the clone session table.
std::string GetCloneSessionTableName();

// Returns the PDPI name for the replica action.
std::string GetReplicaActionName();

// Returns true if `table_name` is a known built_in table.
// Useful for branching on table type.
bool IsBuiltInTable(absl::string_view table_name);

// Returns true if `action_name` is a known built_in table.
// Useful for branching on action type.
bool IsBuiltInAction(absl::string_view action_name);

// Returns true if built-in `table` has built-in `field`.
bool BuiltInTableHasMatchField(IrBuiltInTable table, IrBuiltInMatchField field);

// Returns true if built-in `table` has built-in `action`.
bool BuiltInTableHasAction(IrBuiltInTable table, IrBuiltInAction action);

// Returns true if built-in `action` has built-in `parameter`.
bool BuiltInActionHasParameter(IrBuiltInAction action,
                               IrBuiltInParameter parameter);

// Returns enum `IrBuiltInAction` that built-in `parameter` belongs to.
// Returns InvalidArgumentError if built-in `parameter` holds invalid/unknown
// enum.
absl::StatusOr<IrBuiltInAction> GetBuiltInActionFromBuiltInParameter(
    IrBuiltInParameter parameter);

// Returns string representation of built-in `table`.
// Returns InvalidArgumentError if built-in `table` holds invalid/unknown enum.
absl::StatusOr<std::string> IrBuiltInTableToString(IrBuiltInTable table);

// Returns string representation of built-in `field`.
// Returns InvalidArgumentError if built-in `field` holds invalid/unknown enum.
absl::StatusOr<std::string> IrBuiltInMatchFieldToString(
    IrBuiltInMatchField field);

// Returns string representation of built-in `action`.
// Returns InvalidArgumentError if built-in `action` holds invalid/unknown enum.
absl::StatusOr<std::string> IrBuiltInActionToString(IrBuiltInAction action);

// Returns string representation of built-in `parameter`.
// Returns InvalidArgumentError if built-in `parameter` holds invalid/unknown
// enum.
absl::StatusOr<std::string> IrBuiltInParameterToString(
    IrBuiltInParameter parameter);

// Returns enum `IrBuiltInTable` whose string representation is `table_name`.
// Returns InvalidArgumentError if no `IrBuiltInTable` has string representation
// `table_name` (i.e. if `IsBuiltInTable(table_name)` is false).
absl::StatusOr<IrBuiltInTable> StringToIrBuiltInTable(
    absl::string_view table_name);

// Returns enum `IrBuiltInMatchField` whose string representation is
// `field_name`. Returns InvalidArgumentError if no IrBuiltInMatchField has
// string representation `field_name`.
absl::StatusOr<IrBuiltInMatchField> StringToIrBuiltInMatchField(
    absl::string_view field_name);

// Returns enum `IrBuiltInAction` whose string representation is `action_name`.
// Returns InvalidArgumentError if no IrBuiltInAction has string representation
// `action_name`.
absl::StatusOr<IrBuiltInAction> StringToIrBuiltInAction(
    absl::string_view action_name);

// Returns enum `IrBuiltInParameter` whose string representation is
// `parameter_name`. Returns InvalidArgumentError if no IrBuiltInParameter has
// string representation `parameter_name`.
absl::StatusOr<IrBuiltInParameter> StringToIrBuiltInParameter(
    absl::string_view parameter_name);

}  // namespace pdpi

#endif  // PINS_P4_INFRA_P4_PDPI_BUILT_INS_H_
