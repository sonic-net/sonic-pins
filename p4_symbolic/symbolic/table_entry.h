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

#ifndef PINS_P4_SYMBOLIC_SYMBOLIC_TABLE_ENTRY_H_
#define PINS_P4_SYMBOLIC_SYMBOLIC_TABLE_ENTRY_H_

#include <string>
#include <vector>

#include "absl/container/btree_map.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "z3++.h"

namespace p4_symbolic::symbolic {

// Contains the symbolic variables of a symbolic match of a table entry.
struct SymbolicMatchVariables {
  p4::config::v1::MatchField::MatchType match_type;
  z3::expr value;
  z3::expr mask;
};

// Contains the symbolic variable names and bit-width of the symbolic match of a
// table entry.
struct SymbolicMatchInfo {
  p4::config::v1::MatchField::MatchType match_type;
  int bitwidth;
  // Value variable name of the symbolic match. It looks like
  // "<table_name>_entry_<index>_<match_name>_<match_type>_value".
  std::string value_variable_name;
  // Value variable name of the symbolic match. It looks like
  // "<table_name>_entry_<index>_<match_name>_<match_type>_mask".
  std::string mask_variable_name;
};

// Contains the symbolic variable name and bit-width of the symbolic action
// parameter of a table entry.
struct SymbolicActionParameterInfo {
  // Variable name of the symbolic action parameter. It looks like
  // "<table_name>_entry_<index>_<action_name>_<param_name>".
  std::string variable_name;
  int bitwidth;
};

class TableEntry {
 public:
  // Constructs a table entry object, where the `index` is the original index of
  // the entry in the table and the `ir_entry` is the entry in P4-Symbolic IR.
  TableEntry(int index, ir::TableEntry ir_entry);

  // Returns the original index of the entry as installed in the table.
  int GetIndex() const;
  // Returns true if the IR entry has a concrete entry.
  bool IsConcrete() const;
  // Returns true if the IR entry has a symbolic entry.
  bool IsSymbolic() const;
  // Returns the table name of the table to which the entry belongs.
  const std::string &GetTableName() const;
  // Returns the P4-Symbolic IR table entry.
  const ir::TableEntry &GetP4SymbolicIrTableEntry() const;
  // Returns the PDPI IR table entry, which may represent a concrete entry or
  // the skeleton for a symbolic entry.
  // Note: If symbolic, the returned entry may not be a well-formed PDPI IR
  // entry. See p4_symbolic/ir/ir.proto for details.
  const pdpi::IrTableEntry &GetPdpiIrTableEntry() const;

  // Returns the symbolic variables of the symbolic match with the given
  // `match_name`. Returns an error if this is not a symbolic entry.
  absl::StatusOr<SymbolicMatchVariables> GetMatchValues(
      absl::string_view match_name, const ir::Table &table,
      const ir::P4Program &program, z3::context &z3_context) const;
  // Returns the symbolic variable of the action invocation with the given
  // `action_name`. Returns an error if this is not a symbolic entry.
  absl::StatusOr<z3::expr> GetActionInvocation(absl::string_view action_name,
                                               const ir::Table &table,
                                               z3::context &z3_context) const;
  // Returns the symbolic variable of the action parameter with the given
  // `param_name` in the `action`. Returns an error if this is not a symbolic
  // entry.
  absl::StatusOr<z3::expr> GetActionParameter(absl::string_view param_name,
                                              const ir::Action &action,
                                              const ir::Table &table,
                                              z3::context &z3_context) const;

 private:
  int index_;                // The original index of the entry in the table.
  ir::TableEntry ir_entry_;  // Entry in P4-Symbolic IR.

  // Returns the symbolic variable names, the bit-width, and the match type of
  // the symbolic match with the given `match_name`. An error is returned if
  // this is not a symbolic entry, or if the given `match_name` is not found in
  // the table definition.
  absl::StatusOr<SymbolicMatchInfo> GetSymbolicMatchInfo(
      absl::string_view match_name, const ir::Table &table,
      const ir::P4Program &program) const;
  // Returns the symbolic variable name of the action invocation with the given
  // `action_name`. An error is returned if this is not a symbolic entry, or if
  // the given `action_name` is not found in the table definition.
  absl::StatusOr<std::string> GetActionChoiceSymbolicVariableName(
      absl::string_view action_name, const ir::Table &table) const;
  // Returns the symbolic variable name and the bit-width of the action
  // parameter with the given `action_name` and `param_name`. An error is
  // returned if this is not a symbolic entry, or if the given `action_name` and
  // `param_name` are not found in the table and action definition.
  absl::StatusOr<SymbolicActionParameterInfo> GetSymbolicActionParameterInfo(
      absl::string_view param_name, const ir::Action &action,
      const ir::Table &table) const;
};

using TableEntries = absl::btree_map<std::string, std::vector<TableEntry>>;

}  // namespace p4_symbolic::symbolic

#endif  // PINS_P4_SYMBOLIC_SYMBOLIC_TABLE_ENTRY_H_
