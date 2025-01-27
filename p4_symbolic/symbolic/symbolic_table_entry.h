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

#include <cstddef>
#include <optional>
#include <string>
#include <vector>

#include "absl/container/btree_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/symbolic/values.h"
#include "z3++.h"

namespace p4_symbolic::symbolic {

// Contains the symbolic variables of a symbolic match of a table entry.
struct SymbolicMatch {
  p4::config::v1::MatchField::MatchType match_type;
  z3::expr value;
  z3::expr mask;
};

// Returns the symbolic variable of the action parameter with the given
// `param_name` in the `action`. Returns an error if this is not a symbolic
// entry.
absl::StatusOr<z3::expr> GetSymbolicActionParameter(
    const ir::SymbolicTableEntry &symbolic_entry, absl::string_view param_name,
    const ir::Action &action, const ir::Table &table, z3::context &z3_context);

// Returns the symbolic variable of the action invocation with the given
// `action_name`. Returns an error if this is not a symbolic entry.
absl::StatusOr<z3::expr> GetSymbolicActionInvocation(
    const ir::SymbolicTableEntry &symbolic_entry, absl::string_view action_name,
    const ir::Table &table, z3::context &z3_context);

// Returns the symbolic variables of the symbolic match with the given
// `match_name`. Returns an error if this is not a symbolic entry.
absl::StatusOr<SymbolicMatch> GetSymbolicMatch(
    const ir::SymbolicTableEntry &symbolic_entry, absl::string_view match_name,
    const ir::Table &table, const ir::P4Program &program,
    z3::context &z3_context);

// Creates symbolic variables and adds constraints for each field match of the
// given `entry` in the given `table`. We don't create symbolic variables for
// omitted matches as the omitted matches are treated as explicit wildcards
// based on the P4Runtime specification. If those symbolic variables are needed
// later, calling the `GetMatchValues` function will automatically create the
// corresponding variables for the entry match.
absl::Status InitializeSymbolicMatches(
    const ir::SymbolicTableEntry &symbolic_entry, const ir::Table &table,
    const ir::P4Program &program, z3::context &z3_context, z3::solver &solver,
    values::P4RuntimeTranslator &translator);

// Creates symbolic variables and adds constraints for the given `entry`, for
// each action and each action parameter in the given `table`.
absl::Status InitializeSymbolicActions(
    const ir::SymbolicTableEntry &symbolic_entry, const ir::Table &table,
    const ir::P4Program &program, z3::context &z3_context, z3::solver &solver,
    values::P4RuntimeTranslator &translator);

// Returns a concrete table entry extracted from the given `symbolic_entry`
// based on the given `model` and `translator`.
absl::StatusOr<ir::ConcreteTableEntry> ExtractConcreteEntryFromModel(
    const ir::SymbolicTableEntry &symbolic_entry, const z3::model &model,
    const ir::P4Program &program, const values::P4RuntimeTranslator &translator,
    z3::context &z3_context);

}  // namespace p4_symbolic::symbolic

#endif  // PINS_P4_SYMBOLIC_SYMBOLIC_TABLE_ENTRY_H_
