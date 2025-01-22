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

#include "p4_symbolic/symbolic/symbolic.h"

#include <cstddef>
#include <iostream>
#include <memory>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

#include "absl/cleanup/cleanup.h"
#include "absl/container/btree_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/types/optional.h"
#include "glog/logging.h"
#include "gutil/status.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/internal/ordered_map.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_symbolic/ir/ir.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/ir/parser.h"
#include "p4_symbolic/ir/table_entries.h"
#include "p4_symbolic/symbolic/context.h"
#include "p4_symbolic/symbolic/table_entry.h"
#include "p4_symbolic/symbolic/util.h"
#include "p4_symbolic/symbolic/v1model.h"
#include "p4_symbolic/symbolic/values.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {

namespace {

// Returns a pointer to the P4-Symbolic IR table with the given `table_name`
// from the `program` IR. The returned pointer would not be null when the status
// is ok.
absl::StatusOr<const ir::Table *> GetIrTable(const ir::P4Program &program,
                                             absl::string_view table_name) {
  auto it = program.tables().find(table_name);
  if (it == program.tables().end()) {
    return gutil::NotFoundErrorBuilder()
           << "Table '" << table_name << "' not found";
  }
  return &it->second;
}

// Initializes the table entry objects in the symbolic context based on the
// given `ir_entries`. For symbolic table entries, symbolic variables and their
// corresponding constraints will be created within the given solver context.
absl::Status InitializeTableEntries(SolverState &state,
                                    ir::TableEntries ir_entries) {
  // Create table entry objects for both concrete and symbolic entries.
  for (auto &[table_name, per_table_ir_entries] : ir_entries) {
    // Check that the table entries do not exist for the table.
    if (auto it = state.context.table_entries.find(table_name);
        it != state.context.table_entries.end() && !it->second.empty()) {
      return gutil::InternalErrorBuilder()
             << "Expected no table entry for table '" << table_name
             << "'. Found: " << it->second.size() << " entries.";
    }

    // For each IR entry, create a table entry object.
    for (size_t index = 0; index < per_table_ir_entries.size(); ++index) {
      ir::TableEntry &ir_entry = per_table_ir_entries[index];
      TableEntry entry(index, std::move(ir_entry));
      if (!entry.IsConcrete() && !entry.IsSymbolic()) {
        return gutil::InvalidArgumentErrorBuilder()
               << "A table entry must be either concrete or symbolic. Found: "
               << entry.GetPdpiIrTableEntry().DebugString();
      }
      state.context.table_entries[table_name].push_back(std::move(entry));
    }
  }

  // For each symbolic table entry object in each table, create respective
  // symbolic variables and add corresponding constraints as Z3 assertions.
  for (auto &[table_name, table_entries] : state.context.table_entries) {
    ASSIGN_OR_RETURN(const ir::Table *table,
                     GetIrTable(state.program, table_name));

    for (TableEntry &entry : table_entries) {
      // Skip concrete table entries.
      if (entry.IsConcrete()) continue;

      // Initialize the symbolic match fields of the current entry.
      RETURN_IF_ERROR(InitializeSymbolicMatches(
          entry, *table, state.program, *state.context.z3_context,
          *state.solver, state.translator));

      // Entries with symbolic action sets are not supported for now.
      if (table->table_definition().has_action_profile_id()) {
        return gutil::UnimplementedErrorBuilder()
               << "Table entries with symbolic action sets are not supported "
                  "at the moment.";
      }

      // Initialize the symbolic actions of the current entry.
      RETURN_IF_ERROR(InitializeSymbolicActions(
          entry, *table, state.program, *state.context.z3_context,
          *state.solver, state.translator));
    }
  }

  // For each symbolic table entry object in each table, create respective
  // symbolic variables and add corresponding constraints as Z3 assertions.
  for (auto &[table_name, table_entries] : state.context.table_entries) {
    ASSIGN_OR_RETURN(const ir::Table *table,
                     GetIrTable(state.program, table_name));

    for (TableEntry &entry : table_entries) {
      // Skip concrete table entries.
      if (entry.IsConcrete()) continue;

      // Initialize the symbolic match fields of the current entry.
      RETURN_IF_ERROR(InitializeSymbolicMatches(
          entry, *table, state.program, *state.context.z3_context,
          *state.solver, state.translator));

      // Entries with symbolic action sets are not supported for now.
      if (table->table_definition().has_action_profile_id()) {
        return gutil::UnimplementedErrorBuilder()
               << "Table entries with symbolic action sets are not supported "
                  "at the moment.";
      }

      // Initialize the symbolic actions of the current entry.
      RETURN_IF_ERROR(InitializeSymbolicActions(
          entry, *table, state.program, *state.context.z3_context,
          *state.solver, state.translator));
    }
  }

  return absl::OkStatus();
}

}  // namespace

std::string SolverState::GetSolverSMT() {
  if (!solver) return "";
  return solver->to_smt2();
}

std::string SolverState::GetHeadersAndSolverConstraintsSMT() {
  std::ostringstream result;
  for (const auto &[field_name, expression] : context.ingress_headers) {
    result << "(ingress) " << field_name << ": " << expression << std::endl;
  }
  result << std::endl;
  for (const auto &[field_name, expression] : context.parsed_headers) {
    result << "(parsed) " << field_name << ": " << expression << std::endl;
  }
  result << std::endl;
  for (const auto &[field_name, expression] : context.egress_headers) {
    result << "(egress) " << field_name << ": " << expression << std::endl;
  }
  result << std::endl << "(solver constraints)" << std::endl << GetSolverSMT();
  return result.str();
}

absl::StatusOr<std::unique_ptr<SolverState>> EvaluateP4Program(
    const ir::P4Program &program, const ir::TableEntries &entries,
    const std::vector<int> &physical_ports,
    const TranslationPerType &translation_per_type) {
  // Initialize the solver state.
  auto state = std::make_unique<SolverState>(program);
  SymbolicContext &context = state->context;

  // Initialize the table entries.
  RETURN_IF_ERROR(InitializeTableEntries(*state, entries));

  // Initialize the p4runtime translator with statically translated types.
  for (const auto &[type, translation] : translation_per_type) {
    state->translator.p4runtime_translation_allocators.emplace(
        type, values::IdAllocator(translation));
  }

  // Evaluate the main program, assuming it conforms to V1 model.
  RETURN_IF_ERROR(v1model::EvaluateV1model(*state, physical_ports));

  // Restrict the value of all fields with (purely static, i.e.
  // dynamic_translation = false) P4RT translated types to what has been used in
  // TranslationPerType. This should be done after the symbolic execution since
  // P4Symbolic does not initially know which fields have translated types.
  for (const auto &[field, type] :
       Ordered(state->translator.fields_p4runtime_type)) {
    if (auto it = translation_per_type.find(type);
        it != translation_per_type.end() && !it->second.dynamic_translation) {
      ASSIGN_OR_RETURN(z3::expr field_expr, context.ingress_headers.Get(field));
      z3::expr constraint = context.z3_context->bool_val(false);
      for (const auto &[string_value, numeric_value] :
           it->second.static_mapping) {
        constraint =
            constraint || (field_expr == static_cast<int>(numeric_value));
      }
      state->solver->add(constraint);
    }
  }

  // Restrict ports to the available physical ports.
  // TODO: Support generating packet-out packets from the CPU port.
  if (physical_ports.empty()) {
    state->solver->add(context.ingress_port != kCpuPort);
    state->solver->add(context.ingress_port != kDropPort);
  } else {
    z3::expr ingress_port_is_physical = context.z3_context->bool_val(false);
    z3::expr egress_port_is_physical = context.z3_context->bool_val(false);
    for (int port : physical_ports) {
      ingress_port_is_physical =
          ingress_port_is_physical || context.ingress_port == port;
      egress_port_is_physical =
          egress_port_is_physical || context.egress_port == port;
    }
    state->solver->add(ingress_port_is_physical);
    // TODO: Lift this constraint, it should not be necessary and
    // prevents generation of packet-ins.
    state->solver->add(context.trace.dropped || egress_port_is_physical);
  }

  // Assemble and return result.
  return state;
}

absl::StatusOr<std::unique_ptr<SolverState>> EvaluateP4Program(
    const p4::v1::ForwardingPipelineConfig &config,
    const std::vector<p4::v1::TableEntry> &entries,
    const std::vector<int> &physical_ports,
    const TranslationPerType &translation_per_type) {
  // Parse the P4 config and concrete PI entries into the P4-symbolic IR.
  ASSIGN_OR_RETURN(ir::Dataplane dataplane, ir::ParseToIr(config, entries));
  return EvaluateP4Program(dataplane.program, dataplane.entries, physical_ports,
                           translation_per_type);
}

absl::StatusOr<std::optional<ConcreteContext>> Solve(SolverState &state) {
  z3::check_result check_result = state.solver->check();
  switch (check_result) {
    case z3::unsat:
    case z3::unknown:
      return absl::nullopt;

    case z3::sat:
      z3::model packet_model = state.solver->get_model();
      ASSIGN_OR_RETURN(ConcreteContext result,
                       util::ExtractFromModel(state.context, packet_model,
                                              state.translator));
      return result;
  }
  LOG(DFATAL) << "invalid Z3 check() result: "
              << static_cast<int>(check_result);
  return absl::nullopt;
}

absl::StatusOr<std::optional<ConcreteContext>> Solve(
    SolverState &state, const Assertion &assertion) {
  ASSIGN_OR_RETURN(z3::expr constraint, assertion(state.context));
  state.solver->push();
  state.solver->add(constraint);
  auto pop = absl::Cleanup([&] { state.solver->pop(); });
  return Solve(state);
}

std::string DebugSMT(const std::unique_ptr<SolverState> &state,
                     const Assertion &assertion) {
  absl::StatusOr<z3::expr> constraint = assertion(state->context);
  if (!constraint.ok()) {
    return "Failed to evaluate the given assertion. " +
           constraint.status().ToString();
  }

  state->solver->push();
  state->solver->add(*constraint);
  std::string smt = state->GetSolverSMT();
  state->solver->pop();
  return smt;
}

}  // namespace symbolic
}  // namespace p4_symbolic
