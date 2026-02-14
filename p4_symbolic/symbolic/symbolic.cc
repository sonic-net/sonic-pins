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
#include <optional>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

#include "absl/cleanup/cleanup.h"
#include "absl/container/btree_map.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/types/optional.h"
#include "gutil/gutil/status.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/built_ins.h"
#include "p4_infra/p4_pdpi/internal/ordered_map.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_symbolic/ir/ir.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/ir/parser.h"
#include "p4_symbolic/ir/table_entries.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesizer.pb.h"
#include "p4_symbolic/symbolic/context.h"
#include "p4_symbolic/symbolic/solver_state.h"
#include "p4_symbolic/symbolic/symbolic_table_entry.h"
#include "p4_symbolic/symbolic/util.h"
#include "p4_symbolic/symbolic/v1model.h"
#include "p4_symbolic/symbolic/values.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {

namespace {

// Initializes the table entry objects in the symbolic context based on the
// given `ir_entries`. For symbolic table entries, symbolic variables and their
// corresponding constraints will be created within the given solver context.
absl::Status InitializeTableEntries(SolverState &state,
                                    ir::TableEntries ir_entries) {
  // For each symbolic table entry object in each table, create respective
  // symbolic variables and add corresponding constraints as Z3 assertions.
  for (auto &[table_name, table_entries] : ir_entries) {
    // We don't support symbolic entries in built-in tables at this time.
    if (pdpi::IsBuiltInTable(table_name)) continue;
    ASSIGN_OR_RETURN(const ir::Table *table,
                     util::GetIrTable(state.program, table_name));
    for (ir::TableEntry &entry : table_entries) {
      switch (entry.entry_case()) {
        case ir::TableEntry::kConcreteEntry:
          continue;
        case ir::TableEntry::kSymbolicEntry: {
          if (table->table_definition().has_action_profile_id()) {
            return gutil::UnimplementedErrorBuilder()
                   << "Table entries with symbolic action sets are not "
                      "supported at the moment.";
          }
          ir::SymbolicTableEntry &symbolic_entry =
              *entry.mutable_symbolic_entry();
          RETURN_IF_ERROR(InitializeSymbolicMatches(
              symbolic_entry, *table, state.program, *state.context.z3_context,
              *state.solver, state.translator));
          RETURN_IF_ERROR(InitializeSymbolicActions(
              symbolic_entry, *table, state.program, *state.context.z3_context,
              *state.solver, state.translator));
          continue;
        }
        case ir::TableEntry::ENTRY_NOT_SET:
          break;
      }
      return gutil::InvalidArgumentErrorBuilder()
             << "Unsupported table entry: " << absl::StrCat(entry);
    }
  }

  state.context.table_entries = std::move(ir_entries);
  return absl::OkStatus();
}

// Adds solver constraint to restrict the statically translated given `value`
// of the given type `type_name` based on the valid values in the given
// `translator`.
void AddConstraintForStaticallyTranslatedValue(
    const z3::expr &value, const std::string &type_name,
    const values::P4RuntimeTranslator &translator, z3::context &z3_context,
    z3::solver &solver) {
  auto it = translator.p4runtime_translation_allocators.find(type_name);
  if (it == translator.p4runtime_translation_allocators.end() ||
      it->second.IsDynamicAllocationEnabled())
    return;

  z3::expr constraint = z3_context.bool_val(false);
  for (const auto &valid_value : it->second.GetAllocatedIds()) {
    constraint = constraint || (value == static_cast<int>(valid_value));
  }
  solver.add(constraint);
}

}  // namespace

// Adds solver constraints to restrict the statically translated values (e.g.,
// values of the type `port_id_t` in SAI-P4) to only the mapped values in the
// translator.
// The optional headers argument is used in case of DFS-style
// symbolic execution for path coverage (go/p4-path-coverage).
absl::Status AddConstraintsForStaticallyTranslatedValues(
    SolverState &state, std::optional<SymbolicPerPacketState> headers) {
  // Restrict the value of all header fields with (purely static, i.e.
  // dynamic_translation = false) P4Runtime translated types to what has been
  // used in the translator.
  for (const auto &[field, type] :
       Ordered(state.translator.fields_p4runtime_type)) {
    ASSIGN_OR_RETURN(z3::expr value,
                     headers.has_value()
                         ? headers.value().Get(field)
                         : state.context.ingress_headers.Get(field));
    AddConstraintForStaticallyTranslatedValue(value, type, state.translator,
                                              *state.context.z3_context,
                                              *state.solver);
  }
  // Restrict the symbolic variable value of all symbolic table entries with
  // (purely static) P4Runtime translated types to what has been used in the
  // translator.
  for (const auto &[table_name, entries_per_table] :
       state.context.table_entries) {
    // We don't support symbolic entries in built-in tables at this time.
    if (pdpi::IsBuiltInTable(table_name)) continue;
    ASSIGN_OR_RETURN(const ir::Table *table,
                     util::GetIrTable(state.program, table_name));
    for (const ir::TableEntry &entry : entries_per_table) {
      if (!entry.has_symbolic_entry()) continue;
      const ir::SymbolicTableEntry &symbolic_entry = entry.symbolic_entry();

      // Constrain the symbolic variables for entry matches.
      for (const pdpi::IrMatch &symbolic_match :
           symbolic_entry.sketch().matches()) {
        const std::string &match_name = symbolic_match.name();
        ASSIGN_OR_RETURN(pdpi::IrMatchFieldDefinition match_definition,
                         util::GetMatchDefinition(match_name, *table));
        std::string type_name =
            match_definition.match_field().type_name().name();
        if (type_name.empty()) {
          // If the match definition does not specify the type name, use the
          // matched header field name to get the type name based on the
          // translator mapping. This seems to happen for matches on locally
          // defined variables.
          ASSIGN_OR_RETURN(std::string field_name,
                           util::GetFieldNameFromMatch(match_name, *table));
          auto it = state.translator.fields_p4runtime_type.find(field_name);
          if (it != state.translator.fields_p4runtime_type.end())
            type_name = it->second;
        }
        ASSIGN_OR_RETURN(
            SymbolicMatch match_variables,
            GetSymbolicMatch(symbolic_entry, match_name, *table, state.program,
                             *state.context.z3_context));
        AddConstraintForStaticallyTranslatedValue(
            match_variables.value, type_name, state.translator,
            *state.context.z3_context, *state.solver);
      }

      // Constrain the symbolic variables for action parameters.
      for (const auto &action_ref : table->table_definition().entry_actions()) {
        const std::string &action_name = action_ref.action().preamble().name();

        // Check and get the action in P4-Symbolic IR.
        auto it = state.program.actions().find(action_name);
        if (it == state.program.actions().end()) {
          return gutil::NotFoundErrorBuilder()
                 << "Action '" << action_name << "' not found.";
        }
        const ir::Action &action = it->second;

        for (const auto &[param_name, param_definition] :
             Ordered(action.action_definition().params_by_name())) {
          const std::string &type_name =
              param_definition.param().type_name().name();
          ASSIGN_OR_RETURN(
              z3::expr param,

              GetSymbolicActionParameter(symbolic_entry, param_name, action,
                                         *table, *state.context.z3_context));
          AddConstraintForStaticallyTranslatedValue(
              param, type_name, state.translator, *state.context.z3_context,
              *state.solver);
        }
      }
    }
  }

  return absl::OkStatus();
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

  // Restrict the symbolic variables of statically translated types to only the
  // translated values. This should be done after the symbolic execution since
  // P4-Symbolic does not initially know which header fields have translated
  // types.
  RETURN_IF_ERROR(AddConstraintsForStaticallyTranslatedValues(*state));

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

absl::StatusOr<packet_synthesizer::PacketSynthesisResults>
EvaluateP4ProgramAndSynthesizePacketsCoveringAllControlFlowPaths(
    const p4::v1::ForwardingPipelineConfig &config,
    const std::vector<p4::v1::Entity> &entities,
    const std::vector<int> &physical_ports,
    const TranslationPerType &translation_per_type) {
  ASSIGN_OR_RETURN(ir::Dataplane dataplane, ir::ParseToIr(config, entities));
  ir::P4Program program = dataplane.program;
  ir::TableEntries entries = dataplane.entries;

  // Initialize the solver state.
  auto state = std::make_unique<SolverState>(program);
  // SymbolicContext &context = state->context;

  LOG(INFO) << "Initialize table entries";
  // Initialize the table entries.
  RETURN_IF_ERROR(InitializeTableEntries(*state, entries));

  LOG(INFO) << "Initialize p4runtime translator";
  // Initialize the p4runtime translator with statically translated types.
  for (const auto &[type, translation] : translation_per_type) {
    state->translator.p4runtime_translation_allocators.emplace(
        type, values::IdAllocator(translation));
  }

  LOG(INFO) << "Evaluate V1 model";
  // Evaluate the main program, assuming it conforms to V1 model.
  ASSIGN_OR_RETURN(
      auto packet_synthesis_results,
      v1model::EvaluateV1modelAndSynthesizePacketsCoveringAllControlFlowPaths(
          *state, physical_ports));

  // Assemble and return result.
  return packet_synthesis_results;
}

absl::StatusOr<std::unique_ptr<SolverState>> EvaluateP4Program(
    const p4::v1::ForwardingPipelineConfig &config,
    const std::vector<p4::v1::Entity> &entities,
    const std::vector<int> &physical_ports,
    const TranslationPerType &translation_per_type) {
  // Parse the P4 config and concrete PI entries into the P4-symbolic IR.
  ASSIGN_OR_RETURN(ir::Dataplane dataplane, ir::ParseToIr(config, entities));
  return EvaluateP4Program(dataplane.program, dataplane.entries, physical_ports,
                           translation_per_type);
}

absl::StatusOr<std::optional<ConcreteContext>> Solve(SolverState &state) {
  z3::check_result check_result = state.solver->check();
  switch (check_result) {
    case z3::unsat:
    case z3::unknown: {
      return absl::nullopt;
    }

    case z3::sat: {
      z3::model model = state.solver->get_model();
      ASSIGN_OR_RETURN(ConcreteContext result,
                       util::ExtractFromModel(model, state));
      return result;
    }

    default: {
      return gutil::InternalErrorBuilder()
             << "Invalid Z3 check() result: " << check_result;
    }
  }
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
