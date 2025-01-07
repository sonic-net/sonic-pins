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

#include <memory>
#include <utility>

#include "absl/cleanup/cleanup.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/types/optional.h"
#include "glog/logging.h"
#include "gutil/status.h"
#include "p4_pdpi/internal/ordered_map.h"
#include "p4_symbolic/ir/parser.h"
#include "p4_symbolic/symbolic/util.h"
#include "p4_symbolic/symbolic/v1model.h"
#include "p4_symbolic/symbolic/values.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {

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

absl::StatusOr<std::unique_ptr<symbolic::SolverState>> EvaluateP4Program(
    const p4::v1::ForwardingPipelineConfig &config,
    const std::vector<p4::v1::TableEntry> &entries,
    const std::vector<int> &physical_ports,
    const TranslationPerType &translation_per_type) {
  // Parse the P4 config and entries into the P4-symbolic IR.
  ASSIGN_OR_RETURN(ir::Dataplane dataplane, ir::ParseToIr(config, entries));

  auto solver_state =
      std::make_unique<SolverState>(dataplane.program, dataplane.entries);
  SymbolicContext &context = solver_state->context;
  values::P4RuntimeTranslator &translator = solver_state->translator;

  // Initialize the p4runtime translator with statically translated types.
  for (const auto &[type, translation] : translation_per_type) {
    translator.p4runtime_translation_allocators.emplace(
        type, values::IdAllocator(translation));
  }

  // Evaluate the main program, assuming it conforms to V1 model.
  RETURN_IF_ERROR(
      v1model::EvaluateV1model(dataplane, physical_ports, context, translator));

  // Restrict the value of all fields with (purely static, i.e.
  // dynamic_translation = false) P4RT translated types to what has been used in
  // TranslationPerType. This should be done after the symbolic execution since
  // P4Symbolic does not initially know which fields have translated types.
  for (const auto &[field, type] : Ordered(translator.fields_p4runtime_type)) {
    if (auto it = translation_per_type.find(type);
        it != translation_per_type.end() && !it->second.dynamic_translation) {
      ASSIGN_OR_RETURN(z3::expr field_expr, context.ingress_headers.Get(field));
      z3::expr constraint = context.z3_context->bool_val(false);
      for (const auto &[string_value, numeric_value] :
           it->second.static_mapping) {
        constraint =
            constraint || (field_expr == static_cast<int>(numeric_value));
      }
      solver_state->solver->add(constraint);
    }
  }

  // Restrict ports to the available physical ports.
  // TODO: Support generating packet-out packets from the CPU port.
  if (physical_ports.empty()) {
    solver_state->solver->add(context.ingress_port != kCpuPort);
    solver_state->solver->add(context.ingress_port != kDropPort);
  } else {
    z3::expr ingress_port_is_physical = context.z3_context->bool_val(false);
    z3::expr egress_port_is_physical = context.z3_context->bool_val(false);
    for (int port : physical_ports) {
      ingress_port_is_physical =
          ingress_port_is_physical || context.ingress_port == port;
      egress_port_is_physical =
          egress_port_is_physical || context.egress_port == port;
    }
    solver_state->solver->add(ingress_port_is_physical);
    // TODO: Lift this constraint, it should not be necessary and
    // prevents generation of packet-ins.
    solver_state->solver->add(context.trace.dropped || egress_port_is_physical);
  }

  // Assemble and return result.
  return solver_state;
}

absl::StatusOr<std::optional<ConcreteContext>> Solve(
    SolverState &solver_state) {
  z3::check_result check_result = solver_state.solver->check();
  switch (check_result) {
    case z3::unsat:
    case z3::unknown:
      return absl::nullopt;

    case z3::sat:
      z3::model packet_model = solver_state.solver->get_model();
      ASSIGN_OR_RETURN(
          ConcreteContext result,
          util::ExtractFromModel(solver_state.context, packet_model,
                                 solver_state.translator));
      return result;
  }
  LOG(DFATAL) << "invalid Z3 check() result: "
              << static_cast<int>(check_result);
  return absl::nullopt;
}

absl::StatusOr<std::optional<ConcreteContext>> Solve(
    SolverState &solver_state, const Assertion &assertion) {
  ASSIGN_OR_RETURN(z3::expr constraint, assertion(solver_state.context));
  solver_state.solver->push();
  solver_state.solver->add(constraint);
  auto pop = absl::Cleanup([&] { solver_state.solver->pop(); });
  return Solve(solver_state);
}

absl::StatusOr<std::optional<ConcreteContext>> Solve(
    const std::unique_ptr<SolverState> &solver_state,
    const Assertion &assertion) {
  return Solve(*solver_state, assertion);
}

std::string DebugSMT(const std::unique_ptr<SolverState> &solver_state,
                     const Assertion &assertion) {
  absl::StatusOr<z3::expr> constraint = assertion(solver_state->context);
  if (!constraint.ok()) {
    return "Failed to evaluate the given assertion. " +
           constraint.status().ToString();
  }

  solver_state->solver->push();
  solver_state->solver->add(*constraint);
  std::string smt = solver_state->GetSolverSMT();
  solver_state->solver->pop();
  return smt;
}

}  // namespace symbolic
}  // namespace p4_symbolic
