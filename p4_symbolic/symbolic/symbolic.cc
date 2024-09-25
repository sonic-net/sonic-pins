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

#include <utility>

#include "p4_symbolic/symbolic/control.h"
#include "p4_symbolic/symbolic/operators.h"
#include "p4_symbolic/symbolic/packet.h"
#include "p4_symbolic/symbolic/parser.h"
#include "p4_symbolic/symbolic/util.h"

namespace p4_symbolic {
namespace symbolic {

z3::context &Z3Context() {
  static z3::context *z3_context = new z3::context();
  return *z3_context;
}

absl::StatusOr<std::unique_ptr<SolverState>> EvaluateP4Pipeline(
    const Dataplane &data_plane, const std::vector<int> &physical_ports,
    bool hardcoded_parser) {
  // Use global context to define a solver.
  std::unique_ptr<z3::solver> z3_solver =
      std::make_unique<z3::solver>(Z3Context());

  // Create free/unconstrainted headers variables, and then
  // put constraints on them matching the hardcoded behavior of the parser
  // for programs we are interested in.
  ASSIGN_OR_RETURN(SymbolicPerPacketState ingress_headers,
                   SymbolicGuardedMap::CreateSymbolicGuardedMap(
                       data_plane.program.headers()));
  if (hardcoded_parser) {
    ASSIGN_OR_RETURN(std::vector<z3::expr> parser_constraints,
                     parser::EvaluateHardcodedParser(ingress_headers));
    for (const z3::expr &constraint : parser_constraints) {
      z3_solver->add(constraint);
    }
  }

  // Initially, the p4runtime translator has empty state.
  values::P4RuntimeTranslator translator;

  // "Accumulator"-style p4 program headers.
  // This is used to evaluate the P4 program.
  // Initially free/unconstrained and contains symbolic variables for
  // every header field.
  SymbolicPerPacketState egress_headers(ingress_headers);

  ASSIGN_OR_RETURN(z3::expr ingress_port,
                   ingress_headers.Get("standard_metadata.ingress_port"));
  // TODO: Function hardcoded.
  SymbolicPacket ingress_packet =
      packet::ExtractSymbolicPacket(ingress_headers);

  // Evaluate the initial control, which will evaluate the next controls
  // internally and return the full symbolic trace.
  ASSIGN_OR_RETURN(
      SymbolicTrace trace,
      control::EvaluateControl(data_plane, data_plane.program.initial_control(),
                               &egress_headers, &translator,
                               Z3Context().bool_val(true)));

  // Alias the event that the packet is dropped for ease of use in assertions.
  z3::expr dropped_value =
      Z3Context().bv_val(DROPPED_EGRESS_SPEC_VALUE, DROPPED_EGRESS_SPEC_LENGTH);
  ASSIGN_OR_RETURN(trace.dropped,
                   egress_headers.Get("standard_metadata.egress_spec"));
  ASSIGN_OR_RETURN(trace.dropped, operators::Eq(trace.dropped, dropped_value));

  // Construct a symbolic context, containing state and trace information
  // from evaluating the tables.
  ASSIGN_OR_RETURN(z3::expr egress_port,
                   egress_headers.Get("standard_metadata.egress_spec"));

  // Restrict ports to the available physical ports.
  if (!physical_ports.empty()) {
    z3::expr ingress_port_domain = Z3Context().bool_val(false);
    z3::expr egress_port_domain = trace.dropped;
    unsigned int port_size = ingress_port.get_sort().bv_size();
    for (int port : physical_ports) {
      ASSIGN_OR_RETURN(
          z3::expr ingress_port_eq,
          operators::Eq(ingress_port, Z3Context().bv_val(port, port_size)));
      ASSIGN_OR_RETURN(
          z3::expr egress_port_eq,
          operators::Eq(egress_port, Z3Context().bv_val(port, port_size)));

      ASSIGN_OR_RETURN(ingress_port_domain,
                       operators::Or(ingress_port_domain, ingress_port_eq));
      ASSIGN_OR_RETURN(egress_port_domain,
                       operators::Or(egress_port_domain, egress_port_eq));
    }
    z3_solver->add(ingress_port_domain);
    z3_solver->add(egress_port_domain);
  }

  // Construct solver state for this program.
  SymbolicPacket egress_packet = packet::ExtractSymbolicPacket(egress_headers);
  SymbolicContext symbolic_context = {
      ingress_port,    egress_port,    ingress_packet, egress_packet,
      ingress_headers, egress_headers, trace};

  return std::make_unique<SolverState>(data_plane.program, data_plane.entries,
                                       symbolic_context, std::move(z3_solver),
                                       translator);
}

absl::StatusOr<std::optional<ConcreteContext>> Solve(
    const std::unique_ptr<SolverState> &solver_state,
    const Assertion &assertion) {
  z3::expr constraint = assertion(solver_state->context);

  solver_state->solver->push();
  solver_state->solver->add(constraint);
  switch (solver_state->solver->check()) {
    case z3::unsat:
      solver_state->solver->pop();
      return std::optional<ConcreteContext>();

    case z3::unknown:
      solver_state->solver->pop();
      return std::optional<ConcreteContext>();

    case z3::sat:
    default:
      z3::model packet_model = solver_state->solver->get_model();
      ASSIGN_OR_RETURN(
          ConcreteContext result,
          util::ExtractFromModel(solver_state->context, packet_model,
                                 solver_state->translator));
      solver_state->solver->pop();
      return std::make_optional<ConcreteContext>(result);
  }
}

std::string DebugSMT(const std::unique_ptr<SolverState> &solver_state,
                     const Assertion &assertion) {
  solver_state->solver->push();
  solver_state->solver->add(assertion(solver_state->context));
  std::string smt = solver_state->solver->to_smt2();
  solver_state->solver->pop();
  return smt;
}

}  // namespace symbolic
}  // namespace p4_symbolic
