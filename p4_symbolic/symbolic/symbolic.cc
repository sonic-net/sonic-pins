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
#include "absl/strings/substitute.h"
#include "absl/types/optional.h"
#include "glog/logging.h"
#include "gutil/status.h"
#include "p4_symbolic/symbolic/control.h"
#include "p4_symbolic/symbolic/operators.h"
#include "p4_symbolic/symbolic/util.h"
#include "p4_symbolic/symbolic/values.h"
#include "p4_symbolic/z3_util.h"

namespace p4_symbolic {
namespace symbolic {

std::string SolverState::GetSolverSMT() const {
  if (!solver) return "";
  return solver->to_smt2();
}

z3::expr EgressSpecDroppedValue() {
  return Z3Context().bv_val(kDropPort, kPortBitwidth);
}

absl::StatusOr<z3::expr> IsDropped(const SymbolicPerPacketState &state) {
  ASSIGN_OR_RETURN(z3::expr egress_spec,
                   state.Get("standard_metadata.egress_spec"));
  return operators::Eq(egress_spec, EgressSpecDroppedValue());
}

absl::StatusOr<z3::expr> GotCloned(const SymbolicPerPacketState &state) {
  return state.Get(std::string(kGotClonedPseudoField));
}

absl::Status CheckPhysicalPortsConformanceToV1Model(
    const std::vector<int> &physical_ports) {
  for (const int port : physical_ports) {
    if (port == kDropPort) {
      return gutil::InvalidArgumentErrorBuilder()
             << "cannot use physical port " << kDropPort
             << " as p4-symbolic reserves it to encode dropping a packet; see "
                "the documentation of `mark_to_drop` in v1mode1.p4 for details";
    }
    if (port < 0 || port >= 512) {
      return absl::InvalidArgumentError(absl::Substitute(
          "Cannot use the value $0 as a physical port as the value does not "
          "fit into PortId_t (bit<9>), the type of "
          "standard_metadata.{ingress/egress}_port in v1model.p4.",
          port));
    }
    if (port == kDropPort) {
      return absl::InvalidArgumentError(
          absl::Substitute("Cannot use the value $0 as a physical port as the "
                           "value is reserved for dropping packets.",
                           port));
    }
    if (port == kCpuPort) {
      return absl::InvalidArgumentError(
          absl::Substitute("Cannot use the value $0 as a physical port as the "
                           "value is reserved for the CPU port.",
                           port));
    }
  }

  return absl::OkStatus();
}

absl::StatusOr<std::unique_ptr<SolverState>> EvaluateP4Pipeline(
    const Dataplane &data_plane, const std::vector<int> &physical_ports,
    const TranslationPerType &translation_per_type) {
  // Check input physical ports.
  if (absl::Status status =
          CheckPhysicalPortsConformanceToV1Model(physical_ports);
      !status.ok()) {
    return status;
  }

  // Use global context to define a solver.
  std::unique_ptr<z3::solver> z3_solver =
      std::make_unique<z3::solver>(Z3Context());

  // Initially, the p4runtime translator has empty state.
  values::P4RuntimeTranslator translator;

  // Initiate the p4runtime translator with statically translated types.
  for (const auto &[type, translation] : translation_per_type) {
    translator.p4runtime_translation_allocators.emplace(
        type, values::IdAllocator(translation));
  }

  // "Accumulator"-style p4 program headers.
  // This is used to evaluate the P4 program.
  // Initially free/unconstrained and contains symbolic variables for
  // every header field.
  ASSIGN_OR_RETURN(SymbolicPerPacketState ingress_headers,
                   SymbolicGuardedMap::CreateSymbolicGuardedMap(
                       data_plane.program.headers()));
  SymbolicPerPacketState egress_headers = ingress_headers;

  // Evaluate the main program.
  ASSIGN_OR_RETURN(
      SymbolicTableMatches matched_entries,
      control::EvaluateV1model(data_plane, &egress_headers, &translator));

  // Restrict the value of all fields with (purely static, i.e.
  // dynamic_translation = false) P4RT translated types to what has been used in
  // TranslationPerType. This should be done after the symbolic execution
  // since P4Symbolic does not initially know which fields have translated
  // types.
  for (const auto &[field, type] : translator.fields_p4runtime_type) {
    if (auto it = translation_per_type.find(type);
        it != translation_per_type.end() && !it->second.dynamic_translation) {
      ASSIGN_OR_RETURN(z3::expr field_expr, ingress_headers.Get(field));
      z3::expr constraint = Z3Context().bool_val(false);
      for (const auto &[string_value, numeric_value] :
           it->second.static_mapping) {
        constraint =
            constraint || (field_expr == static_cast<int>(numeric_value));
      }
      z3_solver->add(constraint);
    }
  }

  // Alias the event that the packet is dropped for ease of use in assertions
  ASSIGN_OR_RETURN(z3::expr dropped, IsDropped(egress_headers));
  ASSIGN_OR_RETURN(z3::expr got_cloned, GotCloned(egress_headers));

  // Restrict ports to the available physical ports.
  if (absl::c_find(physical_ports, kDropPort) != physical_ports.end()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "cannot use physical port " << kDropPort
           << " as p4-symbolic reserves it to encode dropping a packet; see "
              "the documentation of `mark_to_drop` in v1mode.p4 for details";
  }
  ASSIGN_OR_RETURN(z3::expr ingress_port,
                   ingress_headers.Get("standard_metadata.ingress_port"));
  ASSIGN_OR_RETURN(z3::expr egress_port,
                   egress_headers.Get("standard_metadata.egress_spec"));
  // TODO: Support generating packet-out packets from the CPU port.
  if (physical_ports.empty()) {
    z3_solver->add(ingress_port != kCpuPort);
    z3_solver->add(ingress_port != kDropPort);
  } else {
    z3::expr ingress_port_is_physical = Z3Context().bool_val(false);
    z3::expr egress_port_is_physical = Z3Context().bool_val(false);
    for (int port : physical_ports) {
      ingress_port_is_physical =
          ingress_port_is_physical || ingress_port == port;
      egress_port_is_physical = egress_port_is_physical || egress_port == port;
    }
    z3_solver->add(ingress_port_is_physical);
    // TODO: Lift this constraint, it should not be necessary and
    // prevents generation of packet-ins.
    z3_solver->add(dropped || egress_port_is_physical);
  }

  // Assemble and return result.
  auto trace = SymbolicTrace{
      .matched_entries = std::move(matched_entries),
      .dropped = dropped,
      .got_cloned = got_cloned,
  };
  auto context = SymbolicContext{
      .ingress_port = ingress_port,
      .egress_port = egress_port,
      .ingress_headers = std::move(ingress_headers),
      .egress_headers = std::move(egress_headers),
      .trace = std::move(trace),
  };
  return std::make_unique<SolverState>(
      SolverState(data_plane.program, data_plane.entries, std::move(context),
                  std::move(z3_solver), std::move(translator)));
}

absl::StatusOr<std::optional<ConcreteContext>> Solve(
    const SolverState &solver_state) {
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
  z3::expr constraint = assertion(solver_state.context);
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
  solver_state->solver->push();
  solver_state->solver->add(assertion(solver_state->context));
  std::string smt = solver_state->GetSolverSMT();
  solver_state->solver->pop();
  return smt;
}

}  // namespace symbolic
}  // namespace p4_symbolic
