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

#include "absl/algorithm/container.h"
#include "absl/cleanup/cleanup.h"
#include "absl/memory/memory.h"
#include "absl/types/optional.h"
#include "glog/logging.h"
#include "gutil/status.h"
#include "p4_symbolic/symbolic/control.h"
#include "p4_symbolic/symbolic/operators.h"
#include "p4_symbolic/symbolic/packet.h"
#include "p4_symbolic/symbolic/util.h"
#include "p4_symbolic/z3_util.h"

namespace p4_symbolic {
namespace symbolic {

// A port reserved to encode dropping packets.
// The value is arbitrary; we choose the same value as BMv2:
// https://github.com/p4lang/behavioral-model/blob/main/docs/simple_switch.md#standard-metadata
constexpr int kDropPort = 511;  // 2^9 - 1.
constexpr int kPortBitwidth = 9;

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

absl::StatusOr<std::unique_ptr<SolverState>> EvaluateP4Pipeline(
    const Dataplane &data_plane, const std::vector<int> &physical_ports) {
  // Use global context to define a solver.
  std::unique_ptr<z3::solver> z3_solver =
      std::make_unique<z3::solver>(Z3Context());

  // Initially, the p4runtime translator has empty state.
  values::P4RuntimeTranslator translator;

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
  if (physical_ports.empty()) {
    z3_solver->add(ingress_port != kDropPort);
  } else {
    z3::expr ingress_port_is_physical = Z3Context().bool_val(false);
    z3::expr egress_port_is_physical = Z3Context().bool_val(false);
    for (int port : physical_ports) {
      ingress_port_is_physical =
          ingress_port_is_physical || ingress_port == port;
      egress_port_is_physical = egress_port_is_physical || egress_port == port;
    }
    z3_solver->add(ingress_port != kDropPort && ingress_port_is_physical);
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
  return std::make_unique<SolverState>(SolverState{
      .program = data_plane.program,
      .entries = data_plane.entries,
      .context = std::move(context),
      .solver = std::move(z3_solver),
      .translator = std::move(translator),
  });
}

absl::StatusOr<std::optional<ConcreteContext>> Solve(
    const std::unique_ptr<SolverState> &solver_state,
    const Assertion &assertion) {
  z3::expr constraint = assertion(solver_state->context);

  solver_state->solver->push();
  solver_state->solver->add(constraint);
  z3::check_result check_result = solver_state->solver->check();
  switch (check_result) {
    case z3::unsat:
    case z3::unknown:
      solver_state->solver->pop();
      return absl::nullopt;

    case z3::sat:
      z3::model packet_model = solver_state->solver->get_model();
      ASSIGN_OR_RETURN(
          ConcreteContext result,
          util::ExtractFromModel(solver_state->context, packet_model,
                                 solver_state->translator));
      solver_state->solver->pop();
      return result;
  }
  LOG(DFATAL) << "invalid Z3 check() result: "
              << static_cast<int>(check_result);
  return absl::nullopt;
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
