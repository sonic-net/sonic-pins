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

// This file is responsible for evaluating a control construct in a P4
// program flow. A control construct could be a table match or a conditional
// leading to a table match.
//
// Check the header file for a detailed explanation.

#include "p4_symbolic/symbolic/control.h"

#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "gutil/gutil/status.h"
#include "p4_infra/packetlib/packetlib.pb.h"
#include "p4_symbolic/ir/ir.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesizer.pb.h"
#include "p4_symbolic/packet_synthesizer/z3_model_to_packet.h"
#include "p4_symbolic/symbolic/conditional.h"
#include "p4_symbolic/symbolic/context.h"
#include "p4_symbolic/symbolic/operators.h"
#include "p4_symbolic/symbolic/solver_state.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/symbolic/table.h"
#include "z3++.h"

namespace p4_symbolic::symbolic::control {

absl::StatusOr<z3::expr> IsDroppedPacket(const SymbolicPerPacketState &state,
                                         z3::context &z3_context) {
  ASSIGN_OR_RETURN(z3::expr egress_spec,
                   state.Get("standard_metadata.egress_spec"));
  return operators::Eq(egress_spec,
                       z3_context.bv_val(kDropPort, kPortBitwidth));
}

absl::StatusOr<SymbolicTableMatches> EvaluatePipeline(
    const std::string &pipeline_name, SolverState &state,
    SymbolicPerPacketState &headers, const z3::expr &guard) {
  if (auto it = state.program.pipeline().find(pipeline_name);
      it != state.program.pipeline().end()) {
    return EvaluateControl(it->second.initial_control(), state, headers, guard);
  }
  return gutil::InvalidArgumentErrorBuilder()
         << "cannot evaluate unknown pipeline: '" << pipeline_name << "'";
}

// Evaluate the pipeline (ingress or egress) using DFS style symbolic
// execution.
// This is currently being used to generate packets for path coverage
// (go/p4-symbolic-path-coverage).
absl::Status EvaluatePipelineDfs(
    const std::string &pipeline_name, SolverState &state,
    SymbolicPerPacketState &headers,
    packet_synthesizer::PacketSynthesisResults &results) {
  if (auto it = state.program.pipeline().find(pipeline_name);
      it != state.program.pipeline().end()) {
    return EvaluateControlDfs(it->second.initial_control(), state, headers,
                              pipeline_name, results);
  }
  return gutil::InvalidArgumentErrorBuilder()
         << "cannot evaluate unknown pipeline: '" << pipeline_name << "'";
}

absl::StatusOr<SymbolicTableMatches> EvaluateControl(
    const std::string &control_name, SolverState &state,
    SymbolicPerPacketState &headers, const z3::expr &guard) {
  // Base case: we got to the end of the evaluation, no more controls!
  if (control_name == ir::EndOfPipeline()) return SymbolicTableMatches();

  // Find out what type of control we need to evaluate.
  if (state.program.tables().contains(control_name)) {
    // Table: call EvaluateTable on table and its entries.
    const ir::Table &table = state.program.tables().at(control_name);
    return table::EvaluateTable(table, state, headers, guard);
  } else if (state.program.conditionals().contains(control_name)) {
    // Conditional: let EvaluateConditional handle it.
    const ir::Conditional &conditional =
        state.program.conditionals().at(control_name);
    return conditional::EvaluateConditional(conditional, state, headers, guard);
  } else {
    // Something else: unsupported.
    return absl::UnimplementedError(
        absl::StrCat("Unsupported control \"", control_name,
                     "\" is neither a table nor a conditional"));
  }
}

absl::Status EvaluateControlDfs(
    const std::string &control_name, SolverState &state,
    SymbolicPerPacketState &headers, const std::string &pipeline_name,
    packet_synthesizer::PacketSynthesisResults &results) {
  // Base case: we got to the end of the evaluation for the current pipeline.
  if (control_name == ir::EndOfPipeline()) {
    if (pipeline_name == "ingress") {
      // At the end of the ingress pipeline for a particular path in the
      // "parser-ingress" pipeline, the execution moves to the "egress"
      // pipeline. The "egress" pipeline is then evaluated with the current
      // path and the current headers packet state.

      // We check if the packet is dropped after the ingress pipeline.
      // If the parser is dropped, the execution doesn't move to the egress
      // pipeline.
      ASSIGN_OR_RETURN(z3::expr ingress_drop,
                       IsDroppedPacket(headers, *state.context.z3_context));

      state.solver->push();
      // TODO: Ingress_drop should be either true or false.
      // Can optimize by not calling the solver.
      state.solver->add(ingress_drop);
      z3::check_result check_result = state.solver->check();
      if (check_result == z3::check_result::sat) {
        // packet is dropped
        // Here we check for constraints related to statically translated values
        // TODO: check if we can add these constraints at the
        // beginning of evaluating parser pipeline.
        RETURN_IF_ERROR(symbolic::AddConstraintsForStaticallyTranslatedValues(
            state, headers));
        if (state.solver->check() == z3::check_result::sat) {
          // If the constraints are satisfied, a packet is synthesized.
          ASSIGN_OR_RETURN(
              packet_synthesizer::SynthesizedPacket synthesized_packet,
              packet_synthesizer::SynthesizePacketFromZ3Model(state, true,
                                                              headers));
          packet_synthesizer::PacketSynthesisResult packet_synthesis_result;
          *packet_synthesis_result.mutable_synthesized_packet() =
              synthesized_packet;
          *results.add_results() = packet_synthesis_result;
        }
      } else {
        state.solver->pop();
        state.solver->push();
        // If the packet is not dropped, the execution moves to the egress
        // pipeline.
        RETURN_IF_ERROR(
            control::EvaluatePipelineDfs("egress", state, headers, results));
      }
      state.solver->pop();
    } else {
      // At the end of the egress pipeline for a particular path in the
      // "parser-ingress-egress" pipeline, the execution ends.
      // The packet is checked for constraints related to statically translated
      // values. If the constraints are satisfied, a packet is synthesized.
      z3::check_result check_result = state.solver->check();
      if (check_result == z3::check_result::sat) {
        state.solver->push();
        // TODO: check if we can add these constraints at the
        // beginning of evaluating parser pipeline.
        RETURN_IF_ERROR(symbolic::AddConstraintsForStaticallyTranslatedValues(
            state, headers));
        if (state.solver->check() == z3::check_result::sat) {
          ASSIGN_OR_RETURN(
              packet_synthesizer::SynthesizedPacket synthesized_packet,
              packet_synthesizer::SynthesizePacketFromZ3Model(state, false,
                                                              headers));
          // add synthesized packet to results
          packet_synthesizer::PacketSynthesisResult packet_synthesis_result;
          *packet_synthesis_result.mutable_synthesized_packet() =
              synthesized_packet;
          *results.add_results() = packet_synthesis_result;
        }
        state.solver->pop();
      }
    }
    return absl::OkStatus();
  };

  // Find out what type of control we need to evaluate.
  if (state.program.tables().contains(control_name)) {
    // Table: call EvaluateTable on table and its entries.
    const ir::Table &table = state.program.tables().at(control_name);
    return table::EvaluateTableDfs(table, state, headers, pipeline_name,
                                   results);
  } else if (state.program.conditionals().contains(control_name)) {
    // Conditional: let EvaluateConditional handle it.
    const ir::Conditional &conditional =
        state.program.conditionals().at(control_name);
    return conditional::EvaluateConditionalDfs(conditional, state, headers,
                                               pipeline_name, results);
  } else {
    // Something else: unsupported.
    return absl::UnimplementedError(
        absl::StrCat("Unsupported control \"", control_name,
                     "\" is neither a table nor a conditional"));
  }
}

}  // namespace p4_symbolic::symbolic::control
