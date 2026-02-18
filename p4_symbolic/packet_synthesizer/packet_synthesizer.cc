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

#include "p4_symbolic/packet_synthesizer/packet_synthesizer.h"

#include <memory>
#include <optional>
#include <utility>
#include <vector>

#include "absl/log/log.h"
#include "absl/memory/memory.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/time.h"
#include "google/protobuf/duration.pb.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/timer.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesis_criteria.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesis_criteria.pb.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesizer.pb.h"
#include "p4_symbolic/packet_synthesizer/util.h"
#include "p4_symbolic/packet_synthesizer/z3_model_to_packet.h"
#include "p4_symbolic/symbolic/solver_state.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/symbolic/util.h"
#include "p4_symbolic/symbolic/values.h"
#include "z3++.h"

namespace p4_symbolic::packet_synthesizer {
namespace {

using ::p4_symbolic::symbolic::SolverState;

// Adds logical assertions corresponding to the given `criteria` (for packet
// input header) to `solver_state`.
absl::Status AddConstraintsForInputPacketHeader(const HeaderCriteria& criteria,
                                                SolverState& solver_state) {
  // Loop over the list of field criteria, adding the constraints for each
  // criteria to the frame. The overall constraint for `criteria` will
  // effectively be the conjunction of the constraints for each
  // `field_criterion`).
  for (const HeaderCriteria::FieldCriterion& field_criterion :
       criteria.field_criteria()) {
    const pdpi::IrMatch& field_match = field_criterion.field_match();

    // Get the symbolic expression representing the input packet header value of
    // the field in the given field match.
    ASSIGN_OR_RETURN(z3::expr field, solver_state.context.ingress_headers.Get(
                                         field_match.name()));

    // Generate the constraint corresponding to the given field match.
    ASSIGN_OR_RETURN(const int bitwidth,
                     symbolic::util::GetFieldBitwidth(field_match.name(),
                                                      solver_state.program));
    ASSIGN_OR_RETURN(z3::expr constraint,
                     GetFieldMatchConstraints(field, bitwidth, field_match));

    // Negate the constraint if needed.
    if (field_criterion.negated()) {
      constraint = !constraint;
    }
    // Add the constraint to the frame.
    solver_state.solver->add(constraint);
  }
  return absl::OkStatus();
}

// Adds logical assertions corresponding to the given `criteria` (for packet
// ingress port) to `solver_state`.
absl::Status AddConstraintsForIngressPort(const PortCriteria& criteria,
                                          SolverState& solver_state) {
  solver_state.solver->add(solver_state.context.ingress_port ==
                           criteria.v1model_port());
  return absl::OkStatus();
}

// The following functions add logical assertions to the current solver state
// corresponding to the given `criteria`.
absl::Status AddConstraints(const OutputCriteria& criteria,
                            SolverState& solver_state) {
  solver_state.solver->add(criteria.drop_expected()
                               ? solver_state.context.trace.dropped
                               : !solver_state.context.trace.dropped);
  return absl::OkStatus();
}
absl::Status AddConstraints(const TableReachabilityCriteria& criteria,
                            SolverState& solver_state) {
  const auto& table_name = criteria.table_name();
  const auto& match = solver_state.context.trace.matched_entries.at(table_name);
  solver_state.solver->add(match.matched);
  return absl::OkStatus();
}
absl::Status AddConstraints(const TableEntryReachabilityCriteria& criteria,
                            SolverState& solver_state) {
  const auto& table_name = criteria.table_name();
  auto& match = solver_state.context.trace.matched_entries.at(table_name);
  solver_state.solver->add(match.entry_index == criteria.match_index());

  return absl::OkStatus();
}

}  // namespace

absl::StatusOr<std::unique_ptr<PacketSynthesizer>> PacketSynthesizer::Create(
    const PacketSynthesisParams& params) {
  gutil::Timer timer;

  // Extract data from params.
  const p4::v1::ForwardingPipelineConfig& config = params.pipeline_config();
  std::vector<p4::v1::Entity> entities(params.pi_entities().begin(),
                                       params.pi_entities().end());
  std::vector<int> physical_ports(params.physical_port().begin(),
                                  params.physical_port().end());
  symbolic::TranslationPerType translation_per_type;
  for (const auto& [type_name, data] : params.translation_per_type()) {
    symbolic::values::TranslationData translation;
    translation.dynamic_translation = data.dynamic_translation();
    for (const auto& mapping : data.static_mapping()) {
      translation.static_mapping.push_back(
          {mapping.string_value(), mapping.integer_value()});
    }
    translation_per_type.insert({type_name, translation});
  }

  // Evaluate P4 pipeline to get solver_state.
  ASSIGN_OR_RETURN(auto solver_state,
                   symbolic::EvaluateP4Program(config, entities, physical_ports,
                                               translation_per_type));

  // TODO: Avoid generating packets that are always dropped.
  RETURN_IF_ERROR(AddSanePacketConstraints(*solver_state));

  LOG(INFO) << "Generated the SMT formula in " << timer.GetDuration();

  // The p4-symbolic's solver_state contains the symbolic variables and the
  // SMT formula corresponding to the inputs (P4 program, entries, etc.) passed
  // to Create.
  return absl::WrapUnique(new PacketSynthesizer(std::move(*solver_state)));
}

// Performs DFS based symbolic execution
// and synthesizes packets for path coverage
// (go/p4-symbolic-path-coverage).
absl::StatusOr<PacketSynthesisResults>
PacketSynthesizer::SynthesizePacketsForPathCoverage(
    const PacketSynthesisParams& params) {
  gutil::Timer timer;

  // Extract data from params.
  const p4::v1::ForwardingPipelineConfig& config = params.pipeline_config();
  std::vector<p4::v1::Entity> entities(params.pi_entities().begin(),
                                       params.pi_entities().end());
  std::vector<int> physical_ports(params.physical_port().begin(),
                                  params.physical_port().end());
  symbolic::TranslationPerType translation_per_type;
  for (const auto& [type_name, data] : params.translation_per_type()) {
    symbolic::values::TranslationData translation;
    translation.dynamic_translation = data.dynamic_translation();
    for (const auto& mapping : data.static_mapping()) {
      translation.static_mapping.push_back(
          {mapping.string_value(), mapping.integer_value()});
    }
    translation_per_type.insert({type_name, translation});
  }

  // Evaluate P4 pipeline to get solver_state.
  ASSIGN_OR_RETURN(
      auto packet_synthesis_results,
      symbolic::
          EvaluateP4ProgramAndSynthesizePacketsCoveringAllControlFlowPaths(
              config, entities, physical_ports, translation_per_type));

  LOG(INFO) << "Evaluated and Synthesized packets in " << timer.GetDuration();

  return packet_synthesis_results;
}

absl::StatusOr<PacketSynthesisResult> PacketSynthesizer::SynthesizePacket(
    const PacketSynthesisCriteria& criteria) {
  PacketSynthesisResult result;

  // Timer to keep end to end time spent in this function.
  gutil::Timer overall_timer;
  // Timer used for granular measurement of time spent on the main steps of this
  // function (gets reset after each step).
  gutil::Timer granular_timer;

  // Add synthesized packet criterion as Z3 assertions. Modify the incremental
  // solver stack accordingly.
  ASSIGN_OR_RETURN(const int popped_frame_count,
                   PrepareZ3SolverStack(criteria));
  result.mutable_metadata()->set_z3_solver_stack_popped_frame_count(
      popped_frame_count);
  result.mutable_metadata()->set_z3_solver_stack_preparation_time_ms(
      absl::ToInt64Milliseconds(granular_timer.GetDurationAndReset()));

  // Solve the constraints and generate the packet if satisfiable.
  z3::check_result check_result = solver_state_.solver->check();
  result.mutable_metadata()->set_z3_solver_time_ms(
      absl::ToInt64Milliseconds(granular_timer.GetDurationAndReset()));

  if (check_result == z3::check_result::sat) {
    std::optional<bool> drop_expected;
    if (criteria.has_output_criteria())
      drop_expected = criteria.output_criteria().drop_expected();
    ASSIGN_OR_RETURN(*result.mutable_synthesized_packet(),
                     SynthesizePacketFromZ3Model(
                         solver_state_, criteria.payload_criteria().payload(),
                         drop_expected));
  }
  result.mutable_metadata()->set_z3_model_eval_time_ms(
      absl::ToInt64Milliseconds(granular_timer.GetDurationAndReset()));

  result.mutable_metadata()->set_synthesize_packet_overall_time_ms(
      absl::ToInt64Milliseconds(overall_timer.GetDuration()));
  VLOG(1) << absl::Substitute("SynthesizePacket finished in $0 for\n$1",
                              absl::FormatDuration(overall_timer.GetDuration()),
                              criteria.ShortDebugString());
  return result;
}

absl::Status PacketSynthesizer::PushSolverFrame() {
  if (solver_frame_stack_size_ >= kSolverFrameStackOrder.size()) {
    return absl::InternalError("Cannot push a new frame to full solver stack");
  }
  solver_state_.solver->push();
  ++solver_frame_stack_size_;

  return absl::OkStatus();
}

absl::Status PacketSynthesizer::PopSolverFrames(int n) {
  if (n < 0) {
    return absl::InvalidArgumentError(
        absl::StrCat("Expected non-negative number of frames to pop, got ", n));
  }
  if (n == 0) {
    LOG(WARNING)
        << "Received duplicate consecutive requests, popping 0 frames.";
  }

  for (int i = 0; i < n; i++) {
    if (solver_frame_stack_size_ == 0) {
      return absl::InternalError("Cannot pop from empty solver stack");
    }
    solver_state_.solver->pop();
    --solver_frame_stack_size_;
  }

  return absl::OkStatus();
}

absl::Status PacketSynthesizer::AddFrameForCriteria(
    CriteriaVariant::CriteriaCase criteria_case,
    const PacketSynthesisCriteria& criteria) {
  // Add a new frame.
  RETURN_IF_ERROR(PushSolverFrame());

  // Add the constraints for the given `criteria_case`. If the input
  // `criteria` does not contain the corresponding criteria case, we add no
  // constraints to the frame.
  switch (criteria_case) {
    case CriteriaVariant::kOutputCriteria:
      if (criteria.has_output_criteria())
        return AddConstraints(criteria.output_criteria(), solver_state_);
      break;
    case CriteriaVariant::kInputPacketHeaderCriteria:
      if (criteria.has_input_packet_header_criteria()) {
        return AddConstraintsForInputPacketHeader(
            criteria.input_packet_header_criteria(), solver_state_);
      }
      break;
    case CriteriaVariant::kTableReachabilityCriteria:
      if (criteria.has_table_reachability_criteria())
        return AddConstraints(criteria.table_reachability_criteria(),
                              solver_state_);
      break;
    case CriteriaVariant::kTableEntryReachabilityCriteria:
      if (criteria.has_table_reachability_criteria())
        return AddConstraints(criteria.table_entry_reachability_criteria(),
                              solver_state_);
      break;
    case CriteriaVariant::kIngressPortCriteria:
      if (criteria.has_ingress_port_criteria())
        return AddConstraintsForIngressPort(criteria.ingress_port_criteria(),
                                            solver_state_);
      break;
    default:
      return gutil::InvalidArgumentErrorBuilder()
             << "Unsupported criteria case " << criteria_case << " for "
             << criteria.ShortDebugString();
  }

  return absl::OkStatus();
}

absl::StatusOr<int> PacketSynthesizer::PrepareZ3SolverStack(
    const PacketSynthesisCriteria& criteria) {
  // Find the first index from which the stack needs to be popped. This is
  // essentially the first index in which the currently encoded criteria is
  // different from the requested criteria.
  int pop_index = 0;
  for (; pop_index < kSolverFrameStackOrder.size(); pop_index++) {
    const CriteriaVariant::CriteriaCase criteria_case =
        kSolverFrameStackOrder[pop_index];
    ASSIGN_OR_RETURN(
        bool equal_variants,
        HaveEqualCriteriaVariants(criteria, current_criteria_, criteria_case));
    if (!equal_variants) break;
  }

  VLOG(1) << "Frame stack pop index is " << pop_index;

  // Pop the frames on top of pop_index (including itself).
  RETURN_IF_ERROR(PopSolverFrames(kSolverFrameStackOrder.size() - pop_index));

  // Push new frames.
  while (solver_frame_stack_size_ < kSolverFrameStackOrder.size()) {
    RETURN_IF_ERROR(AddFrameForCriteria(
        kSolverFrameStackOrder[solver_frame_stack_size_], criteria));
  }

  if (solver_frame_stack_size_ != kSolverFrameStackOrder.size()) {
    return absl::InternalError(absl::Substitute(
        "Expected frame size of $0, got $1", kSolverFrameStackOrder.size(),
        solver_frame_stack_size_));
  }

  current_criteria_ = criteria;

  return kSolverFrameStackOrder.size() - pop_index;
}

const SolverState& PacketSynthesizer::SolverState() { return solver_state_; }

}  // namespace p4_symbolic::packet_synthesizer
