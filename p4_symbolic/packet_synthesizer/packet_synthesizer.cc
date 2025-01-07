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

#include <cstddef>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "absl/base/log_severity.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/time.h"
#include "gutil/status.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_symbolic/deparser.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesis_criteria.h"
#include "p4_symbolic/packet_synthesizer/util.h"
#include "p4_symbolic/sai/sai.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/symbolic/util.h"
#include "p4_symbolic/z3_util.h"

namespace p4_symbolic::packet_synthesizer {

namespace {
using ::p4_symbolic::symbolic::SolverState;

// Given a Z3 model, prepares a SynthesizedPacket by extracting the relevant
// fields from the model. The packet payload will be set to the contents of
// `packet_payload` parameter.
absl::StatusOr<SynthesizedPacket> SynthesizePacketFromZ3Model(
    const SolverState& solver_state, absl::string_view packet_payload,
    std::optional<bool> should_be_dropped) {
  z3::model model = solver_state.solver->get_model();
  ASSIGN_OR_RETURN(std::string packet,
                   p4_symbolic::DeparseIngressPacket(solver_state, model));
  ASSIGN_OR_RETURN(
      const bool dropped,
      p4_symbolic::EvalZ3Bool(solver_state.context.trace.dropped, model));
  if (dropped != should_be_dropped) {
    return absl::FailedPreconditionError(absl::Substitute(
        "Z3 model's drop prediction ($0) is inconsistent with the expectation "
        "($1)",
        dropped ? "drop" : "no drop", should_be_dropped ? "drop" : "no drop"));
  }
  ASSIGN_OR_RETURN(const bool got_cloned,
                   EvalZ3Bool(solver_state.context.trace.got_cloned, model));

  // Get mirrored from the model.
  ASSIGN_OR_RETURN(
      std::string mirror_session_id_valid_field_name,
      GetUserMetadataFieldName("mirror_session_id_valid",
                               solver_state.context.egress_headers));
  ASSIGN_OR_RETURN(z3::expr mirror_session_id_valid,
                   solver_state.context.egress_headers.Get(
                       mirror_session_id_valid_field_name));
  ASSIGN_OR_RETURN(const bool mirrored,
                   EvalZ3Bool(mirror_session_id_valid == 1, model));

  // Get ingress port from the model.
  ASSIGN_OR_RETURN(std::string local_metadata_ingress_port,
                   GetLocalMetadataIngressPortFromModel(solver_state));

  // TODO: p4-symbolic might miss that
  // local_metadata.ingress_port is p4runtime_translated. In such cases,
  // p4-symbolic returns the raw Z3 bitvector value. As a hacky workaround,
  // we assign the empty string ("") as the ingress port for such cases,
  // signaling that no port is picked by the test generator. Note
  // that we currently assume that local_metadata.ingress_port is a
  // decimal string in normal cases.
  if (absl::StartsWith(local_metadata_ingress_port, "#")) {
    // Z3 raw value is detected.
    local_metadata_ingress_port = "";
  }

  // Set packet payload.
  // TODO: Move this logic to the client.
  RET_CHECK(packet.payload().empty())
      << "where packet = " << packet.DebugString();
  *packet.mutable_payload() = packet_payload;

  // Avoid using bad next_header that causes packet to be dropped.
  // TODO: Move this logic to the client.
  RET_CHECK(packet.headers_size() > 0)
      << "where packet = " << packet.DebugString();
  auto& last_header = *packet.mutable_headers(packet.headers_size() - 1);
  if (last_header.ipv6_header().next_header() == "0x00") {
    // Use protocol number reserved for experimentation/testing (RFC3692).
    last_header.mutable_ipv6_header()->set_next_header(
        packetlib::IpNextHeader(253));
  } else if (last_header.ipv4_header().protocol() == "0x00") {
    // Use protocol number reserved for experimentation/testing (RFC3692).
    last_header.mutable_ipv4_header()->set_protocol(packetlib::IpProtocol(253));
  }

  SynthesizedPacket synthesized_packet;
  *synthesized_packet.mutable_packet() = packet;
  // Note that we get local_metadata.ingress_port as opposed to
  // standard_metadata.ingress_port because the former is how the
  // controller views the ports. Refer to
  // third_party/pins_infra/sai_p4/fixed/metadata.p4 for more info.
  synthesized_packet.set_ingress_port(local_metadata_ingress_port);
  // Currently, p4-symbolic has no generic, built-in support for
  // predicting whether a packet gets dropped and/or punted to the
  // controller. As a workaround, we hard-code some program-specific
  // predictions here; they may break in the future when the program
  // changes.
  //
  // The hard-coded predictions work as follows:
  // - We predict that a packet gets dropped iff (i) it got
  //   `mark_to_drop`'ed in the P4 program and (ii) it did not get
  //   mirrored. Criterion (ii) is needed because mirrored packets are
  //   not considered dropped, for the purposes of dataplane test.
  // - We predict that a packet gets punted iff (i) it got cloned in
  //   the P4 program and (ii) it did not get mirrored. Criterion (ii)
  //   is needed because mirroring is implemented through cloning, but
  //   mirrored packets are not considered "punted" (as they are
  //   forwarded in the dataplane). Luckily we know that mirrored
  //   packets never get punted, so the prediction should be sound.
  //
  // TODO: these hard-coded predictions are major tech debt
  // that has led to hard-to-debug problems in the past; replacing
  // them with sound, generic predictions is high priority.
  synthesized_packet.set_drop_expected(dropped && !mirrored);
  synthesized_packet.set_punt_expected(got_cloned && !mirrored);
  synthesized_packet.set_mirror_expected(mirrored);

  return synthesized_packet;
}

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
  Timer timer;

  // Extract data from params.
  const p4::v1::ForwardingPipelineConfig& config = params.pipeline_config();
  std::vector<p4::v1::TableEntry> entries(params.pi_entries().begin(),
                                          params.pi_entries().end());
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
                   p4_symbolic::symbolic::EvaluateP4Program(
                       config, entries, physical_ports, translation_per_type));

  // TODO: Avoid generating packets that are always dropped.
  RETURN_IF_ERROR(AddSanePacketConstraints(*solver_state));

  LOG(INFO) << "Generated the SMT formula in " << timer.GetDuration();

  // The p4-symbolic's solver_state contains the symbolic variables and the
  // SMT formula corresponding to the inputs (P4 program, entries, etc.) passed
  // to Create.
  return absl::WrapUnique(new PacketSynthesizer(std::move(*solver_state)));
}

absl::StatusOr<PacketSynthesisResult> PacketSynthesizer::SynthesizePacket(
    const PacketSynthesisCriteria& criteria) {
  PacketSynthesisResult result;
  Timer timer;

  // Add synthesized packet criterion as Z3 assertions. Modify the incremental
  // solver stack accordingly.
  RETURN_IF_ERROR(PrepareZ3SolverStack(criteria));

  // Solve the constraints and generate the packet if satisfiable.
  if (solver_state_.solver->check() == z3::check_result::sat) {
    ASSIGN_OR_RETURN(*result.mutable_synthesized_packet(),
                     SynthesizePacketFromZ3Model(
                         solver_state_, criteria.payload_criteria().payload(),
                         criteria.output_criteria().drop_expected()));
  }

  VLOG(1) << absl::Substitute("SynthesizePacket finished in $0 for\n$1",
                              absl::FormatDuration(timer.GetDuration()),
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
  if (n < 1) {
    return absl::InvalidArgumentError(
        absl::StrCat("Expected positive number of frames, got ", n));
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
    default:
      return gutil::InvalidArgumentErrorBuilder()
             << "Unsupported criteria case " << criteria.ShortDebugString();
  }

  return absl::OkStatus();
}

absl::Status PacketSynthesizer::PrepareZ3SolverStack(
    const PacketSynthesisCriteria& criteria) {
  // Find the first index from which the stack needs to be poped. This is
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

  return absl::OkStatus();
}

const SolverState& PacketSynthesizer::SolverState() { return solver_state_; }

}  // namespace p4_symbolic::packet_synthesizer
