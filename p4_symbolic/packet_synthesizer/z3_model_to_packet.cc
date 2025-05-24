// Copyright 2025 Google LLC
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
// limitations under the License

#include "p4_symbolic/packet_synthesizer/z3_model_to_packet.h"

#include <optional>
#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "gutil/status.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_symbolic/sai/sai.h"
#include "p4_symbolic/symbolic/context.h"
#include "p4_symbolic/symbolic/deparser.h"
#include "p4_symbolic/symbolic/solver_state.h"
#include "p4_symbolic/z3_util.h"
#include "z3++.h"

namespace p4_symbolic::packet_synthesizer {

// Given a Z3 model, prepares a SynthesizedPacket by extracting the relevant
// fields from the model. The packet payload will be set to the contents of
// `packet_payload` parameter.
absl::StatusOr<SynthesizedPacket> SynthesizePacketFromZ3Model(
    const symbolic::SolverState &solver_state, absl::string_view packet_payload,
    std::optional<bool> should_be_dropped) {
  z3::model model = solver_state.solver->get_model();
  ASSIGN_OR_RETURN(std::string packet,
                   DeparseIngressPacket(solver_state, model));
  ASSIGN_OR_RETURN(const bool dropped,
                   EvalZ3Bool(solver_state.context.trace.dropped, model));
  if (should_be_dropped.has_value() && dropped != *should_be_dropped) {
    return absl::FailedPreconditionError(absl::Substitute(
        "Z3 model's drop prediction ($0) is inconsistent with the expectation "
        "($1)",
        dropped ? "drop" : "no drop", *should_be_dropped ? "drop" : "no drop"));
  }
  ASSIGN_OR_RETURN(const bool got_cloned,
                   EvalZ3Bool(solver_state.context.trace.got_cloned, model));

  // TODO: Remove this hack once we do not need to test older P4
  // programs that still use 'mirror_session_id_valid' metadata. Get mirrored
  // from the model.
  absl::StatusOr<std::string> mirror_session_id_valid_field_name =
      GetUserMetadataFieldName("mirror_session_id_valid",
                               solver_state.context.egress_headers);
  absl::StatusOr<std::string> marked_to_mirror_field_name =
      GetUserMetadataFieldName("marked_to_mirror",
                               solver_state.context.egress_headers);
  bool mirrored = false;

  if (mirror_session_id_valid_field_name.ok()) {
    ASSIGN_OR_RETURN(z3::expr mirror_session_id_valid,
                     solver_state.context.egress_headers.Get(
                         *mirror_session_id_valid_field_name));
    ASSIGN_OR_RETURN(mirrored, EvalZ3Bool(mirror_session_id_valid == 1, model));
  } else if (marked_to_mirror_field_name.ok()) {
    ASSIGN_OR_RETURN(
        z3::expr marked_to_mirror,
        solver_state.context.egress_headers.Get(*marked_to_mirror_field_name));
    ASSIGN_OR_RETURN(mirrored, EvalZ3Bool(marked_to_mirror == 1, model));
  } else {
    return absl::InvalidArgumentError(
        "Unable to get mirror-related metadata, neither "
        "`mirror_session_id_valid` "
        "nor `marked_to_mirror`, from egress_headers.");
  }

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
  {
    packetlib::Packet parsed_packet = packetlib::ParsePacket(packet);
    RET_CHECK(parsed_packet.payload().empty())
        << "where parsed_packet = " << parsed_packet.DebugString();
  }
  absl::StrAppend(&packet, packet_payload);

  SynthesizedPacket synthesized_packet;
  *synthesized_packet.mutable_packet() = packet;
  *synthesized_packet.mutable_debug_info()
       ->mutable_possibly_stale_parsed_version_of_packet() =
      packetlib::ParsePacket(packet);
  // Note that we get local_metadata.ingress_port as opposed to
  // standard_metadata.ingress_port because the former is how the
  // controller views the ports. Refer to
  // sonic-net/sonic-pins/sai_p4/fixed/metadata.p4 for more info.
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

// Synthesize Packet from Z3 Model
// It uses the headers passed as arguments and if the packet is dropped or not
// This is currently being used to generate packets for path coverage
// (go/p4-symbolic-path-coverage).
absl::StatusOr<packet_synthesizer::SynthesizedPacket>
SynthesizePacketFromZ3Model(const symbolic::SolverState &solver_state,
                            const bool dropped,
                            symbolic::SymbolicPerPacketState &headers) {
  z3::model model = solver_state.solver->get_model();

  ASSIGN_OR_RETURN(std::string packet,
                   DeparseIngressPacket(solver_state, model, headers));

  const bool got_cloned = false;

  absl::StatusOr<std::string> mirror_session_id_valid_field_name =
      GetUserMetadataFieldName("mirror_session_id_valid", headers);
  absl::StatusOr<std::string> marked_to_mirror_field_name =
      GetUserMetadataFieldName("marked_to_mirror", headers);
  bool mirrored = false;

  if (mirror_session_id_valid_field_name.ok()) {
    ASSIGN_OR_RETURN(z3::expr mirror_session_id_valid,
                     headers.Get(*mirror_session_id_valid_field_name));
    ASSIGN_OR_RETURN(mirrored, EvalZ3Bool(mirror_session_id_valid == 1, model));
  } else if (marked_to_mirror_field_name.ok()) {
    ASSIGN_OR_RETURN(z3::expr marked_to_mirror,
                     headers.Get(*marked_to_mirror_field_name));
    ASSIGN_OR_RETURN(mirrored, EvalZ3Bool(marked_to_mirror == 1, model));
  } else {
    return absl::InvalidArgumentError(
        "Unable to get mirror-related metadata, neither "
        "`mirror_session_id_valid` "
        "nor `marked_to_mirror`, from headers.");
  }

  // Get ingress port from the model.
  ASSIGN_OR_RETURN(std::string local_metadata_ingress_port,
                   GetLocalMetadataIngressPortFromModel(solver_state, headers));

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

  packet_synthesizer::SynthesizedPacket synthesized_packet;
  *synthesized_packet.mutable_packet() = packet;
  *synthesized_packet.mutable_debug_info()
       ->mutable_possibly_stale_parsed_version_of_packet() =
      packetlib::ParsePacket(packet);
  synthesized_packet.set_ingress_port(local_metadata_ingress_port);
  synthesized_packet.set_drop_expected(dropped && !mirrored);
  synthesized_packet.set_punt_expected(got_cloned && !mirrored);
  synthesized_packet.set_mirror_expected(mirrored);

  return synthesized_packet;
}
}  // namespace p4_symbolic::packet_synthesizer
