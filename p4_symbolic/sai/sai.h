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

#ifndef PINS_P4_SYMBOLIC_SAI_SAI_H_
#define PINS_P4_SYMBOLIC_SAI_SAI_H_

#include <optional>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "p4_symbolic/symbolic/context.h"
#include "p4_symbolic/symbolic/solver_state.h"

namespace p4_symbolic {

// SAI-specific type names.
constexpr absl::string_view kPortIdTypeName = "port_id_t";
constexpr absl::string_view kVrfIdTypeName = "vrf_id_t";

// Checks if the set of physical ports is the same as the set of numeric IDs
// passed as the static mapping for "port_id_t".
absl::Status CheckPhysicalPortAndPortIdTypeValueConsistency(
    const std::vector<int>& physical_ports,
    const symbolic::TranslationPerType& translation_per_type);

// Adds the partially static mapping for "vrf_id_t" if such mapping is not
// present in `translation_per_type`.
absl::Status AddVrfIdTypeTranslation(
    symbolic::TranslationPerType& translation_per_type);

// Returns the mangled user metadata field name of the given `header_name` and
// `field_name`. Note that this function is specific to SAI because it assumes
// the local metadata header type name to be `local_metadata_t`.
absl::StatusOr<std::string> GetUserMetadataFieldName(
    absl::string_view field_name,
    const symbolic::SymbolicPerPacketState& state);

// Returns the concrete value of `local_metadata.ingress_port` given the
// `solver_state`. Note that this function is specific to SAI because it assumes
// the existence of `local_metadata_t` header type and that the header type has
// a field called `ingress_port`.
absl::StatusOr<std::string> GetLocalMetadataIngressPortFromModel(
    const symbolic::SolverState& solver_state,
    std::optional<symbolic::SymbolicPerPacketState> headers = std::nullopt);

// Adds solver constraints for entry restrictions.
// Right now only the entry restrictions of "vrf_table" and
// "acl_pre_ingress_table" are implemented.
// TODO: Note that this is for testing only and is not needed once
// P4-Constraints is integrated with P4-Symbolic.
absl::Status AddConstraintsForP4ConstraintsAnnotations(
    symbolic::SolverState& state);

// Adds solver constraints for each symbolic variable of type "vrf_id_t" to
// avoid synthesizing values of VRF 0.
// TODO: Note that this is for testing only and is not needed once
// P4-Constraints is integrated with P4-Symbolic.
absl::Status AddConstraintsToForbidVrfZero(symbolic::SolverState& state);

// Adds solver constraints for "acl_pre_ingress_table".
// TODO: Note that this is for testing only and is not needed once
// P4-Constraints is integrated with P4-Symbolic.
absl::Status AddConstraintsForAclPreIngressTable(symbolic::SolverState& state);

// For any entry in "egress_port_loopback_table" matching on port `p`, add a
// constraint avoiding `p` as ingress port.
// TODO: Remove when these constraints are provided as part of
// synthesis request.
absl::Status AddConstraintsPreventingIngressPortBeingInLoopbackMode(
    symbolic::SolverState& state);

// Adds solver constraints for "acl_ingress_table" (for middleblock).
// Reference:
// third_party/pins_infra/sai_p4/instantiations/google/acl_ingress.p4.
// TODO: Note that this is for testing only and is not needed once
// P4-Constraints is integrated with P4-Symbolic.
absl::Status AddConstraintsForAclIngressTable(symbolic::SolverState& state);

}  // namespace p4_symbolic

#endif  // PINS_P4_SYMBOLIC_SAI_SAI_H_
