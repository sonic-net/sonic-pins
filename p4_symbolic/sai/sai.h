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

#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "p4_symbolic/symbolic/symbolic.h"

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

// Returns the concrete value of the field `local_metadata.ingress_port` right
// after parser processing based on the given model.
absl::StatusOr<std::string> GetLocalMetadataIngressPortFromModel(
    const symbolic::SolverState& solver_state);

} // namespace p4_symbolic

#endif  // PINS_INFRA_P4_SYMBOLIC_SAI_SAI_H_
