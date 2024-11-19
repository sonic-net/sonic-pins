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
#include "p4_symbolic/sai/sai.h"

#include <memory>
#include <string>
#include <type_traits>
#include <unordered_set>
#include <vector>

#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_symbolic/parser.h"
#include "p4_symbolic/sai/parser.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/symbolic/values.h"

namespace p4_symbolic {

// Checks if the set of physical ports is the same as the set of numeric IDs
// passed as the static mapping for "port_id_t".
absl::Status CheckPhysicalPortAndPortIdTypeValueConsistency(
    const std::vector<int>& physical_ports,
    const symbolic::TranslationPerType& translation_per_type) {
  absl::flat_hash_set<uint64_t> physical_port_set(physical_ports.begin(),
                                                  physical_ports.end());
  absl::flat_hash_set<uint64_t> numeric_value_set;
  if (auto it = translation_per_type.find(kPortIdTypeName);
      it != translation_per_type.end()) {
    for (const auto& [_, numeric_value] : it->second.static_mapping)
      numeric_value_set.insert(numeric_value);
  }

  if (physical_port_set != numeric_value_set) {
    return absl::InvalidArgumentError(absl::StrCat(
        "Input physical port is inconsistent with the static mapping for ",
        kPortIdTypeName));
  }

  return absl::OkStatus();
}

// Adds partially static mapping for "vrf_id_t".
absl::Status AddVrfIdTypeTranslation(
    symbolic::TranslationPerType& translation_per_type) {
  if (translation_per_type.contains(kVrfIdTypeName)) {
    return absl::InvalidArgumentError(absl::StrCat(
        "Did not expect user defined translation for ", kVrfIdTypeName));
  }

  // TODO: A temporary workaround until the issue is fixed.
  // Map the string "" to value 0. The rest of the mapping is done dynamically.
  translation_per_type[kVrfIdTypeName] = symbolic::values::TranslationData{
      .static_mapping = {{"", 0}},
      .dynamic_translation = true,
  };

  return absl::OkStatus();
}

absl::StatusOr<std::unique_ptr<symbolic::SolverState>> EvaluateSaiPipeline(
    const p4::v1::ForwardingPipelineConfig& config,
    const std::vector<p4::v1::TableEntry>& entries,
    const std::vector<int>& physical_ports,
    symbolic::TranslationPerType translation_per_type) {
  // Check inputs for consistency.
  RETURN_IF_ERROR(CheckPhysicalPortAndPortIdTypeValueConsistency(
      physical_ports, translation_per_type));

  // Add translation for vrf_id_t.
  RETURN_IF_ERROR(AddVrfIdTypeTranslation(translation_per_type));

  ASSIGN_OR_RETURN(symbolic::Dataplane dataplane, ParseToIr(config, entries));
  ASSIGN_OR_RETURN(std::unique_ptr<symbolic::SolverState> state,
                   symbolic::EvaluateP4Pipeline(dataplane, physical_ports,
                                                translation_per_type));
  ASSIGN_OR_RETURN(std::vector<z3::expr> parser_constraints,
                   EvaluateSaiParser(state->context.ingress_headers));
  for (auto& constraint : parser_constraints) {
    state->solver->add(constraint);
  }
  return state;
}

absl::StatusOr<std::string> ExtractLocalMetadataIngressPortFromModel(
    const symbolic::SolverState& solver_state) {
  ASSIGN_OR_RETURN(
      p4_symbolic::SaiFields ingress_fields,
      p4_symbolic::GetSaiFields(solver_state.context.ingress_headers));
  ASSIGN_OR_RETURN(const std::string local_metadata_ingress_port_field_name,
                   p4_symbolic::GetUserMetadataFieldName(
                       "ingress_port", solver_state.context.ingress_headers));
  // Note: Do NOT directly use "local_metadata.ingress_port" as the field name
  // (see p4_symbolic::GetUserMetadataFieldName).
  return TranslateValueToP4RT(
      local_metadata_ingress_port_field_name,
      solver_state.solver->get_model()
          .eval(ingress_fields.local_metadata.ingress_port, true)
          .to_string(),
      solver_state.translator);
}

}  // namespace p4_symbolic
