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

#include <cstdint>
#include <optional>
#include <string>
#include <type_traits>
#include <unordered_set>
#include <vector>

#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/ascii.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "gutil/status.h"
#include "p4_symbolic/symbolic/context.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/symbolic/values.h"
#include "z3++.h"

namespace p4_symbolic {

absl::Status CheckPhysicalPortAndPortIdTypeValueConsistency(
    const std::vector<int> &physical_ports,
    const symbolic::TranslationPerType &translation_per_type) {
  absl::flat_hash_set<uint64_t> physical_port_set(physical_ports.begin(),
                                                  physical_ports.end());
  absl::flat_hash_set<uint64_t> numeric_value_set;
  if (auto it = translation_per_type.find(kPortIdTypeName);
      it != translation_per_type.end()) {
    for (const auto &[_, numeric_value] : it->second.static_mapping)
      numeric_value_set.insert(numeric_value);
  }

  if (physical_port_set != numeric_value_set) {
    return absl::InvalidArgumentError(absl::StrCat(
        "Input physical port is inconsistent with the static mapping for ",
        kPortIdTypeName));
  }

  return absl::OkStatus();
}

absl::Status AddVrfIdTypeTranslation(
    symbolic::TranslationPerType &translation_per_type) {
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

absl::StatusOr<std::string> GetUserMetadataFieldName(
    absl::string_view field_name,
    const symbolic::SymbolicPerPacketState &state) {
  // Compute set of mangled field names that match the given field name.
  std::vector<std::string> mangled_candidates;

  // p4c seems to use the following template to name user metadata fields:
  //
  // - Until ~ 2022-11-01:
  //   "scalars.userMetadata._<field name><a number>"
  //
  // - After ~ 2022-11-01:
  //  "scalars.<user metadata typename>._<field name><a number>", where
  //  <user metadata typename> is the header type name of the given
  //  `header_name`.
  //
  // We look for names that match these templates.
  // TODO: Remove the old prefix eventually when we no
  // longer need backward compatibility.
  std::vector<std::string> fully_qualified_field_prefixes;
  fully_qualified_field_prefixes.reserve(2);
  // Old prefix.
  fully_qualified_field_prefixes.push_back(
      absl::StrCat("scalars.userMetadata._", field_name));
  // New prefix. Note that this is SAI-specific.
  fully_qualified_field_prefixes.push_back(
      absl::StrCat("scalars.local_metadata_t._", field_name));

  for (const auto &[key, _] : state) {
    for (absl::string_view prefix : fully_qualified_field_prefixes) {
      if (absl::StartsWith(key, prefix) && key.length() > prefix.length() &&
          absl::ascii_isdigit(key.at(prefix.length()))) {
        mangled_candidates.push_back(key);
      }
    }
  }

  if (mangled_candidates.size() == 1) {
    return mangled_candidates.back();
  }

  auto error = gutil::InternalErrorBuilder()
               << "unable to disambiguate metadata field '" << field_name
               << "': ";
  if (mangled_candidates.empty()) {
    return error << "no matching fields found in config: "
                 << absl::StrJoin(state, "\n  - ",
                                  [](std::string *out, const auto &key_value) {
                                    absl::StrAppend(out, key_value.first);
                                  });
  }
  return error << "several mangled fields in the config match:\n- "
               << absl::StrJoin(mangled_candidates, "\n- ");
}

absl::StatusOr<std::string> GetLocalMetadataIngressPortFromModel(
    const symbolic::SolverState &solver_state) {
  ASSIGN_OR_RETURN(std::string ingress_port_field_name,
                   GetUserMetadataFieldName(
                       "ingress_port", solver_state.context.parsed_headers));
  ASSIGN_OR_RETURN(
      z3::expr ingress_port_expr,
      solver_state.context.parsed_headers.Get(ingress_port_field_name));
  ASSIGN_OR_RETURN(auto translated_value,
                   symbolic::values::TranslateZ3ValueStringToP4RT(
                       solver_state.solver->get_model()
                           .eval(ingress_port_expr, true)
                           .to_string(),
                       ingress_port_field_name,
                       /*type_name=*/std::nullopt, solver_state.translator));
  return translated_value.first;
}

}  // namespace p4_symbolic
