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

#include "p4_symbolic/sai/fields.h"

#include "absl/strings/match.h"
#include "absl/strings/str_join.h"
#include "gutil/status.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "z3++.h"

namespace p4_symbolic {

namespace {

using ::p4_symbolic::symbolic::SymbolicPerPacketState;
using ::p4_symbolic::symbolic::Z3Context;

// The p4c compiler mangles field names from the local_metadata struct.
// As a workaround, we unmangle the names, best effort.
absl::StatusOr<z3::expr> GetUserMetadata(const std::string& field,
                                         const SymbolicPerPacketState& state) {
  // Compute set of mangled field names that match the given field name.
  std::vector<std::string> mangled_candidates;
  for (const auto& [key, _] : state) {
    if (absl::StartsWith(key, "scalars.userMetadata.") &&
        absl::StrContains(key, field)) {
      mangled_candidates.push_back(key);
    }
  }

  if (mangled_candidates.size() == 1) {
    return state.Get(mangled_candidates[0]);
  }

  auto error = gutil::InternalErrorBuilder()
               << "unable to disambiguate metadata field '" << field << "': ";
  if (mangled_candidates.empty())
    return error << "no matching fields found in config";
  return error << "several mangled fields in the config match:\n- "
               << absl::StrJoin(mangled_candidates, "\n- ");
}

}  // namespace

absl::StatusOr<SaiFields> GetSaiFields(const SymbolicPerPacketState& state) {
  // Helpers to extract fields.
  std::vector<absl::Status> errors;
  auto get_field = [&](const std::string& field) -> z3::expr {
    auto result = state.Get(field);
    if (result.ok()) return *result;
    errors.push_back(result.status());
    // Return dummy.
    return z3::expr(Z3Context());
  };
  auto get_metadata_field = [&](const std::string& field) -> z3::expr {
    auto result = GetUserMetadata(field, state);
    if (result.ok()) return *result;
    errors.push_back(result.status());
    // Return dummy.
    return z3::expr(Z3Context());
  };

  auto ethernet = SaiEthernet{
      .valid = get_field("ethernet.$valid$"),
      .dst_addr = get_field("ethernet.dst_addr"),
      .src_addr = get_field("ethernet.src_addr"),
      .ether_type = get_field("ethernet.ether_type"),
  };
  auto ipv4 = SaiIpv4{
      .valid = get_field("ipv4.$valid$"),
      .version = get_field("ipv4.version"),
      .ihl = get_field("ipv4.ihl"),
      .dscp = get_field("ipv4.dscp"),
      .ecn = get_field("ipv4.ecn"),
      .total_len = get_field("ipv4.total_len"),
      .identification = get_field("ipv4.identification"),
      .reserved = get_field("ipv4.reserved"),
      .do_not_fragment = get_field("ipv4.do_not_fragment"),
      .more_fragments = get_field("ipv4.more_fragments"),
      .frag_offset = get_field("ipv4.frag_offset"),
      .ttl = get_field("ipv4.ttl"),
      .protocol = get_field("ipv4.protocol"),
      .header_checksum = get_field("ipv4.header_checksum"),
      .src_addr = get_field("ipv4.src_addr"),
      .dst_addr = get_field("ipv4.dst_addr"),
  };
  auto local_metadata = SaiLocalMetadata{
      .admit_to_l3 = get_metadata_field("admit_to_l3"),
      .vrf_id = get_metadata_field("vrf_id"),
      .mirror_session_id_valid = get_metadata_field("mirror_session_id_valid"),
  };

  if (!errors.empty()) {
    return gutil::InternalErrorBuilder()
           << "Errors while trying to extract hard coded fields:\n- "
           << absl::StrJoin(errors, "\n- ",
                            [](std::string* out, const absl::Status& error) {
                              absl::StrAppend(out, error.ToString());
                            });
  }
  return SaiFields{
      .headers = SaiHeaders{.ethernet = ethernet, .ipv4 = ipv4},
      .local_metadata = local_metadata,
  };
}

}  // namespace p4_symbolic
