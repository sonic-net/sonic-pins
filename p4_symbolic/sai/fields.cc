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

#include <array>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/ascii.h"
#include "absl/strings/match.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "gutil/status.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/z3_util.h"
#include "z3++.h"

namespace p4_symbolic {

using ::p4_symbolic::symbolic::SymbolicPerPacketState;

absl::StatusOr<std::string> GetUserMetadataFieldName(
    const std::string& field, const symbolic::SymbolicPerPacketState& state) {
  // Compute set of mangled field names that match the given field name.
  std::vector<std::string> mangled_candidates;

  // p4c seems to use the following template to name user metadata fields:
  //
  // - Until ~ 2022-11-01:
  //   "scalars.userMetadata._<field name><a number>"
  //
  // - After ~ 2022-11-01:
  //  "scalars.<user metadata typename>._<field name><a number>", where
  //  <user metadata typename> is "local_metadata_t" in SAI P4.
  //
  // We look for names that match these templates.
  // TODO: Remove `old_prefix` eventually when we no longer
  // need backward compatability.
  const std::string old_prefix = absl::StrCat("scalars.userMetadata._", field);
  const std::string new_prefix =
      absl::StrCat("scalars.local_metadata_t._", field);
  for (const auto& [key, _] : state) {
    for (absl::string_view prefix : {old_prefix, new_prefix}) {
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
               << "unable to disambiguate metadata field '" << field << "': ";
  if (mangled_candidates.empty()) {
    return error << "no matching fields found in config: "
                 << absl::StrJoin(state, "\n  - ",
                                  [](std::string* out, const auto& key_value) {
                                    absl::StrAppend(out, key_value.first);
                                  });
  }
  return error << "several mangled fields in the config match:\n- "
               << absl::StrJoin(mangled_candidates, "\n- ");
}

namespace {

// The p4c compiler mangles field names from the local_metadata struct.
// As a workaround, we unmangle the names, best effort.
absl::StatusOr<z3::expr> GetUserMetadata(const std::string& field,
                                         const SymbolicPerPacketState& state) {
  ASSIGN_OR_RETURN(const std::string mangled_name,
                   GetUserMetadataFieldName(field, state));
  return state.Get(mangled_name);
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
  auto ipv6 = SaiIpv6{
      .valid = get_field("ipv6.$valid$"),
      .version = get_field("ipv6.version"),
      .dscp = get_field("ipv6.dscp"),
      .ecn = get_field("ipv6.ecn"),
      .flow_label = get_field("ipv6.flow_label"),
      .payload_length = get_field("ipv6.payload_length"),
      .next_header = get_field("ipv6.next_header"),
      .hop_limit = get_field("ipv6.hop_limit"),
      .src_addr = get_field("ipv6.src_addr"),
      .dst_addr = get_field("ipv6.dst_addr"),
  };
  auto udp = SaiUdp{
      .valid = get_field("udp.$valid$"),
      .src_port = get_field("udp.src_port"),
      .dst_port = get_field("udp.dst_port"),
      .hdr_length = get_field("udp.hdr_length"),
      .checksum = get_field("udp.checksum"),
  };
  auto tcp = SaiTcp{
      .valid = get_field("tcp.$valid$"),
      .src_port = get_field("tcp.src_port"),
      .dst_port = get_field("tcp.dst_port"),
      .seq_no = get_field("tcp.seq_no"),
      .ack_no = get_field("tcp.ack_no"),
      .data_offset = get_field("tcp.data_offset"),
      .res = get_field("tcp.res"),
      .flags = get_field("tcp.flags"),
      .window = get_field("tcp.window"),
      .checksum = get_field("tcp.checksum"),
      .urgent_ptr = get_field("tcp.urgent_ptr"),
  };
  auto icmp = SaiIcmp{
      .valid = get_field("icmp.$valid$"),
      .type = get_field("icmp.type"),
      .code = get_field("icmp.code"),
      .checksum = get_field("icmp.checksum"),
  };
  auto arp = SaiArp{
      .valid = get_field("arp.$valid$"),
      .hw_type = get_field("arp.hw_type"),
      .proto_type = get_field("arp.proto_type"),
      .hw_addr_len = get_field("arp.hw_addr_len"),
      .proto_addr_len = get_field("arp.proto_addr_len"),
      .opcode = get_field("arp.opcode"),
      .sender_hw_addr = get_field("arp.sender_hw_addr"),
      .sender_proto_addr = get_field("arp.sender_proto_addr"),
      .target_hw_addr = get_field("arp.target_hw_addr"),
      .target_proto_addr = get_field("arp.target_proto_addr"),
  };
  auto local_metadata = SaiLocalMetadata{
      .admit_to_l3 = get_metadata_field("admit_to_l3"),
      .vrf_id = get_metadata_field("vrf_id"),
      .l4_src_port = get_metadata_field("l4_src_port"),
      .l4_dst_port = get_metadata_field("l4_dst_port"),
      .mirror_session_id_valid = get_metadata_field("mirror_session_id_valid"),
      .ingress_port = get_metadata_field("ingress_port"),
  };
  auto standard_metadata = V1ModelStandardMetadata{
      .ingress_port = get_field("standard_metadata.ingress_port"),
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
      .headers = SaiHeaders{.ethernet = ethernet,
                            .ipv4 = ipv4,
                            .ipv6 = ipv6,
                            .udp = udp,
                            .tcp = tcp,
                            .icmp = icmp,
                            .arp = arp},
      .local_metadata = local_metadata,
      .standard_metadata = standard_metadata,
  };
}

}  // namespace p4_symbolic
