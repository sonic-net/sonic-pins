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

// This file exposes the SAI header/metadata fields as Z3 expressions, making it
// easy to formulate constraints on these fields.

#ifndef PINS_P4_SYMBOLIC_SAI_FIELDS_H_
#define PINS_P4_SYMBOLIC_SAI_FIELDS_H_

#include <optional>

#include "absl/status/statusor.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "z3++.h"

namespace p4_symbolic {

// Symbolic version of `packet_in_header_t` in metadata.p4.
struct SaiPacketIn {
  z3::expr valid;
  z3::expr ingress_port;
  z3::expr target_egress_port;
  z3::expr unused_pad;
};

// Symbolic version of `packet_out_header_t` in metadata.p4.
struct SaiPacketOut {
  z3::expr valid;
  z3::expr egress_port;
  z3::expr submit_to_ingress;
  z3::expr unused_pad;
};

// Symbolic version of `struct ethernet_t` in headers.p4.
struct SaiEthernet {
  z3::expr valid;
  z3::expr dst_addr;
  z3::expr src_addr;
  z3::expr ether_type;
};

// Symbolic version of `struct ipv4_t` in headers.p4.
struct SaiIpv4 {
  z3::expr valid;
  z3::expr version;
  z3::expr ihl;
  z3::expr dscp;
  z3::expr ecn;
  z3::expr total_len;
  z3::expr identification;
  z3::expr reserved;
  z3::expr do_not_fragment;
  z3::expr more_fragments;
  z3::expr frag_offset;
  z3::expr ttl;
  z3::expr protocol;
  z3::expr header_checksum;
  z3::expr src_addr;
  z3::expr dst_addr;
};

// Symbolic version of `struct ipv6_t` in headers.p4.
struct SaiIpv6 {
  z3::expr valid;
  z3::expr version;
  z3::expr dscp;
  z3::expr ecn;
  z3::expr flow_label;
  z3::expr payload_length;
  z3::expr next_header;
  z3::expr hop_limit;
  z3::expr src_addr;
  z3::expr dst_addr;
};

// Symbolic version of `struct udp_t` in headers.p4.
struct SaiUdp {
  z3::expr valid;
  z3::expr src_port;
  z3::expr dst_port;
  z3::expr hdr_length;
  z3::expr checksum;
};

// Symbolic version of `struct tcp_t` in headers.p4.
struct SaiTcp {
  z3::expr valid;
  z3::expr src_port;
  z3::expr dst_port;
  z3::expr seq_no;
  z3::expr ack_no;
  z3::expr data_offset;
  z3::expr res;
  z3::expr flags;
  z3::expr window;
  z3::expr checksum;
  z3::expr urgent_ptr;
};

// Symbolic version of `struct icmp_t` in headers.p4.
struct SaiIcmp {
  z3::expr valid;
  z3::expr type;
  z3::expr code;
  z3::expr checksum;
};

// Symbolic version of `struct arp_t` in headers.p4.
struct SaiArp {
  z3::expr valid;
  z3::expr hw_type;
  z3::expr proto_type;
  z3::expr hw_addr_len;
  z3::expr proto_addr_len;
  z3::expr opcode;
  z3::expr sender_hw_addr;
  z3::expr sender_proto_addr;
  z3::expr target_hw_addr;
  z3::expr target_proto_addr;
};

// Symbolic version of `struct gre_t` in headers.p4.
struct SaiGre {
  z3::expr valid;
  z3::expr checksum_present;
  z3::expr routing_present;
  z3::expr key_present;
  z3::expr sequence_present;
  z3::expr strict_source_route;
  z3::expr recursion_control;
  z3::expr acknowledgement_present;
  z3::expr flags;
  z3::expr version;
  z3::expr protocol;
};

// Symbolic version of `struct headers_t` in metadata.p4.
struct SaiHeaders {
  // TODO: Make non-optional when we no longer need
  // backwards-compatability.
  std::optional<SaiPacketIn> packet_in;
  std::optional<SaiPacketOut> packet_out;

  SaiEthernet erspan_ethernet;
  SaiIpv4 erspan_ipv4;
  SaiGre erspan_gre;
  SaiEthernet ethernet;

  // Not extracted during parsing.
  SaiIpv6 tunnel_encap_ipv6;
  SaiGre tunnel_encap_gre;

  SaiIpv4 ipv4;
  SaiIpv6 ipv6;
  SaiUdp udp;
  SaiTcp tcp;
  SaiIcmp icmp;
  SaiArp arp;
};

// Symbolic version of `struct local_metadata_t` in metadata.p4.
// TODO: add missing fields.
struct SaiLocalMetadata {
  z3::expr admit_to_l3;
  z3::expr vrf_id;
  z3::expr l4_src_port;
  z3::expr l4_dst_port;
  z3::expr mirror_session_id_valid;
  z3::expr ingress_port;
  z3::expr route_metadata;
  // TODO: Make non-optional when we no longer need
  // backwards-compatability.
  std::optional<z3::expr> bypass_ingress;
};

// Symbolic version of `struct standard_metadata_t` in v1model.p4
// TODO: Add missing fields, as needed.
struct V1ModelStandardMetadata {
  z3::expr ingress_port;
};

struct SaiFields {
  SaiHeaders headers;
  SaiLocalMetadata local_metadata;
  V1ModelStandardMetadata standard_metadata;
};

absl::StatusOr<SaiFields> GetSaiFields(
    const symbolic::SymbolicPerPacketState& state);

// The p4c compiler "mangles" field names of user defined metadata and the
// mangled name is used in some places in p4-symbolic. This function returns
// the mangled name of a given user defined metadata field. Note that this is a
// workaround and done in a best effort fashion.
absl::StatusOr<std::string> GetUserMetadataFieldName(
    const std::string& field, const symbolic::SymbolicPerPacketState& state);

// The p4c compiler adds a special field ("$valid$") to each header
// corresponding to its validity. This function returns a field reference (in
// form of <header>.<field>) to the p4c generated validity field of the given
// `header`.
// Note: This function does NOT check if the given header exists.
std::string GetHeaderValidityFieldRef(absl::string_view header);

}  // namespace p4_symbolic

#endif  // PINS_P4_SYMBOLIC_SAI_FIELDS_H_
