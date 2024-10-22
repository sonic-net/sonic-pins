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

#include "p4_symbolic/symbolic/symbolic.h"
#include "z3++.h"

namespace p4_symbolic {

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

// Symbolic version of `struct headers_t` in metadata.p4.
struct SaiHeaders {
  SaiEthernet ethernet;
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

}  // namespace p4_symbolic

#endif  // PINS_P4_SYMBOLIC_SAI_FIELDS_H_
