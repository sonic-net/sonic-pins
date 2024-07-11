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

// Hardcodes the behavior of an interesting p4 parser that is part
// of the p4 program we are interested in.
// The hardcoded behavior sets the validity of certain header fields
// based on the fields in the packet, and sets the default values
// for local_metadata fields.

#include "p4_symbolic/symbolic/parser.h"

#include "p4_symbolic/symbolic/operators.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {
namespace parser {

absl::StatusOr<std::vector<z3::expr>> EvaluateHardcodedParser(
    const SymbolicPerPacketState &state) {
  std::vector<z3::expr> constraints;

  // Set initial value for vrf.
  ASSIGN_OR_RETURN(z3::expr vrf_id, state.Get("scalars.userMetadata.vrf_id"));
  ASSIGN_OR_RETURN(z3::expr vrf_constraint,
                   operators::Eq(vrf_id, Z3Context().bv_val(0, 1)));
  constraints.push_back(vrf_constraint);

  // l4_src_port and l4_dst_port are extracted from the headers if tcp or udp
  // were used, and set to zero otherwise.
  // We must be careful that these values are guarded by the proper validity
  // guards, or we will impose contradictory constraints.
  ASSIGN_OR_RETURN(z3::expr l4_src_port,
                   state.Get("scalars.userMetadata.l4_src_port"));
  ASSIGN_OR_RETURN(z3::expr l4_dst_port,
                   state.Get("scalars.userMetadata.l4_dst_port"));

  // Find out which headers the program supports.
  ASSIGN_OR_RETURN(z3::expr ipv4_valid, state.Get("ipv4.$valid$"));
  ASSIGN_OR_RETURN(z3::expr ipv6_valid, state.Get("ipv6.$valid$"));
  ASSIGN_OR_RETURN(z3::expr arp_valid, state.Get("arp.$valid$"));

  // Put restrictions on what "eth_type" can be and how it affects validity of
  // certain headers.
  ASSIGN_OR_RETURN(z3::expr eth_type, state.Get("ethernet.ether_type"));
  constraints.push_back(ipv4_valid == (eth_type == ETHERTYPE_IPV4));
  constraints.push_back(ipv6_valid == (eth_type == ETHERTYPE_IPV6));
  constraints.push_back(arp_valid == (eth_type == ETHERTYPE_ARP));

  // Put similar restrictions on the validity of protocol-specific headers.
  // Which protocol used is specified by ipv4.protcol or ipv6.next_headers.
  ASSIGN_OR_RETURN(z3::expr protocol, state.Get("ipv4.protocol"));
  ASSIGN_OR_RETURN(z3::expr next_header, state.Get("ipv6.next_header"));

  // ICMP.
  ASSIGN_OR_RETURN(z3::expr icmp_valid, state.Get("icmp.$valid$"));
  z3::expr icmp_valid_ipv4 = (protocol == IP_PROTOCOL_ICMP) && ipv4_valid;
  z3::expr icmp_valid_ipv6 = (next_header == IP_PROTOCOL_ICMPV6) && ipv6_valid;
  constraints.push_back(icmp_valid == (icmp_valid_ipv4 || icmp_valid_ipv6));

  // TCP.
  ASSIGN_OR_RETURN(z3::expr tcp_valid, state.Get("tcp.$valid$"));
  z3::expr tcp_valid_ipv4 = (protocol == IP_PROTOCOL_TCP) && ipv4_valid;
  z3::expr tcp_valid_ipv6 = (next_header == IP_PROTOCOL_TCP) && ipv6_valid;
  constraints.push_back(tcp_valid == (tcp_valid_ipv4 || tcp_valid_ipv6));

  // Set l4_src_port and l4_dst_port to those of tcp header, if tcp is used.
  ASSIGN_OR_RETURN(z3::expr tcp_src_port, state.Get("tcp.src_port"));
  ASSIGN_OR_RETURN(z3::expr tcp_dst_port, state.Get("tcp.dst_port"));
  ASSIGN_OR_RETURN(z3::expr l4_src_port_eq_tcp_src_port,
                   operators::Eq(tcp_src_port, l4_src_port));
  ASSIGN_OR_RETURN(z3::expr l4_dst_port_eq_tcp_dst_port,
                   operators::Eq(tcp_dst_port, l4_dst_port));

  constraints.push_back(z3::implies(tcp_valid, l4_src_port_eq_tcp_src_port));
  constraints.push_back(z3::implies(tcp_valid, l4_dst_port_eq_tcp_dst_port));

  // UDP.
  ASSIGN_OR_RETURN(z3::expr udp_valid, state.Get("udp.$valid$"));
  z3::expr udp_valid_ipv4 = (protocol == IP_PROTOCOL_UDP) && ipv4_valid;
  z3::expr udp_valid_ipv6 = (next_header == IP_PROTOCOL_UDP) && ipv6_valid;
  constraints.push_back(udp_valid == (udp_valid_ipv4 || udp_valid_ipv6));

  // Set l4_src_port and l4_dst_port to those of udp header, if udp is used.
  ASSIGN_OR_RETURN(z3::expr udp_src_port, state.Get("udp.src_port"));
  ASSIGN_OR_RETURN(z3::expr udp_dst_port, state.Get("udp.dst_port"));
  ASSIGN_OR_RETURN(z3::expr l4_src_port_eq_udp_src_port,
                   operators::Eq(udp_src_port, l4_src_port));
  ASSIGN_OR_RETURN(z3::expr l4_dst_port_eq_udp_dst_port,
                   operators::Eq(udp_dst_port, l4_dst_port));

  constraints.push_back(z3::implies(udp_valid, l4_src_port_eq_udp_src_port));
  constraints.push_back(z3::implies(udp_valid, l4_dst_port_eq_udp_dst_port));

  // Default values for l4_src_port and l4_dst_port.
  ASSIGN_OR_RETURN(z3::expr tcp_or_udp_valid,
                   operators::Or(tcp_valid, udp_valid));
  ASSIGN_OR_RETURN(z3::expr l4_src_port_constraint,
                   operators::Eq(l4_src_port, Z3Context().bv_val(0, 1)));
  ASSIGN_OR_RETURN(z3::expr l4_dst_port_constraint,
                   operators::Eq(l4_dst_port, Z3Context().bv_val(0, 1)));
  constraints.push_back(z3::implies(!tcp_or_udp_valid, l4_src_port_constraint));
  constraints.push_back(z3::implies(!tcp_or_udp_valid, l4_dst_port_constraint));

  // Done, return all constraints.
  return constraints;
}

}  // namespace parser
}  // namespace symbolic
}  // namespace p4_symbolic
