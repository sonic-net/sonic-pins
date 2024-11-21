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

#include "p4_symbolic/sai/parser.h"

#include "gutil/status.h"
#include "p4_symbolic/sai/fields.h"
#include "p4_symbolic/symbolic/operators.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/z3_util.h"
#include "z3++.h"

namespace p4_symbolic {

using ::p4_symbolic::symbolic::SymbolicPerPacketState;

absl::StatusOr<std::vector<z3::expr>> EvaluateSaiParser(
    const SymbolicPerPacketState& state) {
  std::vector<z3::expr> constraints;

  ASSIGN_OR_RETURN(SaiFields fields, GetSaiFields(state));
  // TODO: Make non-optional when we no longer need
  // backwards-compatability.
  std::optional<SaiPacketOut>& packet_out = fields.headers.packet_out;
  SaiEthernet& erspan_ethernet = fields.headers.erspan_ethernet;
  SaiIpv4& erspan_ipv4 = fields.headers.erspan_ipv4;
  SaiGre& erspan_gre = fields.headers.erspan_gre;
  SaiEthernet& ethernet = fields.headers.ethernet;
  SaiIpv6& tunnel_encap_ipv6 = fields.headers.tunnel_encap_ipv6;
  SaiGre& tunnel_encap_gre = fields.headers.tunnel_encap_gre;
  SaiIpv4& ipv4 = fields.headers.ipv4;
  SaiIpv6& ipv6 = fields.headers.ipv6;
  SaiUdp& udp = fields.headers.udp;
  SaiTcp& tcp = fields.headers.tcp;
  SaiIcmp& icmp = fields.headers.icmp;
  SaiArp& arp = fields.headers.arp;
  SaiLocalMetadata& local_metadata = fields.local_metadata;
  V1ModelStandardMetadata& standard_metadata = fields.standard_metadata;
  z3::expr bv_true = Z3Context().bv_val(1, 1);
  z3::expr bv_false = Z3Context().bv_val(0, 1);

  // `start` state.
  constraints.push_back(!erspan_ethernet.valid);
  constraints.push_back(!erspan_ipv4.valid);
  constraints.push_back(!erspan_gre.valid);
  constraints.push_back(!tunnel_encap_ipv6.valid);
  constraints.push_back(!tunnel_encap_gre.valid);
  constraints.push_back(local_metadata.admit_to_l3 == bv_false);
  constraints.push_back(local_metadata.vrf_id == 0);
  constraints.push_back(local_metadata.mirror_session_id_valid == bv_false);
  constraints.push_back(local_metadata.ingress_port ==
                        standard_metadata.ingress_port);
  constraints.push_back(local_metadata.route_metadata == 0);
  if (local_metadata.bypass_ingress.has_value()) {
    // TODO: Make unconditional when we no longer need
    // backwards-compatability.
    constraints.push_back(*local_metadata.bypass_ingress == false);
  }

  // `parse_packet_out` state.
  if (packet_out.has_value()) {
    // TODO: Make unconditional when we no longer need
    // backwards-compatability.
    constraints.push_back(
        packet_out->valid ==
        (standard_metadata.ingress_port == symbolic::kCpuPort));
  }

  // `parse_ethernet` state.
  constraints.push_back(ethernet.valid == Z3Context().bool_val(true));
  constraints.push_back(ipv4.valid == (ethernet.ether_type == 0x0800));
  constraints.push_back(ipv6.valid == (ethernet.ether_type == 0x86dd));
  constraints.push_back(arp.valid == (ethernet.ether_type == 0x0806));

  // `parse_ipv{4,6}` states.
  constraints.push_back(icmp.valid == (ipv4.valid && ipv4.protocol == 0x01 ||
                                       ipv6.valid && ipv6.next_header == 0x3a));
  constraints.push_back(tcp.valid == (ipv4.valid && ipv4.protocol == 0x06 ||
                                      ipv6.valid && ipv6.next_header == 0x06));
  constraints.push_back(udp.valid == (ipv4.valid && ipv4.protocol == 0x11 ||
                                      ipv6.valid && ipv6.next_header == 0x11));

  // `parse_tcp` state.
  // We use `!a || b` to express `a implies b`.
  constraints.push_back(!tcp.valid ||
                        (local_metadata.l4_src_port == tcp.src_port &&
                         local_metadata.l4_dst_port == tcp.dst_port));

  // `parse_udp` state.
  // We use `!a || b` ito express `a implies b`.
  constraints.push_back(!udp.valid ||
                        (local_metadata.l4_src_port == udp.src_port &&
                         local_metadata.l4_dst_port == udp.dst_port));

  return constraints;
}

}  // namespace p4_symbolic
