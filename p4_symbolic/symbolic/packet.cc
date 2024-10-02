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

// Contains helpers for creating, extracting, and managing concerete and
// symbolic packet structs.

#include "p4_symbolic/symbolic/packet.h"

#include <string>

namespace p4_symbolic {
namespace symbolic {
namespace packet {

namespace {

// Get the symbolic field value from state or return a default value
// of the given size.
z3::expr GetOrDefault(SymbolicPerPacketState state, const std::string &field,
                      unsigned int default_value_bit_size) {
  if (state.ContainsKey(field)) {
    return state.Get(field).value();
  }
  return Z3Context().bv_val(-1, default_value_bit_size);
}

}  // namespace

SymbolicPacket ExtractSymbolicPacket(SymbolicPerPacketState state) {
  z3::expr ipv6_src = GetOrDefault(state, "ipv6.src_addr", 128);
  z3::expr ipv6_dst = GetOrDefault(state, "ipv6.dst_addr", 128);

  return SymbolicPacket{GetOrDefault(state, "ethernet.src_addr", 48),
                        GetOrDefault(state, "ethernet.dst_addr", 48),
                        GetOrDefault(state, "ethernet.ether_type", 16),

                        GetOrDefault(state, "ipv4.src_addr", 32),
                        GetOrDefault(state, "ipv4.dst_addr", 32),
                        ipv6_dst.extract(127, 64),
                        ipv6_dst.extract(63, 0),
                        GetOrDefault(state, "ipv4.protocol", 8),
                        GetOrDefault(state, "ipv4.dscp", 6),
                        GetOrDefault(state, "ipv4.ttl", 8),

                        GetOrDefault(state, "icmp.type", 8)};
}

ConcretePacket ExtractConcretePacket(SymbolicPacket packet, z3::model model) {
  return {model.eval(packet.eth_src, true).to_string(),
          model.eval(packet.eth_dst, true).to_string(),
          model.eval(packet.eth_type, true).to_string(),

          model.eval(packet.ipv4_src, true).to_string(),
          model.eval(packet.ipv4_dst, true).to_string(),
          model.eval(packet.ipv6_dst_upper, true).to_string(),
          model.eval(packet.ipv6_dst_lower, true).to_string(),
          model.eval(packet.protocol, true).to_string(),
          model.eval(packet.dscp, true).to_string(),
          model.eval(packet.ttl, true).to_string(),

          model.eval(packet.icmp_type, true).to_string()};
}

}  // namespace packet
}  // namespace symbolic
}  // namespace p4_symbolic
