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

#include "p4_symbolic/packet_synthesizer/util.h"

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "gutil/gutil/status.h"
#include "p4_infra/netaddr/ipv6_address.h"
#include "p4_infra/p4_pdpi/ir_utils.h"
#include "p4_infra/string_encodings/decimal_string.h"
#include "p4_infra/string_encodings/hex_string.h"
#include "p4_symbolic/sai/sai.h"
#include "p4_symbolic/symbolic/operators.h"
#include "p4_symbolic/symbolic/solver_state.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/symbolic/util.h"
#include "p4_symbolic/z3_util.h"
#include "z3++.h"

namespace p4_symbolic {
namespace packet_synthesizer {
using ::p4_symbolic::symbolic::operators::BitAnd;
using ::p4_symbolic::symbolic::operators::Eq;
using ::p4_symbolic::symbolic::operators::PrefixEq;

namespace {

// Creates Z3 bitvector of the given width and value.
// The use of a template here is a hack to improve readability.
// TODO: Move to p4-symbolic utility library.
template <size_t num_bits>
inline z3::expr Bitvector(uint64_t value, z3::context& z3_context) {
  return z3_context.bv_val(value, num_bits);
}

// TODO: Move to netaddr.
struct Ipv6Range {
  netaddr::Ipv6Address value;
  int prefix_length = 0;
};

// TODO: Move to netaddr.
absl::StatusOr<Ipv6Range> ParseIpv6Range(absl::string_view ipv6_range) {
  std::vector<std::string> parts = absl::StrSplit(ipv6_range, '/');
  if (parts.size() != 2) {
    return gutil::InvalidArgumentErrorBuilder()
           << "invalid IPv6 range: " << ipv6_range;
  }
  ASSIGN_OR_RETURN(auto ipv6, netaddr::Ipv6Address::OfString(parts[0]),
                   _ << " while trying to parse Ipv6 range: " << ipv6_range);
  ASSIGN_OR_RETURN(int prefix_length,
                   string_encodings::DecimalStringToUint32(parts[1]),
                   _ << " while trying to parse Ipv6 range: " << ipv6_range);
  return Ipv6Range{
      .value = ipv6,
      .prefix_length = prefix_length,
  };
}

// https://www.iana.org/assignments/ipv6-address-space/ipv6-address-space.xhtml
absl::StatusOr<std::vector<Ipv6Range>> GetUnicastIpv6Ranges() {
  std::vector<Ipv6Range> result;
  // Global Unicast (RFC 4291).
  ASSIGN_OR_RETURN(result.emplace_back(), ParseIpv6Range("2000::/3"));
  // Unique Local Unicast (RFC 4193).
  ASSIGN_OR_RETURN(result.emplace_back(), ParseIpv6Range("fe80::/10"));
  return result;
}

// TODO: Move to p4-symbolic utility library and add unit tests.
absl::StatusOr<z3::expr> Ipv6PrefixLengthToZ3Mask(int prefix_length,
                                                  z3::context& z3_context) {
  if (prefix_length < 0 || prefix_length > 128) {
    return gutil::InvalidArgumentErrorBuilder()
           << "invalid IPv6 prefix length: " << prefix_length;
  }
  if (prefix_length > 64) {
    return Bitvector<128>(0xFFFF'FFFF'FFFF'FFFFu, z3_context).rotate_left(64) |
           Bitvector<128>(0xFFFF'FFFF'FFFF'FFFFu << (128 - prefix_length),
                          z3_context);
  } else {
    return Bitvector<128>(0xFFFF'FFFF'FFFF'FFFFu << (64 - prefix_length),
                          z3_context)
        .rotate_left(64);
  }
}

// TODO: Move to p4-symbolic utility library.
absl::StatusOr<z3::expr> Ipv6AddressToZ3Bitvector(
    const netaddr::Ipv6Address& ipv6, z3::context& z3_context) {
  std::bitset<128> bits = ipv6.ToBitset();
  uint64_t upper = (bits >> 64).to_ullong();
  uint64_t lower =
      (bits & std::bitset<128>(0xFFFF'FFFF'FFFF'FFFFu)).to_ullong();
  return Bitvector<128>(upper, z3_context).rotate_left(64) |
         Bitvector<128>(lower, z3_context);
}

absl::StatusOr<z3::expr> IsIpv6UnicastAddress(z3::expr ipv6_address) {
  z3::context& z3_context = ipv6_address.ctx();
  z3::expr result = z3_context.bool_val(false);
  ASSIGN_OR_RETURN(std::vector<Ipv6Range> ranges, GetUnicastIpv6Ranges());
  for (auto& range : ranges) {
    ASSIGN_OR_RETURN(z3::expr value,
                     Ipv6AddressToZ3Bitvector(range.value, z3_context));
    ASSIGN_OR_RETURN(z3::expr mask,
                     Ipv6PrefixLengthToZ3Mask(range.prefix_length, z3_context));
    result = result || ((ipv6_address & mask) == value);
  }
  return result;
}

absl::StatusOr<z3::expr> IrValueToZ3Bitvector(const pdpi::IrValue& value,
                                              int bitwidth,
                                              z3::context& z3_context) {
  ASSIGN_OR_RETURN(const std::string bytes,
                   pdpi::IrValueToNormalizedByteString(value, bitwidth));
  const std::string hex_string = string_encodings::ByteStringToHexString(bytes);
  return HexStringToZ3Bitvector(z3_context, hex_string, bitwidth);
}

}  // namespace

// TODO: We need extra constraints to avoid generating packets
// the switch deams invalid and drops, such as "martian" packets.
// Ideally this switch behavior would be fully modeled in P4 instead, and this
// function would disappear.
absl::Status AddSanePacketConstraints(
    p4_symbolic::symbolic::SolverState& state) {
  // TODO: Remove when these constraints are provided as part of
  // synthesis request.
  // RETURN_IF_ERROR(
  //    AddConstraintsPreventingIngressPortBeingInLoopbackMode(state));

  z3::context& z3_context = *state.context.z3_context;

  // ======Ethernet constraints======
  ASSIGN_OR_RETURN(z3::expr ethernet_src_addr,
                   state.context.ingress_headers.Get("ethernet.src_addr"));
  ASSIGN_OR_RETURN(z3::expr ethernet_dst_addr,
                   state.context.ingress_headers.Get("ethernet.dst_addr"));
  // Use "locally administered", "individual" MAC addresses
  // (U/L bit = 1, I/G bit = 0).
  // TODO: A multicast MAC address is not a legal src_mac, but it
  // is a legal dst_mac, thus applying the constraint only to the src_mac. If
  // applied to dst_mac, the constraint would make some of the NDV6_PUNTFLOWs
  // and VARIOUS_L3ADMIT_PUNTFLOWs unsatisfiable. Actually, the packets with
  // multicast dst_mac addresses are indeed marked to drop in l3_admit, however
  // such packets still continue to hit the acl_ingress table and some of the
  // entries cause such packets to get punted. So we should not disallow the
  // generation of such packets.
  state.solver->add(
      (ethernet_src_addr & Bitvector<48>(0x03'00'00'00'00'00, z3_context)) ==
      Bitvector<48>(0x02'00'00'00'00'00, z3_context));

  for (auto& mac_address : {ethernet_src_addr, ethernet_dst_addr}) {
    // Require key parts of the address to be nonzero to avoid corner cases.
    auto nonzero_masks = std::vector({
        Bitvector<48>(0x00'FF'FF'00'00'00, z3_context),  // OUI
    });
    for (auto& nonzero_mask : nonzero_masks) {
      state.solver->add((mac_address & nonzero_mask) != 0);
    }
  }
  // Require source MAC and destination MAC to differ.
  state.solver->add(ethernet_src_addr != ethernet_dst_addr);

  // ======IPv4 constraints======
  ASSIGN_OR_RETURN(z3::expr ipv4_src_addr,
                   state.context.ingress_headers.Get("ipv4.src_addr"));
  ASSIGN_OR_RETURN(z3::expr ipv4_dst_addr,
                   state.context.ingress_headers.Get("ipv4.dst_addr"));
  // Avoid martian IP addresses.
  // https://tools.ietf.org/html/rfc1122#section-3.2.1.3
  state.solver->add(
      (ipv4_src_addr & Bitvector<32>(0xFF'00'00'00, z3_context)) != 0);
  // Src IP address cannot be 255.255.255.255 (broadcast).
  state.solver->add(ipv4_src_addr != Bitvector<32>(0xFF'FF'FF'FF, z3_context));
  // Neither src nor dst IPv4 addresses can be 0.
  state.solver->add(ipv4_src_addr != Bitvector<32>(0, z3_context));
  state.solver->add(ipv4_dst_addr != Bitvector<32>(0, z3_context));
  // Neither src nor dst IPv4 addresses can be 127.0.0.1 (loopback).
  state.solver->add(ipv4_src_addr != Bitvector<32>(0x7F'00'00'01, z3_context));
  state.solver->add(ipv4_dst_addr != Bitvector<32>(0x7F'00'00'01, z3_context));

  // ======Ipv6 constraints======
  ASSIGN_OR_RETURN(z3::expr ipv6_src_addr,
                   state.context.ingress_headers.Get("ipv6.src_addr"));
  ASSIGN_OR_RETURN(z3::expr ipv6_dst_addr,
                   state.context.ingress_headers.Get("ipv6.dst_addr"));
  // Src IP address should be a unicast address.
  {
    ASSIGN_OR_RETURN(z3::expr constraint, IsIpv6UnicastAddress(ipv6_src_addr));
    state.solver->add(constraint);
  }
  // Neither src nor dst IPv6 addresses can be 0.
  state.solver->add(ipv6_src_addr != Bitvector<128>(0, z3_context));
  state.solver->add(ipv6_dst_addr != Bitvector<128>(0, z3_context));
  // Neither src nor dst IPv6 addresses can be ::1 (loopback).
  state.solver->add(ipv6_src_addr != Bitvector<128>(1, z3_context));
  state.solver->add(ipv6_dst_addr != Bitvector<128>(1, z3_context));

  // ======VLAN constraints==========
  // TODO: Make unconditional when we no longer need
  // backwards-compatibility.
  bool vlan = state.context.ingress_headers.ContainsKey(
      symbolic::util::GetHeaderValidityFieldName("vlan"));
  if (vlan) {
    ASSIGN_OR_RETURN(z3::expr vlan_id,
                     state.context.ingress_headers.Get("vlan.vlan_id"));
    // TODO: Consider testing the following VIDs when PacketIO is
    // properly modeled.
    state.solver->add(vlan_id != Bitvector<12>(0xFFF, z3_context));
    state.solver->add(vlan_id != Bitvector<12>(0x001, z3_context));
  }

  return absl::OkStatus();
}

// The following functions return Z3 constraints corresponding to `field`
// matching the given pdpi::IrMatch value.
absl::StatusOr<z3::expr> GetFieldMatchConstraints(z3::expr field, int bitwidth,
                                                  const pdpi::IrValue& match) {
  ASSIGN_OR_RETURN(z3::expr value,
                   IrValueToZ3Bitvector(match, bitwidth, field.ctx()));
  return Eq(field, value);
}
absl::StatusOr<z3::expr> GetFieldMatchConstraints(
    z3::expr field, int bitwidth, const pdpi::IrMatch::IrLpmMatch& match) {
  ASSIGN_OR_RETURN(z3::expr value,
                   IrValueToZ3Bitvector(match.value(), bitwidth, field.ctx()));
  return PrefixEq(field, value,
                  static_cast<unsigned int>(match.prefix_length()));
}
absl::StatusOr<z3::expr> GetFieldMatchConstraints(
    z3::expr field, int bitwidth, const pdpi::IrMatch::IrTernaryMatch& match) {
  ASSIGN_OR_RETURN(z3::expr value,
                   IrValueToZ3Bitvector(match.value(), bitwidth, field.ctx()));
  ASSIGN_OR_RETURN(z3::expr mask,
                   IrValueToZ3Bitvector(match.mask(), bitwidth, field.ctx()));
  ASSIGN_OR_RETURN(z3::expr masked_field, BitAnd(field, mask));
  return Eq(masked_field, value);
}
absl::StatusOr<z3::expr> GetFieldMatchConstraints(z3::expr field, int bitwidth,
                                                  const pdpi::IrMatch& match) {
  switch (match.match_value_case()) {
    case pdpi::IrMatch::kExact:
      return GetFieldMatchConstraints(field, bitwidth, match.exact());
    case pdpi::IrMatch::kLpm:
      return GetFieldMatchConstraints(field, bitwidth, match.lpm());
    case pdpi::IrMatch::kTernary:
      return GetFieldMatchConstraints(field, bitwidth, match.ternary());
    default:
      return gutil::InvalidArgumentErrorBuilder()
             << "Unsupported IR match type in " << match.ShortDebugString();
  }
}

}  // namespace packet_synthesizer
}  // namespace p4_symbolic
