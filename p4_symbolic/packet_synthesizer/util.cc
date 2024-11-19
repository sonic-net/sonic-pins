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

#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "gutil/status.h"
#include "p4_pdpi/netaddr/ipv6_address.h"
#include "p4_pdpi/string_encodings/decimal_string.h"
#include "p4_pdpi/utils/ir.h"
#include "p4_symbolic/sai/fields.h"
#include "p4_symbolic/symbolic/operators.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/z3_util.h"

namespace p4_symbolic {
namespace packet_synthesizer {
using ::p4_symbolic::ir::P4Program;
using ::p4_symbolic::symbolic::operators::BitAnd;
using ::p4_symbolic::symbolic::operators::Eq;
using ::p4_symbolic::symbolic::operators::PrefixEq;

namespace {

// Creates Z3 bitvector of the given width and value.
// The use of a template here is a hack to improve readability.
// TODO: Move to p4-symbolic utility library.
template <size_t num_bits>
inline z3::expr Bitvector(uint64_t value) {
  return p4_symbolic::Z3Context().bv_val(value, num_bits);
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
  ASSIGN_OR_RETURN(int prefix_length, pdpi::DecimalStringToUint32(parts[1]),
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
absl::StatusOr<z3::expr> Ipv6PrefixLengthToZ3Mask(int prefix_length) {
  if (prefix_length < 0 || prefix_length > 128) {
    return gutil::InvalidArgumentErrorBuilder()
           << "invalid IPv6 prefix length: " << prefix_length;
  }
  if (prefix_length > 64) {
    return Bitvector<128>(0xFFFF'FFFF'FFFF'FFFFu).rotate_left(64) |
           Bitvector<128>(0xFFFF'FFFF'FFFF'FFFFu << (128 - prefix_length));
  } else {
    return Bitvector<128>(0xFFFF'FFFF'FFFF'FFFFu << (64 - prefix_length))
        .rotate_left(64);
  }
}

// TODO: Move to p4-symbolic utility library.
absl::StatusOr<z3::expr> Ipv6AddressToZ3Bitvector(
    const netaddr::Ipv6Address& ipv6) {
  std::bitset<128> bits = ipv6.ToBitset();
  uint64_t upper = (bits >> 64).to_ullong();
  uint64_t lower =
      (bits & std::bitset<128>(0xFFFF'FFFF'FFFF'FFFFu)).to_ullong();
  return Bitvector<128>(upper).rotate_left(64) | Bitvector<128>(lower);
}

absl::StatusOr<z3::expr> IsIpv6UnicastAddress(z3::expr ipv6_address) {
  z3::expr result = p4_symbolic::Z3Context().bool_val(false);
  ASSIGN_OR_RETURN(std::vector<Ipv6Range> ranges, GetUnicastIpv6Ranges());
  for (auto& range : ranges) {
    ASSIGN_OR_RETURN(z3::expr value, Ipv6AddressToZ3Bitvector(range.value));
    ASSIGN_OR_RETURN(z3::expr mask,
                     Ipv6PrefixLengthToZ3Mask(range.prefix_length));
    result = result || ((ipv6_address & mask) == value);
  }
  return result;
}
}  // namespace

// TODO: We need extra constraints to avoid generating packets
// the switch deams invalid and drops, such as "martian" packets.
// Ideally this switch behavior would be fully modeled in P4 instead, and this
// function would disappear.
absl::Status AddSanePacketConstraints(
    p4_symbolic::symbolic::SolverState& state) {
  ASSIGN_OR_RETURN(p4_symbolic::SaiFields ingress_fields,
                   p4_symbolic::GetSaiFields(state.context.ingress_headers));
  auto& ethernet = ingress_fields.headers.ethernet;
  auto& ipv4 = ingress_fields.headers.ipv4;
  auto& ipv6 = ingress_fields.headers.ipv6;

  // ======Ethernet constraints======
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
  state.solver->add((ethernet.src_addr & Bitvector<48>(0x03'00'00'00'00'00)) ==
                    Bitvector<48>(0x02'00'00'00'00'00));

  for (auto& mac_address : {ethernet.src_addr, ethernet.dst_addr}) {
    // Require key parts of the address to be nonzero to avoid corner cases.
    auto nonzero_masks = std::vector({
        Bitvector<48>(0x00'FF'FF'00'00'00),  // OUI
    });
    for (auto& nonzero_mask : nonzero_masks) {
      state.solver->add((mac_address & nonzero_mask) != 0);
    }
  }
  // Require source MAC and destination MAC to differ.
  state.solver->add(ethernet.src_addr != ethernet.dst_addr);

  // ======IPv4 constraints======
  // Avoid martian IP addresses.
  // https://tools.ietf.org/html/rfc1122#section-3.2.1.3
  state.solver->add((ipv4.src_addr & Bitvector<32>(0xFF'00'00'00)) != 0);
  // Src IP address cannot be 255.255.255.255 (broadcast).
  state.solver->add(ipv4.src_addr != Bitvector<32>(0xFF'FF'FF'FF));
  // Neither src nor dst IPv4 addresses can be 0.
  state.solver->add(ipv4.src_addr != Bitvector<32>(0));
  state.solver->add(ipv4.dst_addr != Bitvector<32>(0));
  // Neither src nor dst IPv4 addresses can be 127.0.0.1 (loopback).
  state.solver->add(ipv4.src_addr != Bitvector<32>(0x7F'00'00'01));
  state.solver->add(ipv4.dst_addr != Bitvector<32>(0x7F'00'00'01));

  // ======Ipv6 constraints======
  // Src IP address should be a unicast address.
  {
    ASSIGN_OR_RETURN(z3::expr constraint, IsIpv6UnicastAddress(ipv6.src_addr));
    state.solver->add(constraint);
  }
  // Neither src nor dst IPv6 addresses can be 0.
  state.solver->add(ipv6.src_addr != Bitvector<128>(0));
  state.solver->add(ipv6.dst_addr != Bitvector<128>(0));
  // Neither src nor dst IPv4 addresses can be ::1 (loopback).
  state.solver->add(ipv6.src_addr != Bitvector<128>(1));
  state.solver->add(ipv6.dst_addr != Bitvector<128>(1));

  return absl::OkStatus();
}

absl::StatusOr<z3::expr> IrValueToZ3Bitvector(const pdpi::IrValue& value,
                                              int bitwidth) {
  ASSIGN_OR_RETURN(const std::string bytes,
                   pdpi::IrValueToNormalizedByteString(value, bitwidth));
  const std::string hex_string = pdpi::ByteStringToHexString(bytes);
  return HexStringToZ3Bitvector(hex_string, bitwidth);
}

// The following functions return Z3 constraints corresponding to `field`
// matching the given pdpi::IrMatch value.
absl::StatusOr<z3::expr> GetFieldMatchConstraints(z3::expr field, int bitwidth,
                                                  const pdpi::IrValue& match) {
  ASSIGN_OR_RETURN(z3::expr value, IrValueToZ3Bitvector(match, bitwidth));
  return Eq(field, value);
}
absl::StatusOr<z3::expr> GetFieldMatchConstraints(
    z3::expr field, int bitwidth, const pdpi::IrMatch::IrLpmMatch& match) {
  ASSIGN_OR_RETURN(z3::expr value,
                   IrValueToZ3Bitvector(match.value(), bitwidth));
  return PrefixEq(field, value,
                  static_cast<unsigned int>(match.prefix_length()));
}
absl::StatusOr<z3::expr> GetFieldMatchConstraints(
    z3::expr field, int bitwidth, const pdpi::IrMatch::IrTernaryMatch& match) {
  ASSIGN_OR_RETURN(z3::expr value,
                   IrValueToZ3Bitvector(match.value(), bitwidth));
  ASSIGN_OR_RETURN(z3::expr mask, IrValueToZ3Bitvector(match.mask(), bitwidth));
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

// Extract the header field defition of a `field_ref` from the given P4
// `program`.
absl::StatusOr<p4_symbolic::ir::HeaderField> GetFieldDefinition(
    const P4Program& program, absl::string_view field_ref) {
  // Split the field reference into header and field names.
  std::vector<std::string> split = absl::StrSplit(field_ref, '.');
  if (split.size() != 2) {
    return absl::InvalidArgumentError(
        absl::Substitute("Expected <header>.<field> got '$0'", field_ref));
  }
  const std::string& header_name = split[0];
  const std::string& field_name = split[1];

  // Extract the header definition from the program.
  if (!program.headers().contains(header_name)) {
    return absl::InvalidArgumentError(
        absl::Substitute("Unexpected header instance'$0'", header_name));
  }
  const p4_symbolic::ir::HeaderType& header_def =
      program.headers().at(header_name);

  // Extract the field definition from the header definition.
  if (!header_def.fields().contains(field_name)) {
    return absl::InvalidArgumentError(absl::Substitute(
        "Unexpected field'$0' in header '$1'", field_name, header_name));
  }
  return header_def.fields().at(field_name);
}

absl::StatusOr<int> GetFieldBitwidth(
    absl::string_view field_name, const p4_symbolic::ir::P4Program& program) {
  if (absl::EndsWith(field_name, ".$valid$")) {
    return 1;
  } else {
    ASSIGN_OR_RETURN(const p4_symbolic::ir::HeaderField field_definition,
                     GetFieldDefinition(program, field_name));
    return field_definition.bitwidth();
  }
}

}  // namespace packet_synthesizer
}  // namespace p4_symbolic
