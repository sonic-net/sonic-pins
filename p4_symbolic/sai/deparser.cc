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
#include "p4_symbolic/sai/deparser.h"

#include <stddef.h>

#include <bitset>
#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "gutil/status.h"
#include "p4_pdpi/string_encodings/bit_string.h"
#include "p4_symbolic/sai/fields.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/z3_util.h"
#include "z3++.h"

namespace p4_symbolic {

namespace {

template <size_t num_bits>
absl::StatusOr<std::bitset<num_bits>> EvalBitvector(const z3::expr& bv_expr,
                                                    const z3::model& model) {
  if (!bv_expr.is_bv() || bv_expr.get_sort().bv_size() != num_bits) {
    return gutil::InvalidArgumentErrorBuilder()
           << "expected bitvector of " << num_bits << " bits, but got "
           << bv_expr.get_sort() << ": " << bv_expr;
  }

  std::string value_with_prefix = model.eval(bv_expr, true).to_string();
  absl::string_view value = value_with_prefix;
  if (absl::ConsumePrefix(&value, "#x")) {
    return pdpi::HexStringToBitset<num_bits>(absl::StrCat("0x", value));
  }
  if (absl::ConsumePrefix(&value, "#b")) {
    return std::bitset<num_bits>(std::string(value));
  }
  return gutil::InvalidArgumentErrorBuilder()
         << "invalid Z3 bitvector value '" << value_with_prefix << "'";
}

template <size_t num_bits>
absl::Status Deparse(const z3::expr& field, const z3::model& model,
                     pdpi::BitString& result) {
  ASSIGN_OR_RETURN(std::bitset<num_bits> bits,
                   EvalZ3Bitvector<num_bits>(field, model));
  result.AppendBits(bits);
  return absl::OkStatus();
}

absl::Status Deparse(const SaiEthernet& header, const z3::model& model,
                     pdpi::BitString& result) {
  ASSIGN_OR_RETURN(bool valid, EvalZ3Bool(header.valid, model));
  if (valid) {
    RETURN_IF_ERROR(Deparse<48>(header.dst_addr, model, result));
    RETURN_IF_ERROR(Deparse<48>(header.src_addr, model, result));
    RETURN_IF_ERROR(Deparse<16>(header.ether_type, model, result));
  }
  return absl::OkStatus();
}

absl::Status Deparse(const SaiVlan& header, const z3::model& model,
                     pdpi::BitString& result) {
  ASSIGN_OR_RETURN(bool valid, EvalZ3Bool(header.valid, model));
  if (valid) {
    RETURN_IF_ERROR(Deparse<3>(header.priority_code_point, model, result));
    RETURN_IF_ERROR(Deparse<1>(header.drop_eligible_indicator, model, result));
    RETURN_IF_ERROR(Deparse<12>(header.vlan_id, model, result));
    RETURN_IF_ERROR(Deparse<16>(header.ether_type, model, result));
  }
  return absl::OkStatus();
}

absl::Status Deparse(const SaiIpv4& header, const z3::model& model,
                     pdpi::BitString& result) {
  ASSIGN_OR_RETURN(bool valid, EvalZ3Bool(header.valid, model));
  if (valid) {
    RETURN_IF_ERROR(Deparse<4>(header.version, model, result));
    RETURN_IF_ERROR(Deparse<4>(header.ihl, model, result));
    RETURN_IF_ERROR(Deparse<6>(header.dscp, model, result));
    RETURN_IF_ERROR(Deparse<2>(header.ecn, model, result));
    RETURN_IF_ERROR(Deparse<16>(header.total_len, model, result));
    RETURN_IF_ERROR(Deparse<16>(header.identification, model, result));
    RETURN_IF_ERROR(Deparse<1>(header.reserved, model, result));
    RETURN_IF_ERROR(Deparse<1>(header.do_not_fragment, model, result));
    RETURN_IF_ERROR(Deparse<1>(header.more_fragments, model, result));
    RETURN_IF_ERROR(Deparse<13>(header.frag_offset, model, result));
    RETURN_IF_ERROR(Deparse<8>(header.ttl, model, result));
    RETURN_IF_ERROR(Deparse<8>(header.protocol, model, result));
    RETURN_IF_ERROR(Deparse<16>(header.header_checksum, model, result));
    RETURN_IF_ERROR(Deparse<32>(header.src_addr, model, result));
    RETURN_IF_ERROR(Deparse<32>(header.dst_addr, model, result));
  }
  return absl::OkStatus();
}

absl::Status Deparse(const SaiIpv6& header, const z3::model& model,
                     pdpi::BitString& result) {
  ASSIGN_OR_RETURN(bool valid, EvalZ3Bool(header.valid, model));
  if (valid) {
    RETURN_IF_ERROR(Deparse<4>(header.version, model, result));
    RETURN_IF_ERROR(Deparse<6>(header.dscp, model, result));
    RETURN_IF_ERROR(Deparse<2>(header.ecn, model, result));
    RETURN_IF_ERROR(Deparse<20>(header.flow_label, model, result));
    RETURN_IF_ERROR(Deparse<16>(header.payload_length, model, result));
    RETURN_IF_ERROR(Deparse<8>(header.next_header, model, result));
    RETURN_IF_ERROR(Deparse<8>(header.hop_limit, model, result));
    RETURN_IF_ERROR(Deparse<128>(header.src_addr, model, result));
    RETURN_IF_ERROR(Deparse<128>(header.dst_addr, model, result));
  }
  return absl::OkStatus();
}

absl::Status Deparse(const SaiUdp& header, const z3::model& model,
                     pdpi::BitString& result) {
  ASSIGN_OR_RETURN(bool valid, EvalZ3Bool(header.valid, model));
  if (valid) {
    RETURN_IF_ERROR(Deparse<16>(header.src_port, model, result));
    RETURN_IF_ERROR(Deparse<16>(header.dst_port, model, result));
    RETURN_IF_ERROR(Deparse<16>(header.hdr_length, model, result));
    RETURN_IF_ERROR(Deparse<16>(header.checksum, model, result));
  }
  return absl::OkStatus();
}

absl::Status Deparse(const SaiTcp& header, const z3::model& model,
                     pdpi::BitString& result) {
  ASSIGN_OR_RETURN(bool valid, EvalZ3Bool(header.valid, model));
  if (valid) {
    RETURN_IF_ERROR(Deparse<16>(header.src_port, model, result));
    RETURN_IF_ERROR(Deparse<16>(header.dst_port, model, result));
    RETURN_IF_ERROR(Deparse<32>(header.seq_no, model, result));
    RETURN_IF_ERROR(Deparse<32>(header.ack_no, model, result));
    RETURN_IF_ERROR(Deparse<4>(header.data_offset, model, result));
    RETURN_IF_ERROR(Deparse<4>(header.res, model, result));
    RETURN_IF_ERROR(Deparse<8>(header.flags, model, result));
    RETURN_IF_ERROR(Deparse<16>(header.window, model, result));
    RETURN_IF_ERROR(Deparse<16>(header.checksum, model, result));
    RETURN_IF_ERROR(Deparse<16>(header.urgent_ptr, model, result));
  }
  return absl::OkStatus();
}

absl::Status Deparse(const SaiIcmp& header, const z3::model& model,
                     pdpi::BitString& result) {
  ASSIGN_OR_RETURN(bool valid, EvalZ3Bool(header.valid, model));
  if (valid) {
    RETURN_IF_ERROR(Deparse<8>(header.type, model, result));
    RETURN_IF_ERROR(Deparse<8>(header.code, model, result));
    RETURN_IF_ERROR(Deparse<16>(header.checksum, model, result));
    // Rest of header. Not parsed by P4 SAI, so the best we can do is to always
    // set it to zero.
    result.AppendBits(std::bitset<32>(0));
  }
  return absl::OkStatus();
}

absl::Status Deparse(const SaiArp& header, const z3::model& model,
                     pdpi::BitString& result) {
  ASSIGN_OR_RETURN(bool valid, EvalZ3Bool(header.valid, model));
  if (valid) {
    RETURN_IF_ERROR(Deparse<16>(header.hw_type, model, result));
    RETURN_IF_ERROR(Deparse<16>(header.proto_type, model, result));
    RETURN_IF_ERROR(Deparse<8>(header.hw_addr_len, model, result));
    RETURN_IF_ERROR(Deparse<8>(header.proto_addr_len, model, result));
    RETURN_IF_ERROR(Deparse<16>(header.opcode, model, result));
    RETURN_IF_ERROR(Deparse<48>(header.sender_hw_addr, model, result));
    RETURN_IF_ERROR(Deparse<32>(header.sender_proto_addr, model, result));
    RETURN_IF_ERROR(Deparse<48>(header.target_hw_addr, model, result));
    RETURN_IF_ERROR(Deparse<32>(header.target_proto_addr, model, result));
  }
  return absl::OkStatus();
}

absl::Status Deparse(const SaiGre& header, const z3::model& model,
                     pdpi::BitString& result) {
  ASSIGN_OR_RETURN(bool valid, EvalZ3Bool(header.valid, model));
  if (valid) {
    RETURN_IF_ERROR(Deparse<1>(header.checksum_present, model, result));
    RETURN_IF_ERROR(Deparse<1>(header.routing_present, model, result));
    RETURN_IF_ERROR(Deparse<1>(header.key_present, model, result));
    RETURN_IF_ERROR(Deparse<1>(header.sequence_present, model, result));
    RETURN_IF_ERROR(Deparse<1>(header.strict_source_route, model, result));
    RETURN_IF_ERROR(Deparse<3>(header.recursion_control, model, result));
    RETURN_IF_ERROR(Deparse<1>(header.acknowledgement_present, model, result));
    RETURN_IF_ERROR(Deparse<4>(header.flags, model, result));
    RETURN_IF_ERROR(Deparse<3>(header.version, model, result));
    RETURN_IF_ERROR(Deparse<16>(header.protocol, model, result));
  }
  return absl::OkStatus();
}

absl::Status Deparse(const SaiPacketIn& header, const z3::model& model,
                     pdpi::BitString& result) {
  ASSIGN_OR_RETURN(bool valid, EvalZ3Bool(header.valid, model));
  if (valid) {
    RETURN_IF_ERROR(Deparse<9>(header.ingress_port, model, result));
    RETURN_IF_ERROR(Deparse<9>(header.target_egress_port, model, result));
    RETURN_IF_ERROR(Deparse<6>(header.unused_pad, model, result));
  }
  return absl::OkStatus();
}

}  // namespace

absl::StatusOr<std::string> SaiDeparser(
    const symbolic::SymbolicPerPacketState& packet, const z3::model& model) {
  ASSIGN_OR_RETURN(SaiFields fields, GetSaiFields(packet));
  return SaiDeparser(fields, model);
}

absl::StatusOr<std::string> SaiDeparser(const SaiFields& packet,
                                        const z3::model& model) {
  pdpi::BitString result;
  // TODO: Make unconditional when we no longer need
  // backwards-compatibility.
  if (packet.headers.packet_in.has_value()) {
    RETURN_IF_ERROR(Deparse(packet.headers.packet_in.value(), model, result));
  }
  RETURN_IF_ERROR(Deparse(packet.headers.erspan_ethernet, model, result));
  RETURN_IF_ERROR(Deparse(packet.headers.erspan_ipv4, model, result));
  RETURN_IF_ERROR(Deparse(packet.headers.erspan_gre, model, result));
  RETURN_IF_ERROR(Deparse(packet.headers.ethernet, model, result));
  // TODO: Make unconditional when we no longer need
  // backwards-compatibility.
  if (packet.headers.vlan.has_value()) {
    RETURN_IF_ERROR(Deparse(*packet.headers.vlan, model, result));
  }
  RETURN_IF_ERROR(Deparse(packet.headers.tunnel_encap_ipv6, model, result));
  RETURN_IF_ERROR(Deparse(packet.headers.tunnel_encap_gre, model, result));
  RETURN_IF_ERROR(Deparse(packet.headers.ipv4, model, result));
  RETURN_IF_ERROR(Deparse(packet.headers.ipv6, model, result));
  RETURN_IF_ERROR(Deparse(packet.headers.udp, model, result));
  RETURN_IF_ERROR(Deparse(packet.headers.tcp, model, result));
  RETURN_IF_ERROR(Deparse(packet.headers.icmp, model, result));
  RETURN_IF_ERROR(Deparse(packet.headers.arp, model, result));
  ASSIGN_OR_RETURN(std::string bytes, result.ToByteString());
  return bytes;
}

}  // namespace p4_symbolic
