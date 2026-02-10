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
#ifndef PINS_P4_PDPI_PACKETLIB_PACKETLIB_H_
#define PINS_P4_PDPI_PACKETLIB_PACKETLIB_H_

#include <bitset>
#include <cstdint>
#include <optional>
#include <string>
#include <vector>

#include "absl/log/log.h"
#include "absl/numeric/bits.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_infra/p4_pdpi/string_encodings/hex_string.h"

namespace packetlib {

constexpr uint32_t kIpfixUdpDestPort = 4739; // 0x1283

// Parses the given packet. Parsing is a total function, and any aspect that
// cannot be parsed correctly will be put into `payload` of `Packet`.
//
// Even invalid packets will be parsed into the header structure of `Packet`
// when possible. For instance an invalid checksum will be parsed. However, not
// all invalid packets can be parsed into the header structure. Specifically, if
// trying to represent the packet would lose information, the function will
// instead not parse that header and put the data in `payload` instead. For
// example IPv4 packets with options is treated this way (since the library does
// not support options and thus has no place in `Ipv4Header` for options).
//
// Parsing starts with the given header (defaulting to Ethernet).
//
// Guarantees for `packet = ParsePacket(data)`:
// 1. Valid packets are valid:
//    `packet.reasons_invalid.empty()` implies `ValidatePacket(packet).ok()`.
// 2. Parsing is loss-less:
//    Running `serialized = RawSerializePacket(packet);` guarantees
//    `serialized.ok() && *serialized == data`.
// 3. If a header is supported by packetlib, it will be parsed. Partially
//    supported headers may not be parsed, but then `reason_not_fully_parsed`
//    will indicate what unsupported feature the packet uses, and the
//    unsupported header will appear uninterpreted in the payload.
Packet ParsePacket(absl::string_view input,
                   Header::HeaderCase first_header = Header::kEthernetHeader);

// Validates packets by checking that:
// 1. Headers appear in a valid order, and fields indicating the next header
//    match the actual next header for all supported header types.
// 2. Each field is specified, and of the correct format.
// 3. Computed fields have the right value.
// 4. The packet has the minimum size required by its headers.
// 5. The packet is non-empty (not uninitialized).
absl::Status ValidatePacket(const Packet &packet);

// Same as ValidatePacket, but returns a list of reasons why the packet isn't
// valid instead.
std::vector<std::string> PacketInvalidReasons(const Packet &packet);

// Seralizes a given packet. The packet may miss computed fields, which will be
// filled in automatically when missing (but not changed if they are present).
// Serialization succeeds iff `ValidatePacket(packet).ok()` after calling
// `PadPacketToMinimumSize(packet); UpdateMissingComputedFields(packet)`. An
// error status is returned otherwise.
absl::StatusOr<std::string> SerializePacket(Packet packet);

// Like the other `SerializePacket` overload, but takes in the `packet` in text
// proto format.
absl::StatusOr<std::string>
SerializePacket(absl::string_view packet_text_proto);

// Seralizes a given packet without checking header invariants. All fields must
// be present and use a valid value (according to ir::Format), but otherwise no
// requirements are made on the set of headers; they will just be serialized in
// order without checking, if computed fields are correct, header order is
// valid, etc.
absl::StatusOr<std::string> RawSerializePacket(const Packet &packet);

// Updates all computed fields that are missing. Computed fields that are
// already present are not modified. Returns true iff any changes where made.
// Fails if fields that are required for determining computed fields are missing
// or invalid.
absl::StatusOr<bool> UpdateMissingComputedFields(Packet &packet);

// Like `UpdateMissingComputedFields`, but also overwrites comuted fields
// that are already present.
absl::StatusOr<bool> UpdateAllComputedFields(Packet &packet);

// If the given packet must have a minimum size based on its headers (e.g., an
// Ethernet payload can be no smaller than 46 bytes), and if the packet size can
// be computed, appends the minimum number  of additional zeros needed to the
// payload and returns true. If the packet size cannot be computed, returns
// error status.
// If no padding is required, leaves the packet unmodified and returns false.
//
// Note: This function may invalidate computed fields (e.g., checksum and length
// fields) and should be called prior to `Update*ComputedFields`.
absl::StatusOr<bool> PadPacketToMinimumSize(Packet &packet);

// Pads a packet to certain size by appending zeros to the payload and return
// true. If the packet size is bigger than or equal to the target size,
// leaves the packet unmodified and returns false. If the packet size cannot be
// computed, returns error satus.
absl::StatusOr<bool> PadPacket(int num_bytes, Packet &packet);

// Returns the size of the given packet in bits, starting at the nth header and
// ignoring all headers before that. Works even when computed fields are
// missing.
// Returns error if
// - `start_header_index` is not in [0, packet.headers().size()], or
// - `packet.headers(i)` is uninitialized for i in
//   [start_header_index, packet.headers().size()]
absl::StatusOr<int> PacketSizeInBits(const Packet &packet,
                                     int start_header_index = 0);

// Like `PacketSizeInBits`, but returns size in bytes, or an error if the bit
// size is not divisible by 8.
absl::StatusOr<int> PacketSizeInBytes(const Packet &packet,
                                      int start_header_index = 0);

// Computes the 16-bit checksum of an IPv4 header. All fields must be set and
// valid except possibly the checksum, which is ignored.
absl::StatusOr<int> Ipv4HeaderChecksum(Ipv4Header header);

// Computes the 16-bit UDP checksum for the given `packet` and
// `udp_header_index`.
// The header at the given index must be a UDP header. All fields in all headers
// following the parent header must be set and valid except possibly the UDP
// checksum field, which is ignored. Returning nullopt means the value cannot be
// computed based on information in the packet (i.e. any value is allowed).
//
// NOTE: The nullopt case should not occur in the normal L4 UDP use case. It can
// appear when the UDP header is nested deeper inside a packet. For example when
// we are using tunnels (e.g. PSP).
absl::StatusOr<std::optional<int>> UdpHeaderChecksum(Packet packet,
                                                     int udp_header_index);
// Computes the 16-bit ICMP checksum for the given `packet` and
// `icmp_header_index`.
// The header at the given index must be an ICMP header, and it must be preceded
// by an IP header. All fields in all headers following that IP header must be
// set and valid except possibly the UDP checksum field, which is ignored.
absl::StatusOr<int> IcmpHeaderChecksum(Packet packet, int icmp_header_index);

// Computes the 16-bit GRE checksum for the given `packet` and
// `gre_header_index`. The header at the given index must be an GRE header. All
// fields in all headers following that GRE header must be set and valid except
// possibly the GRE checksum field, which is ignored.
absl::StatusOr<int> GreHeaderChecksum(Packet packet, int gre_header_index);

std::string HeaderCaseName(Header::HeaderCase header_case);

// Returns the Ethernet trailer of the given packet as a raw byte string. If
// there is no Ethernet trailer, returns the empty string. The Ethernet trailer
// is defined to be the suffix of the packet that is not upper protocol data,
// where "upper protocols" means ARP, IPv4, or IPv6 (see e.g.
// https://ask.wireshark.org/question/8809/what-is-the-trailer-in-the-ethernet-frame-and-why-is-the-fcs-incorrect/
// for more details).Returns an error if the packet does not start with an
// ethernet header or if there are no headers after the "lower protocol" headers
// (Ethernet/VLAN/CSIG).
absl::StatusOr<std::string> GetEthernetTrailer(const packetlib::Packet& packet);

// Helper functions to translate the header fields to hex string. It abstracts
// the bitwidth limitation away from the client and provides the validation that
// checks if the input data is truncated because its bit width exceeds the
// limitation.
std::string EtherType(uint32_t ether_type);
std::string VlanId(uint32_t vlan_id);
std::string IpVersion(uint32_t version);
std::string IpIhl(uint32_t ihl);
std::string IpDscp(uint32_t dscp);
std::string IpEcn(uint32_t ecn);
std::string IpTotalLength(uint32_t total_length);
std::string IpIdentification(uint32_t identification);
std::string IpFlags(uint32_t flag);
std::string IpFragmentOffset(uint32_t fragment_offset);
std::string IpTtl(uint32_t ttl);
std::string IpProtocol(uint32_t protocol);
std::string IpChecksum(uint32_t checksum);
std::string IpFlowLabel(uint32_t flow_label);
std::string IpPayloadLength(uint32_t payload_length);
std::string IpNextHeader(uint32_t next_header);
std::string IpHopLimit(uint32_t hop_limit);
std::string UdpPort(uint32_t udp_port);
std::string UdpChecksum(uint32_t checksum);
std::string UdpLength(uint32_t udp_length);
std::string TcpPort(uint32_t tcp_port);
std::string TcpSequenceNumber(uint32_t sequence_number);
std::string TcpAcknowledgementNumber(uint32_t ackowledgement_number);
std::string TcpDataOffset(uint32_t data_offset);
std::string TcpRestOfHeader(uint64_t rest_of_header);
std::string ArpType(uint32_t type);
std::string ArpLength(uint32_t length);
std::string ArpOperation(uint32_t operation);
std::string IcmpType(uint32_t type);
std::string IcmpCode(uint32_t code);
std::string IcmpChecksum(uint32_t checksum);
std::string IcmpRestOfHeader(uint32_t rest_of_header);
std::string GreChecksumPresent(uint32_t checksum_present);
std::string GreReserved0(uint32_t reserved0);
std::string GreVersion(uint32_t version);
std::string GreProtocolType(uint32_t protocol_type);
std::string GreChecksum(uint32_t checksum);
std::string GreReserved1(uint32_t reserved1);
std::string IpfixVersion(uint32_t version);
std::string IpfixLength(uint32_t length);
std::string IpfixExportTime(uint32_t exported_time);
std::string IpfixSequenceNumber(uint32_t sequence_number);
std::string IpfixObservationDomainId(uint32_t observation_domain_id);
std::string PsampTemplateId(uint32_t template_id);
std::string PsampObservationTime(uint64_t observation_time);
std::string PsampFlowset(uint32_t flowset);
std::string PsampNextHopIndex(uint32_t next_hop_index);
std::string PsampEpoch(uint32_t epoch);
std::string PsampIngressPort(uint32_t ingress_port);
std::string PsampEgressPort(uint32_t egress_port);
std::string PsampUserMetaField(uint32_t user_meta_field);
std::string PsampDlbId(uint32_t dlb_id);
// -- END OF PUBLIC INTERFACE --------------------------------------------------

template <int bit_limit>
std::string ValidateAndConvertToHexString(uint64_t input) {
  int bit_width = absl::bit_width(input);
  if (bit_width > bit_limit) {
    LOG(DFATAL)
        << "Input has been truncated because maximum allowable bitwidth "
           "for this field is "
        << bit_limit << " but input has " << bit_width << " bits: " << input;
  }

  return pdpi::BitsetToHexString(std::bitset<bit_limit>(input));
}

} // namespace packetlib

#endif // GOOGLE_P4_PDPI_PACKETLIB_PACKETLIB_H_
