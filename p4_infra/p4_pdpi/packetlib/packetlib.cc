// Copyright 2025 Google LLC
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

#include "p4_infra/p4_pdpi/packetlib/packetlib.h"

#include <algorithm>
#include <bitset>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "absl/types/span.h"
#include "absl/types/variant.h"
#include "gutil/gutil/overload.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status.h"
#include "p4_infra/p4_pdpi/netaddr/ipv4_address.h"
#include "p4_infra/p4_pdpi/netaddr/ipv6_address.h"
#include "p4_infra/p4_pdpi/netaddr/mac_address.h"
#include "p4_infra/p4_pdpi/packetlib/bit_widths.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_infra/p4_pdpi/string_encodings/bit_string.h"
#include "p4_infra/p4_pdpi/string_encodings/hex_string.h"

namespace packetlib {

using ::netaddr::Ipv4Address;
using ::netaddr::Ipv6Address;
using ::netaddr::MacAddress;

namespace {

// -- Determining the header following a given header  -------------------------

// Indicates that a header should follow the current header, but that that
// header is unsupported by packetlib.
struct UnsupportedNextHeader {
  std::string reason;
};

// Encodes header, if any, that should follow the current header.
using NextHeader = absl::variant<
    // A supported next header, or no next header (encoded as HEADER_NOT_SET) if
    // the previous header was the final one before the payload.
    Header::HeaderCase,
    // An unsupported next header.
    UnsupportedNextHeader>;

absl::StatusOr<NextHeader> GetNextHeaderForEtherType(
    absl::string_view header_name, absl::string_view ethertype_hexstring) {
  ASSIGN_OR_RETURN(int ethertype, pdpi::HexStringToInt(ethertype_hexstring),
                   _.SetCode(absl::StatusCode::kInternal).SetPrepend()
                       << "unable to parse ethertype: ");
  // See https://en.wikipedia.org/wiki/EtherType.
  if (ethertype <= 1535) return Header::HEADER_NOT_SET;
  if (ethertype == 0x0800) return Header::kIpv4Header;
  if (ethertype == 0x86dd) return Header::kIpv6Header;
  if (ethertype == 0x0806) return Header::kArpHeader;
  if (ethertype == 0x8100) return Header::kVlanHeader;
  return UnsupportedNextHeader{
      .reason = absl::StrFormat("%s.ethertype %s: unsupported", header_name,
                                ethertype_hexstring)};
}

absl::StatusOr<NextHeader> GetNextHeader(const EthernetHeader& header) {
  return GetNextHeaderForEtherType("ethernet_header", header.ethertype());
}
absl::StatusOr<NextHeader> GetNextHeader(const VlanHeader& header) {
  return GetNextHeaderForEtherType("vlan_header", header.ethertype());
}
absl::StatusOr<NextHeader> GetNextHeader(const GreHeader& header) {
  return GetNextHeaderForEtherType("gre_header", header.protocol_type());
}
absl::StatusOr<NextHeader> GetNextHeader(
    const SaiP4BMv2PacketInHeader& header) {
  return Header::kEthernetHeader;
}
absl::StatusOr<NextHeader> GetNextHeader(const Ipv4Header& header) {
  if (header.protocol() == "0x04") return Header::kIpv4Header;
  if (header.protocol() == "0x06") return Header::kTcpHeader;
  if (header.protocol() == "0x11") return Header::kUdpHeader;
  if (header.protocol() == "0x01") return Header::kIcmpHeader;
  if (header.protocol() == "0x29") return Header::kIpv6Header;
  if (header.protocol() == "0x2f") return Header::kGreHeader;
  // The following IP protocol numbers are "reserved for experimentation",
  // meaning the bits after the L3 header are arbitrary.
  if (header.protocol() == "0xfd") return Header::HEADER_NOT_SET;
  if (header.protocol() == "0xfe") return Header::HEADER_NOT_SET;
  return UnsupportedNextHeader{
      .reason = absl::StrFormat("ipv4_header.protocol %s: unsupported",
                                header.protocol())};
}
absl::StatusOr<NextHeader> GetNextHeader(const Ipv6Header& header) {
  if (header.next_header() == "0x00") return Header::kHopByHopOptionsHeader;
  if (header.next_header() == "0x04") return Header::kIpv4Header;
  if (header.next_header() == "0x06") return Header::kTcpHeader;
  if (header.next_header() == "0x11") return Header::kUdpHeader;
  if (header.next_header() == "0x3a") return Header::kIcmpHeader;
  if (header.next_header() == "0x29") return Header::kIpv6Header;
  if (header.next_header() == "0x2f") return Header::kGreHeader;
  // The following IP protocol numbers are "reserved for experimentation",
  // meaning the bits after the L3 header are arbitrary.
  if (header.next_header() == "0xfd") return Header::HEADER_NOT_SET;
  if (header.next_header() == "0xfe") return Header::HEADER_NOT_SET;
  return UnsupportedNextHeader{
      .reason = absl::StrFormat("ipv6_header.next_header %s: unsupported",
                                header.next_header())};
}
absl::StatusOr<NextHeader> GetNextHeader(const HopByHopOptionsHeader& header) {
  if (header.header_extension_length() != "0x00")
    return UnsupportedNextHeader{
        .reason = "hop_by_hop_options_header.header_extension_length is not 0.",
    };
  if (header.next_header() == "0x04") return Header::kIpv4Header;
  if (header.next_header() == "0x06") return Header::kTcpHeader;
  if (header.next_header() == "0x11") return Header::kUdpHeader;
  if (header.next_header() == "0x3a") return Header::kIcmpHeader;
  if (header.next_header() == "0x29") return Header::kIpv6Header;
  if (header.next_header() == "0x2f") return Header::kGreHeader;
  // The following IP protocol numbers are "reserved for experimentation",
  // meaning the bits after the L3 header are arbitrary.
  if (header.next_header() == "0xfd") return Header::HEADER_NOT_SET;
  if (header.next_header() == "0xfe") return Header::HEADER_NOT_SET;
  return UnsupportedNextHeader{
      .reason = absl::StrFormat(
          "hop_by_hop_options_header.next_header %s: unsupported",
          header.next_header())};
}
absl::StatusOr<NextHeader> GetNextHeader(const UdpHeader& header) {
  ASSIGN_OR_RETURN(auto dest_port,
                   pdpi::HexStringToInt32(header.destination_port()));
  if (dest_port == kIpfixUdpDestPort) return Header::kIpfixHeader;
  if (dest_port == 1000) return Header::kPspHeader;
  return Header::HEADER_NOT_SET;
}
absl::StatusOr<NextHeader> GetNextHeader(const TcpHeader& header) {
  return Header::HEADER_NOT_SET;
}
absl::StatusOr<NextHeader> GetNextHeader(const ArpHeader& header) {
  return Header::HEADER_NOT_SET;
}
absl::StatusOr<NextHeader> GetNextHeader(const IcmpHeader& header) {
  return Header::HEADER_NOT_SET;
}
absl::StatusOr<NextHeader> GetNextHeader(const IpfixHeader& header) {
  return Header::kPsampHeader;
}
absl::StatusOr<NextHeader> GetNextHeader(const PsampHeader& header) {
  return Header::HEADER_NOT_SET;
}
absl::StatusOr<NextHeader> GetNextHeader(const PspHeader& header) {
  if (header.virtualization_cookie_present() == "0x1") {
    return UnsupportedNextHeader{
        .reason = "psp_header virtualization_cookie is not supported.",
    };
  }
  // Only parse the UDP header if we have enough unencrypted bits.
  ASSIGN_OR_RETURN(int crypt_offset,
                   pdpi::HexStringToInt32(header.crypt_offset()));
  if (header.next_header() == "0x11" && crypt_offset * 32 >= kUdpHeaderBitwidth)
    return Header::kUdpHeader;
  return Header::HEADER_NOT_SET;
}
absl::StatusOr<NextHeader> GetNextHeader(const Header& header) {
  switch (header.header_case()) {
    case Header::kEthernetHeader:
      return GetNextHeader(header.ethernet_header());
    case Header::kIpv4Header:
      return GetNextHeader(header.ipv4_header());
    case Header::kIpv6Header:
      return GetNextHeader(header.ipv6_header());
    case Header::kHopByHopOptionsHeader:
      return GetNextHeader(header.hop_by_hop_options_header());
    case Header::kUdpHeader:
      return GetNextHeader(header.udp_header());
    case Header::kTcpHeader:
      return GetNextHeader(header.tcp_header());
    case Header::kArpHeader:
      return GetNextHeader(header.arp_header());
    case Header::kIcmpHeader:
      return GetNextHeader(header.icmp_header());
    case Header::kVlanHeader:
      return GetNextHeader(header.vlan_header());
    case Header::kGreHeader:
      return GetNextHeader(header.gre_header());
    case Header::kSaiP4Bmv2PacketInHeader:
      return GetNextHeader(header.sai_p4_bmv2_packet_in_header());
    case Header::kIpfixHeader:
      return GetNextHeader(header.ipfix_header());
    case Header::kPsampHeader:
      return GetNextHeader(header.psamp_header());
    case Header::kPspHeader:
      return GetNextHeader(header.psp_header());
    case Header::HEADER_NOT_SET:
      return Header::HEADER_NOT_SET;
  }
  return Header::HEADER_NOT_SET;
}

// ---- Parsing ----------------------------------------------------------------

// Parser helper functions.  Assumes that there are enough bits left in data.
std::string ParseMacAddress(pdpi::BitString& data) {
  if (auto mac = data.ConsumeMacAddress(); mac.ok()) {
    return mac->ToString();
  } else {
    LOG(DFATAL) << "Size was already checked, should never fail; "
                << mac.status();
    return "INTERNAL ERROR";
  }
}
std::string ParseIpv4Address(pdpi::BitString& data) {
  if (auto ip = data.ConsumeIpv4Address(); ip.ok()) {
    return ip->ToString();
  } else {
    LOG(DFATAL) << "Size was already checked, should never fail; "
                << ip.status();
    return "INTERNAL ERROR";
  }
}
std::string ParseIpv6Address(pdpi::BitString& data) {
  if (auto ip = data.ConsumeIpv6Address(); ip.ok()) {
    return ip->ToString();
  } else {
    LOG(DFATAL) << "Size was already checked, should never fail; "
                << ip.status();
    return "INTERNAL ERROR";
  }
}
std::string ParseBits(pdpi::BitString& data, int num_bits) {
  if (auto bits = data.ConsumeHexString(num_bits); bits.ok()) {
    return *bits;
  } else {
    LOG(DFATAL) << "Size was already checked, should never fail; "
                << bits.status();
    return "INTERNAL ERROR";
  }
}

// Parse and return an Ethernet header, or return error if the packet is too
// small.
absl::StatusOr<EthernetHeader> ParseEthernetHeader(pdpi::BitString& data) {
  if (data.size() < kEthernetHeaderBitwidth) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Packet is too short to parse an Ethernet header next. Only "
           << data.size() << " bits left, need at least "
           << kEthernetHeaderBitwidth << ".";
  }

  EthernetHeader header;
  header.set_ethernet_destination(ParseMacAddress(data));
  header.set_ethernet_source(ParseMacAddress(data));
  header.set_ethertype(ParseBits(data, kEthernetEthertypeBitwidth));
  return header;
}

// Parse and return an IPv4 header, or return error if the packet is too small.
absl::StatusOr<Ipv4Header> ParseIpv4Header(pdpi::BitString& data) {
  if (data.size() < kStandardIpv4HeaderBitwidth) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Packet is too short to parse an IPv4 header next. Only "
           << data.size() << " bits left, need at least "
           << kStandardIpv4HeaderBitwidth << ".";
  }

  Ipv4Header header;
  header.set_version(ParseBits(data, kIpVersionBitwidth));
  header.set_ihl(ParseBits(data, kIpIhlBitwidth));
  header.set_dscp(ParseBits(data, kIpDscpBitwidth));
  header.set_ecn(ParseBits(data, kIpEcnBitwidth));
  header.set_total_length(ParseBits(data, kIpTotalLengthBitwidth));
  header.set_identification(ParseBits(data, kIpIdentificationBitwidth));
  header.set_flags(ParseBits(data, kIpFlagsBitwidth));
  header.set_fragment_offset(ParseBits(data, kIpFragmentOffsetBitwidth));
  header.set_ttl(ParseBits(data, kIpTtlBitwidth));
  header.set_protocol(ParseBits(data, kIpProtocolBitwidth));
  header.set_checksum(ParseBits(data, kIpChecksumBitwidth));
  header.set_ipv4_source(ParseIpv4Address(data));
  header.set_ipv4_destination(ParseIpv4Address(data));

  // Parse suffix/options.
  absl::StatusOr<int> ihl = pdpi::HexStringToInt(header.ihl());
  if (!ihl.ok()) {
    LOG(DFATAL) << "SHOULD NEVER HAPPEN: IHL badly formatted: " << ihl.status();
    // Don't return error status so parsing is lossless despite error.
    // The packet will be invalid, but this will be caught by validity checking.
  } else if (*ihl > 5) {
    int options_bit_width = 32 * (*ihl - 5);
    // If the packet ends prematurely, we still parse what's there to maintain
    // the property that parsing is lossless. The result is an invalid packet,
    // since the IHL and the options length will be inconsistent, but this will
    // be caught by the validity check.
    if (data.size() < options_bit_width) {
      options_bit_width = data.size();
    }
    header.set_uninterpreted_options(ParseBits(data, options_bit_width));
  }
  return header;
}

// Parse and return an IPv6 header, or return error if the packet is too small.
absl::StatusOr<Ipv6Header> ParseIpv6Header(pdpi::BitString& data) {
  if (data.size() < kIpv6HeaderBitwidth) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Packet is too short to parse an IPv6 header next. Only "
           << data.size() << " bits left, need at least " << kIpv6HeaderBitwidth
           << ".";
  }

  Ipv6Header header;
  header.set_version(ParseBits(data, kIpVersionBitwidth));
  header.set_dscp(ParseBits(data, kIpDscpBitwidth));
  header.set_ecn(ParseBits(data, kIpEcnBitwidth));
  header.set_flow_label(ParseBits(data, kIpFlowLabelBitwidth));
  header.set_payload_length(ParseBits(data, kIpPayloadLengthBitwidth));
  header.set_next_header(ParseBits(data, kIpNextHeaderBitwidth));
  header.set_hop_limit(ParseBits(data, kIpHopLimitBitwidth));
  header.set_ipv6_source(ParseIpv6Address(data));
  header.set_ipv6_destination(ParseIpv6Address(data));
  return header;
}

// Parse and return a hop-by-hop options header, or return error if the packet
// is too small.
absl::StatusOr<HopByHopOptionsHeader> ParseHopByHopOptionsHeader(
    pdpi::BitString& data) {
  if (data.size() < kMinHopByHopOptionsHeaderBitwidth) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Packet is too short to parse a hop-by-hop options header next. "
              "Only "
           << data.size() << " bits left, need at least "
           << kMinHopByHopOptionsHeaderBitwidth << ".";
  }

  HopByHopOptionsHeader header;
  header.set_next_header(ParseBits(data, kHopByHopNextHeaderBitwidth));
  header.set_header_extension_length(
      ParseBits(data, kHopByHopHeaderExtensionLengthBitwidth));
  header.set_options_and_padding(
      ParseBits(data, kHopByHopOptionsAndPaddingBitwidth));
  return header;
}

// Parse a UDP header, or return error if the packet is too small.
absl::StatusOr<UdpHeader> ParseUdpHeader(pdpi::BitString& data) {
  if (data.size() < kUdpHeaderBitwidth) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Packet is too short to parse an UDP header next. Only "
           << data.size() << " bits left, need at least " << kUdpHeaderBitwidth
           << ".";
  }

  UdpHeader header;
  header.set_source_port(ParseBits(data, kUdpPortBitwidth));
  header.set_destination_port(ParseBits(data, kUdpPortBitwidth));
  header.set_length(ParseBits(data, kUdpLengthBitwidth));
  header.set_checksum(ParseBits(data, kUdpChecksumBitwidth));
  return header;
}

// Parse a TCP header prefix, or return error if the packet is too small.
absl::StatusOr<TcpHeader> ParseTcpHeader(pdpi::BitString& data) {
  if (data.size() < kStandardTcpHeaderBitwidth) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Packet is too short to parse a TCP header next. Only "
           << data.size() << " bits left, need at least "
           << kStandardTcpHeaderBitwidth << ".";
  }

  TcpHeader header;
  header.set_source_port(ParseBits(data, kTcpPortBitwidth));
  header.set_destination_port(ParseBits(data, kTcpPortBitwidth));
  header.set_sequence_number(ParseBits(data, kTcpSequenceNumberBitwidth));
  header.set_acknowledgement_number(
      ParseBits(data, kTcpAcknowledgementNumberBitwidth));
  header.set_data_offset(ParseBits(data, kTcpDataOffsetBitwidth));
  header.set_rest_of_header(ParseBits(data, kTcpRestOfHeaderBitwidth));

  // Parse suffix/options.
  absl::StatusOr<int> offset = pdpi::HexStringToInt(header.data_offset());
  if (!offset.ok()) {
    LOG(DFATAL) << "SHOULD NEVER HAPPEN: data_offset badly formatted: "
                << offset.status();
    // Don't return error status so parsing is lossless despite error.
    // The packet will be invalid, but this will be caught by validity checking.
  } else if (*offset > 5) {
    int options_bit_width = 32 * (*offset - 5);
    // If the packet ends prematurely, we still parse what's there to maintain
    // the property that parsing is lossless. The result is an invalid packet,
    // since the IHL and the options length will be inconsistent, but this will
    // be caught by the validity check.
    if (data.size() < options_bit_width) {
      options_bit_width = data.size();
    }
    header.set_uninterpreted_options(ParseBits(data, options_bit_width));
  }
  return header;
}

// Parse an ARP header, or return error if the packet is too small.
absl::StatusOr<ArpHeader> ParseArpHeader(pdpi::BitString& data) {
  if (data.size() < kArpHeaderBitwidth) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Packet is too short to parse an ARP header next. Only "
           << data.size() << " bits left, need at least " << kArpHeaderBitwidth
           << ".";
  }

  ArpHeader header;
  header.set_hardware_type(ParseBits(data, kArpTypeBitwidth));
  header.set_protocol_type(ParseBits(data, kArpTypeBitwidth));
  header.set_hardware_length(ParseBits(data, kArpLengthBitwidth));
  header.set_protocol_length(ParseBits(data, kArpLengthBitwidth));
  header.set_operation(ParseBits(data, kArpOperationBitwidth));
  header.set_sender_hardware_address(ParseMacAddress(data));
  header.set_sender_protocol_address(ParseIpv4Address(data));
  header.set_target_hardware_address(ParseMacAddress(data));
  header.set_target_protocol_address(ParseIpv4Address(data));
  return header;
}

// Parse an ICMP header, or return error if the packet is too small.
absl::StatusOr<IcmpHeader> ParseIcmpHeader(pdpi::BitString& data) {
  if (data.size() < kIcmpHeaderBitwidth) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Packet is too short to parse an ICMP header next. Only "
           << data.size() << " bits left, need at least " << kIcmpHeaderBitwidth
           << ".";
  }

  IcmpHeader header;
  header.set_type(ParseBits(data, kIcmpTypeBitwidth));
  header.set_code(ParseBits(data, kIcmpCodeBitwidth));
  header.set_checksum(ParseBits(data, kIcmpChecksumBitwidth));
  header.set_rest_of_header(ParseBits(data, kIcmpRestOfHeaderBitwidth));
  return header;
}

// Parse a VLAN header, or return error if the packet is too small.
absl::StatusOr<VlanHeader> ParseVlanHeader(pdpi::BitString& data) {
  if (data.size() < kVlanHeaderBitwidth) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Packet is too short to parse a VLAN header next. Only "
           << data.size() << " bits left, need at least " << kVlanHeaderBitwidth
           << ".";
  }

  VlanHeader header;
  header.set_priority_code_point(
      ParseBits(data, kVlanPriorityCodePointBitwidth));
  header.set_drop_eligible_indicator(
      ParseBits(data, kVlanDropEligibilityIndicatorBitwidth));
  header.set_vlan_identifier(ParseBits(data, kVlanVlanIdentifierBitwidth));
  header.set_ethertype(ParseBits(data, kVlanEthertypeBitwidth));
  return header;
}

// Parse a GRE header, or return error if the packet is too small.
absl::StatusOr<GreHeader> ParseGreHeader(pdpi::BitString& data) {
  int size = kRfc2784GreHeaderWithoutOptionalsBitwidth;

  if (data.size() < size) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Packet is too short to parse a GRE header next. Only "
           << data.size() << " bits left, need at least " << size << ".";
  }

  ASSIGN_OR_RETURN(std::string checksum_present,
                   data.PeekHexString(kGreChecksumPresentBitwidth));

  if (checksum_present == "0x1") {
    size += kGreChecksumBitwidth + kGreReserved1Bitwidth;

    if (data.size() < size) {
      return gutil::InvalidArgumentErrorBuilder()
             << "Packet is too short to parse a GRE header with optional "
                "fields. "
                "Only "
             << data.size() << " bits left, need at least " << size << ".";
    }
  }

  GreHeader header;
  header.set_checksum_present(ParseBits(data, kGreChecksumPresentBitwidth));
  header.set_reserved0(ParseBits(data, kGreReserved0Bitwidth));
  header.set_version(ParseBits(data, kGreVersionBitwidth));
  header.set_protocol_type(ParseBits(data, kGreProtocolTypeBitwidth));

  // Parse optional checksum and reserved1 fields.
  if (checksum_present == "0x1") {
    header.set_checksum(
        ParseBits(data, std::min(data.size(), kGreChecksumBitwidth)));
    header.set_reserved1(
        ParseBits(data, std::min(data.size(), kGreReserved1Bitwidth)));
  }

  return header;
}

// Parse a SAI P4 BMv2 packet_in header, or return error if the packet is too
// small.
absl::StatusOr<SaiP4BMv2PacketInHeader> ParseSaiP4BMv2PacketInHeader(
    pdpi::BitString& data) {
  if (data.size() < kSaiP4BMv2PacketInHeaderBitwidth) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Packet is too short to parse a SAI P4 BMv2 packet_in header "
              "next. Only "
           << data.size() << " bits left, need at least "
           << kSaiP4BMv2PacketInHeaderBitwidth << ".";
  }

  SaiP4BMv2PacketInHeader header;
  header.set_ingress_port(
      ParseBits(data, kSaiP4BMv2PacketInIngressPortBitwidth));
  header.set_target_egress_port(
      ParseBits(data, kSaiP4BMv2PacketInTargetEgressPortBitwidth));
  header.set_unused_pad(ParseBits(data, kSaiP4BMv2PacketInUnusedPadBitwidth));
  return header;
}

absl::StatusOr<IpfixHeader> ParseIpfixHeader(pdpi::BitString& data) {
  if (data.size() < kIpfixHeaderBitwidth) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Packet is too short to parse an IPFIX header next. Only "
           << data.size() << " bits left, need at least "
           << kIpfixHeaderBitwidth << ".";
  }

  IpfixHeader header;
  header.set_version(ParseBits(data, kIpfixVersionBitwidth));
  header.set_length(ParseBits(data, kIpfixLengthBitwidth));
  header.set_export_time(ParseBits(data, kIpfixExportTimeBitwidth));
  header.set_sequence_number(ParseBits(data, kIpfixSequenceNumberBitwidth));
  header.set_observation_domain_id(
      ParseBits(data, kIpfixObservationDomainIdBitwidth));
  return header;
}

absl::StatusOr<PsampHeader> ParsePsampHeader(pdpi::BitString& data) {
  if (data.size() < kPsampHeaderBitwidth) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Packet is too short to parse a PSAMP header next. Only "
           << data.size() << " bits left, need at least "
           << kPsampHeaderBitwidth << ".";
  }
  PsampHeader header;

  header.set_template_id(ParseBits(data, kPsampTemplateIdBitwidth));
  header.set_length(ParseBits(data, kPsampLengthBitwidth));
  header.set_observation_time(ParseBits(data, kPsampObservationTimeBitwidth));
  header.set_flowset(ParseBits(data, kPsampFlowsetBitwidth));
  header.set_next_hop_index(ParseBits(data, kPsampNextHopIndexBitwidth));
  header.set_epoch(ParseBits(data, kPsampEpochBitwidth));
  header.set_ingress_port(ParseBits(data, kPsampIngressPortBitwidth));
  header.set_egress_port(ParseBits(data, kPsampEgressPortBitwidth));
  header.set_user_meta_field(ParseBits(data, kPsampUserMetaFieldBitwidth));
  header.set_dlb_id(ParseBits(data, kPsampDlbIdBitwidth));
  header.set_variable_length(ParseBits(data, kPsampVariableLengthBitwidth));
  header.set_packet_sampled_length(
      ParseBits(data, kPsampPacketSampledLengthBitwidth));
  return header;
}

absl::StatusOr<PspHeader> ParsePspHeader(pdpi::BitString& data) {
  if (data.size() < kPspHeaderBitwidth) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Packet is too short to parse a PSP header next. Only "
           << data.size() << " bits left, need at least " << kPspHeaderBitwidth
           << ".";
  }
  PspHeader header;

  header.set_next_header(ParseBits(data, kPspNextHeaderBitwidth));
  header.set_header_ext_length(ParseBits(data, kPspHeaderExtLengthBitwidth));
  header.set_reserved0(ParseBits(data, kPspReserved0Bitwidth));
  header.set_crypt_offset(ParseBits(data, kPspCryptOffsetBitwidth));
  header.set_sample_bit(ParseBits(data, kPspSampleBitwidth));
  header.set_drop_bit(ParseBits(data, kPspDropBitwidth));
  header.set_version(ParseBits(data, kPspVersionBitwidth));
  header.set_virtualization_cookie_present(
      ParseBits(data, kPspVirtualizationCookieBitwidth));
  header.set_reserved1(ParseBits(data, kPspReserved1Bitwidth));
  header.set_security_parameters_index(
      ParseBits(data, kPspSecurityParametersIndexBitwidth));
  header.set_initialization_vector(
      ParseBits(data, kPspInitializationVectorBitwidth));

  return header;
}

absl::StatusOr<Header> ParseHeader(Header::HeaderCase header_case,
                                   pdpi::BitString& data) {
  Header result;
  switch (header_case) {
    case Header::kEthernetHeader: {
      ASSIGN_OR_RETURN(*result.mutable_ethernet_header(),
                       ParseEthernetHeader(data));
      return result;
    }
    case Header::kIpv4Header: {
      ASSIGN_OR_RETURN(*result.mutable_ipv4_header(), ParseIpv4Header(data));
      return result;
    }
    case Header::kIpv6Header: {
      ASSIGN_OR_RETURN(*result.mutable_ipv6_header(), ParseIpv6Header(data));
      return result;
    }
    case Header::kHopByHopOptionsHeader: {
      ASSIGN_OR_RETURN(*result.mutable_hop_by_hop_options_header(),
                       ParseHopByHopOptionsHeader(data));
      return result;
    }
    case Header::kUdpHeader: {
      ASSIGN_OR_RETURN(*result.mutable_udp_header(), ParseUdpHeader(data));
      return result;
    }
    case Header::kTcpHeader: {
      ASSIGN_OR_RETURN(*result.mutable_tcp_header(), ParseTcpHeader(data));
      return result;
    }
    case Header::kArpHeader: {
      ASSIGN_OR_RETURN(*result.mutable_arp_header(), ParseArpHeader(data));
      return result;
    }
    case Header::kIcmpHeader: {
      ASSIGN_OR_RETURN(*result.mutable_icmp_header(), ParseIcmpHeader(data));
      return result;
    }
    case Header::kVlanHeader: {
      ASSIGN_OR_RETURN(*result.mutable_vlan_header(), ParseVlanHeader(data));
      return result;
    }
    case Header::kGreHeader: {
      ASSIGN_OR_RETURN(*result.mutable_gre_header(), ParseGreHeader(data));
      return result;
    }
    case Header::kSaiP4Bmv2PacketInHeader: {
      ASSIGN_OR_RETURN(*result.mutable_sai_p4_bmv2_packet_in_header(),
                       ParseSaiP4BMv2PacketInHeader(data));
      return result;
    }
    case Header::kIpfixHeader: {
      ASSIGN_OR_RETURN(*result.mutable_ipfix_header(), ParseIpfixHeader(data));
      return result;
    }
    case Header::kPsampHeader: {
      ASSIGN_OR_RETURN(*result.mutable_psamp_header(), ParsePsampHeader(data));
      return result;
    }
    case Header::kPspHeader: {
      ASSIGN_OR_RETURN(*result.mutable_psp_header(), ParsePspHeader(data));
      return result;
    }
    case Header::HEADER_NOT_SET:
      break;
  }
  return gutil::InvalidArgumentErrorBuilder()
         << "unexpected HeaderCase: " << HeaderCaseName(header_case);
}

}  // namespace

Packet ParsePacket(absl::string_view input, Header::HeaderCase first_header) {
  pdpi::BitString data = pdpi::BitString::OfByteString(input);
  Packet packet;

  // Parse headers.
  Header::HeaderCase next_header = first_header;
  while (next_header != Header::HEADER_NOT_SET) {
    absl::StatusOr<Header> header = ParseHeader(next_header, data);
    if (!header.ok()) {
      packet.add_reasons_invalid(std::string(header.status().message()));
      break;
    }
    absl::StatusOr<NextHeader> next = GetNextHeader(*header);
    if (!next.ok()) {
      LOG(DFATAL) << "SHOULD NEVER HAPPEN: " << next.status();
      break;
    }
    *packet.add_headers() = std::move(*header);
    absl::visit(gutil::Overload{
                    [&](Header::HeaderCase next) { next_header = next; },
                    [&](UnsupportedNextHeader unsupported) {
                      next_header = Header::HEADER_NOT_SET;
                      packet.set_reason_not_fully_parsed(unsupported.reason);
                    }},
                *next);
  }

  // Set payload.
  if (auto payload = data.ToByteString(); payload.ok()) {
    packet.set_payload(*payload);
  } else {
    LOG(DFATAL) << payload.status();
    packet.add_reasons_invalid(absl::StrCat(
        "INTERNAL ERROR WHILE PARSING PAYLOAD: ", payload.status().ToString()));
  }

  // Check packet validity.
  for (const auto& invalid_reason : PacketInvalidReasons(packet)) {
    packet.add_reasons_invalid(invalid_reason);
  }

  return packet;
}

// ---- Validation -------------------------------------------------------------

absl::Status ValidatePacket(const Packet& packet) {
  std::vector<std::string> invalid = PacketInvalidReasons(packet);
  if (invalid.empty()) return absl::OkStatus();
  return gutil::InvalidArgumentErrorBuilder()
         << "Packet invalid for the following reasons:\n- "
         << absl::StrJoin(invalid, "\n- ");
}

namespace {

void MacAddressInvalidReasons(absl::string_view address,
                              const std::string& field,
                              std::vector<std::string>& output) {
  if (address.empty()) {
    output.push_back(absl::StrCat(field, ": missing"));
    return;
  }
  if (auto parsed_address = MacAddress::OfString(address);
      !parsed_address.ok()) {
    output.push_back(absl::StrCat(
        field, ": invalid format: ", parsed_address.status().message()));
  }
}
void Ipv4AddressInvalidReasons(absl::string_view address,
                               const std::string& field,
                               std::vector<std::string>& output) {
  if (address.empty()) {
    output.push_back(absl::StrCat(field, ": missing"));
    return;
  }
  if (auto parsed_address = Ipv4Address::OfString(address);
      !parsed_address.ok()) {
    output.push_back(absl::StrCat(
        field, ": invalid format: ", parsed_address.status().message()));
  }
}
void Ipv6AddressInvalidReasons(absl::string_view address,
                               const std::string& field,
                               std::vector<std::string>& output) {
  if (address.empty()) {
    output.push_back(absl::StrCat(field, ": missing"));
    return;
  }
  if (auto parsed_address = Ipv6Address::OfString(address);
      !parsed_address.ok()) {
    output.push_back(absl::StrCat(
        field, ": invalid format: ", parsed_address.status().message()));
  }
}
void HopByHopOptionsInvalidOptionsAndPadding(
    absl::string_view options_and_padding, const std::string& error_prefix,
    std::vector<std::string>& output) {
  absl::StatusOr<std::string> byte_string =
      pdpi::HexStringToByteString(options_and_padding);
  if (!byte_string.ok()) {
    output.push_back(absl::StrCat(
        error_prefix, "invalid format: ", byte_string.status().message()));
    return;
  }

  for (int i = 0; i < byte_string->size(); ++i) {
    // Checks that the option type is single padding and it skips over the
    // option and continues to process the next option.
    char option_type = byte_string->at(i);
    if (option_type == '\0') {
      continue;
    }
    if (i + 1 >= byte_string->size()) {
      output.push_back(
          absl::StrCat(error_prefix,
                       "expected option data length, but reached end of data"));
      return;
    }
    int option_data_length = static_cast<int>(byte_string->at(++i));
    // Option's data length exceeds the remaining bytes.
    if (option_data_length >= byte_string->size() - i) {
      output.push_back(absl::StrCat(
          error_prefix, "expected data length exceeds the remaining bytes: ",
          option_data_length, " > ", byte_string->size() - i));
      return;
    }

    for (int j = 1; j <= option_data_length; ++j) {
      // Checks that the option type is N-padding and it discards the rest of
      // the packet.
      if (option_type == '\1' && byte_string->at(i + j) != '\0') {
        output.push_back(absl::StrCat(
            error_prefix, "expected ", option_data_length,
            " zero bytes of padding, but the ", j, "-th byte was non-zero."));
        return;
      }
    }
    // Here, i is incremented by the option data length.
    i += option_data_length;
  }
}

// Returns `true` if invalid, `false` otherwise.
template <size_t num_bits>
bool HexStringInvalidReasons(absl::string_view hex_string,
                             const std::string& field,
                             std::vector<std::string>& output) {
  if (hex_string.empty()) {
    output.push_back(absl::StrCat(field, ": missing"));
    return true;
  }
  if (auto parsed = pdpi::HexStringToBitset<num_bits>(hex_string);
      !parsed.ok()) {
    output.push_back(
        absl::StrCat(field, ": invalid format: ", parsed.status().message()));
    return true;
  }
  return false;
}

bool Ipv4UninterpretedOptionsInvalidReasons(
    absl::string_view uninterpreted_options, const std::string& error_prefix,
    std::vector<std::string>& output) {
  if (uninterpreted_options.empty()) return false;
  if (auto bytes = pdpi::HexStringToByteString(uninterpreted_options);
      !bytes.ok()) {
    output.push_back(absl::StrCat(
        error_prefix, "invalid format: ", bytes.status().message()));
    return true;
  } else if (int num_bits = bytes->size() * 8; num_bits % 32 != 0) {
    output.push_back(absl::StrCat(error_prefix, "found ", num_bits,
                                  " bits, but expected multiple of 32 bits"));
    return true;
  }
  return false;
}

bool TcpUninterpretedOptionsInvalidReasons(
    absl::string_view uninterpreted_options, const std::string& error_prefix,
    std::vector<std::string>& output) {
  if (uninterpreted_options.empty()) return false;
  if (auto bytes = pdpi::HexStringToByteString(uninterpreted_options);
      !bytes.ok()) {
    output.push_back(absl::StrCat(
        error_prefix, "invalid format: ", bytes.status().message()));
    return true;
  } else if (int num_bits = bytes->size() * 8; num_bits % 32 != 0) {
    output.push_back(absl::StrCat(error_prefix, "found ", num_bits,
                                  " bits, but expected multiple of 32 bits"));
    return true;
  } else if (int num_words = num_bits / 32; num_words > 10) {
    output.push_back(absl::StrCat(error_prefix, "found ", num_words,
                                  " 32-bit words, but at most 10 are allowed"));
  }
  return false;
}

bool GreOptionalFieldsInvalidReasons(const std::string& checksum,
                                     const std::string& reserved1,
                                     const std::string& error_prefix,
                                     std::vector<std::string>& output) {
  if (checksum.empty() && reserved1.empty()) return false;

  bool invalid = false;
  if (auto bytes = pdpi::HexStringToByteString(checksum); !bytes.ok()) {
    output.push_back(absl::StrCat(
        error_prefix, "invalid format: ", bytes.status().message()));
    invalid = true;
  } else if (int num_bits = bytes->size() * 8; num_bits != 16) {
    output.push_back(absl::StrCat(error_prefix, "found ", num_bits,
                                  " bits, but expected 16 bits"));
    invalid = true;
  }

  if (auto bytes = pdpi::HexStringToByteString(reserved1); !bytes.ok()) {
    output.push_back(absl::StrCat(
        error_prefix, "invalid format: ", bytes.status().message()));
    invalid = true;
  } else if (int num_bits = bytes->size() * 8; num_bits != 16) {
    output.push_back(absl::StrCat(error_prefix, "found ", num_bits,
                                  " bits, but expected 16 bits"));
    invalid = true;
  }

  return invalid;
}

void EthernetHeaderInvalidReasons(const EthernetHeader& header,
                                  const std::string& field_prefix,
                                  const Packet& packet, int header_index,
                                  std::vector<std::string>& output) {
  MacAddressInvalidReasons(header.ethernet_destination(),
                           absl::StrCat(field_prefix, "ethernet_destination"),
                           output);
  MacAddressInvalidReasons(header.ethernet_source(),
                           absl::StrCat(field_prefix, "ethernet_source"),
                           output);
  bool ethertype_invalid = HexStringInvalidReasons<kEthernetEthertypeBitwidth>(
      header.ethertype(), absl::StrCat(field_prefix, "ethertype"), output);

  // Check EtherType and minimum payload size, see
  // https://en.wikipedia.org/wiki/EtherType.
  if (auto size = PacketSizeInBytes(packet, header_index + 1); !size.ok()) {
    output.push_back(absl::StrCat(
        field_prefix,
        "couldn't compute payload size: ", size.status().ToString()));
  } else if (auto ethertype = pdpi::HexStringToInt(header.ethertype());
             !ethertype_invalid && !ethertype.ok()) {
    LOG(DFATAL) << field_prefix << "ethertype invalid despite previous check: "
                << ethertype.status();
    output.push_back(absl::StrCat(field_prefix, "ethertype: INTERNAL ERROR: ",
                                  ethertype.status().ToString()));
  } else if (*ethertype <= 1500 && *size != *ethertype) {
    output.push_back(
        absl::StrFormat("%sethertype: value %s is <= 1500 and should thus "
                        "match payload size, but payload size is %d bytes",
                        field_prefix, header.ethertype(), *size));

  } else if (*ethertype > 1500 && *size < kMinNumBytesInEthernetPayload) {
    output.push_back(absl::StrCat(
        field_prefix, "expected at least ", kMinNumBytesInEthernetPayload,
        " bytes of Ethernet payload, but got only ", *size));
  }
}

void Ipv4HeaderInvalidReasons(const Ipv4Header& header,
                              const std::string& field_prefix,
                              const Packet& packet, int header_index,
                              std::vector<std::string>& output) {
  bool version_invalid = HexStringInvalidReasons<kIpVersionBitwidth>(
      header.version(), absl::StrCat(field_prefix, "version"), output);
  bool ihl_invalid = HexStringInvalidReasons<kIpIhlBitwidth>(
      header.ihl(), absl::StrCat(field_prefix, "ihl"), output);
  HexStringInvalidReasons<kIpDscpBitwidth>(
      header.dscp(), absl::StrCat(field_prefix, "dscp"), output);
  HexStringInvalidReasons<kIpEcnBitwidth>(
      header.ecn(), absl::StrCat(field_prefix, "ecn"), output);
  bool length_invalid = HexStringInvalidReasons<kIpTotalLengthBitwidth>(
      header.total_length(), absl::StrCat(field_prefix, "total_length"),
      output);
  HexStringInvalidReasons<kIpIdentificationBitwidth>(
      header.identification(), absl::StrCat(field_prefix, "identification"),
      output);
  HexStringInvalidReasons<kIpFlagsBitwidth>(
      header.flags(), absl::StrCat(field_prefix, "flags"), output);
  HexStringInvalidReasons<kIpFragmentOffsetBitwidth>(
      header.fragment_offset(), absl::StrCat(field_prefix, "fragment_offset"),
      output);
  HexStringInvalidReasons<kIpTtlBitwidth>(
      header.ttl(), absl::StrCat(field_prefix, "ttl"), output);
  HexStringInvalidReasons<kIpProtocolBitwidth>(
      header.protocol(), absl::StrCat(field_prefix, "protocol"), output);
  bool checksum_invalid = HexStringInvalidReasons<kIpChecksumBitwidth>(
      header.checksum(), absl::StrCat(field_prefix, "checksum"), output);
  Ipv4AddressInvalidReasons(header.ipv4_source(),
                            absl::StrCat(field_prefix, "ipv4_source"), output);
  Ipv4AddressInvalidReasons(header.ipv4_destination(),
                            absl::StrCat(field_prefix, "ipv4_destination"),
                            output);
  bool options_invalid = Ipv4UninterpretedOptionsInvalidReasons(
      header.uninterpreted_options(),
      absl::StrCat(field_prefix, "uninterpreted_options: "), output);

  // Check computed fields.
  if (!ihl_invalid) {
    if (options_invalid) {
      output.push_back(absl::StrCat(field_prefix,
                                    "ihl: Correct value undefined since "
                                    "uninterpreted_options is invalid."));
    } else {
      absl::string_view options = header.uninterpreted_options();
      // 4 bits for every hex char after "0x"-prefix.
      int options_bitwidth = options.empty() ? 0 : 4 * (options.size() - 2);
      int num_32bit_words = 5 + options_bitwidth / 32;
      std::string expected =
          pdpi::BitsetToHexString<kIpIhlBitwidth>(num_32bit_words);
      if (header.ihl() != expected) {
        output.push_back(absl::StrCat(field_prefix, "ihl: Must be ", expected,
                                      ", but was ", header.ihl(), " instead."));
      }
    }
  }
  if (!version_invalid && header.version() != "0x4") {
    output.push_back(absl::StrCat(field_prefix,
                                  "version: Must be 0x4, but was ",
                                  header.version(), " instead."));
  }
  if (!length_invalid) {
    if (auto size = PacketSizeInBytes(packet, header_index); !size.ok()) {
      output.push_back(absl::StrCat(
          field_prefix, "total_length: Couldn't compute expected size: ",
          size.status().ToString()));
    } else {
      std::string expected =
          pdpi::BitsetToHexString(std::bitset<kIpTotalLengthBitwidth>(*size));
      if (header.total_length() != expected) {
        output.push_back(absl::StrCat(field_prefix, "total_length: Must be ",
                                      expected, ", but was ",
                                      header.total_length(), " instead."));
      }
    }
  }
  if (!checksum_invalid) {
    if (auto checksum = Ipv4HeaderChecksum(header); !checksum.ok()) {
      output.push_back(absl::StrCat(
          field_prefix, "checksum: Couldn't compute expected checksum: ",
          checksum.status().ToString()));
    } else {
      std::string expected =
          pdpi::BitsetToHexString(std::bitset<kIpChecksumBitwidth>(*checksum));
      if (header.checksum() != expected) {
        output.push_back(absl::StrCat(field_prefix, "checksum: Must be ",
                                      expected, ", but was ", header.checksum(),
                                      " instead."));
      }
    }
  }
}

void Ipv6HeaderInvalidReasons(const Ipv6Header& header,
                              const std::string& field_prefix,
                              const Packet& packet, int header_index,
                              std::vector<std::string>& output) {
  bool version_invalid = HexStringInvalidReasons<kIpVersionBitwidth>(
      header.version(), absl::StrCat(field_prefix, "version"), output);
  HexStringInvalidReasons<kIpDscpBitwidth>(
      header.dscp(), absl::StrCat(field_prefix, "dscp"), output);
  HexStringInvalidReasons<kIpEcnBitwidth>(
      header.ecn(), absl::StrCat(field_prefix, "ecn"), output);
  HexStringInvalidReasons<kIpFlowLabelBitwidth>(
      header.flow_label(), absl::StrCat(field_prefix, "flow_label"), output);
  bool length_invalid = HexStringInvalidReasons<kIpPayloadLengthBitwidth>(
      header.payload_length(), absl::StrCat(field_prefix, "payload_length"),
      output);
  HexStringInvalidReasons<kIpNextHeaderBitwidth>(
      header.next_header(), absl::StrCat(field_prefix, "next_header"), output);
  HexStringInvalidReasons<kIpHopLimitBitwidth>(
      header.hop_limit(), absl::StrCat(field_prefix, "hop_limit"), output);
  Ipv6AddressInvalidReasons(header.ipv6_source(),
                            absl::StrCat(field_prefix, "ipv6_source"), output);
  Ipv6AddressInvalidReasons(header.ipv6_destination(),
                            absl::StrCat(field_prefix, "ipv6_destination"),
                            output);

  // Check computed fields.
  if (!version_invalid && header.version() != "0x6") {
    output.push_back(absl::StrCat(field_prefix,
                                  "version: Must be 0x6, but was ",
                                  header.version(), " instead."));
  }
  if (!length_invalid) {
    // `+1` to skip the IPv6 header and previous headers in the calculation.
    // Note: it includes all optional header extensions in the payload.
    if (auto size = PacketSizeInBytes(packet, header_index + 1); !size.ok()) {
      output.push_back(absl::StrCat(
          field_prefix, "total_length: Couldn't compute expected size: ",
          size.status().ToString()));
    } else {
      std::string expected =
          pdpi::BitsetToHexString(std::bitset<kIpPayloadLengthBitwidth>(*size));
      if (header.payload_length() != expected) {
        output.push_back(absl::StrCat(field_prefix, "payload_length: Must be ",
                                      expected, ", but was ",
                                      header.payload_length(), " instead."));
      }
    }
  }
}

void HopByHopOptionsHeaderInvalidReasons(const HopByHopOptionsHeader& header,
                                         const std::string& field_prefix,
                                         const Packet& packet, int header_index,
                                         std::vector<std::string>& output) {
  HexStringInvalidReasons<kHopByHopNextHeaderBitwidth>(
      header.next_header(), absl::StrCat(field_prefix, "next_header"), output);
  HexStringInvalidReasons<kHopByHopHeaderExtensionLengthBitwidth>(
      header.header_extension_length(),
      absl::StrCat(field_prefix, "header_extension_length"), output);

  if (!HexStringInvalidReasons<kHopByHopOptionsAndPaddingBitwidth>(
          header.options_and_padding(),
          absl::StrCat(field_prefix, "options_and_padding"), output)) {
    HopByHopOptionsInvalidOptionsAndPadding(
        header.options_and_padding(),
        absl::StrCat(field_prefix, "options_and_padding: "), output);
  }
}

void UdpHeaderInvalidReasons(const UdpHeader& header,
                             const std::string& field_prefix,
                             const Packet& packet, int header_index,
                             std::vector<std::string>& output) {
  HexStringInvalidReasons<kUdpPortBitwidth>(
      header.source_port(), absl::StrCat(field_prefix, "source_port"), output);
  HexStringInvalidReasons<kUdpPortBitwidth>(
      header.destination_port(), absl::StrCat(field_prefix, "destination_port"),
      output);
  bool length_invalid = HexStringInvalidReasons<kUdpLengthBitwidth>(
      header.length(), absl::StrCat(field_prefix, "length"), output);
  bool checksum_invalid = HexStringInvalidReasons<kUdpChecksumBitwidth>(
      header.checksum(), absl::StrCat(field_prefix, "checksum"), output);

  // Check computed field: length.
  if (!length_invalid) {
    if (auto size = PacketSizeInBytes(packet, header_index); !size.ok()) {
      output.push_back(absl::StrCat(field_prefix,
                                    "length: Couldn't compute expected size: ",
                                    size.status().ToString()));
    } else {
      std::string expected =
          pdpi::BitsetToHexString(std::bitset<kUdpLengthBitwidth>(*size));
      if (header.length() != expected) {
        output.push_back(absl::StrCat(field_prefix, "length: Must be ",
                                      expected, ", but was ", header.length(),
                                      " instead."));
      }
    }
  }
  // Check computed field: checksum.
  if (!checksum_invalid) {
    if (absl::StatusOr<std::optional<int>> checksum =
            UdpHeaderChecksum(packet, header_index);
        !checksum.ok()) {
      output.push_back(absl::StrCat(
          field_prefix, "checksum: Couldn't compute expected checksum: ",
          checksum.status().ToString()));
    } else if (header.checksum() == UdpChecksum(0) || !checksum->has_value()) {
      // We always allow the UDP checksum to be zero. In certain cases we also
      // allow the checksum to be anything (i.e. UdpHeaderChecksum returns
      // nullopt).
    } else if (std::string expected = pdpi::BitsetToHexString(
                   std::bitset<kUdpChecksumBitwidth>(checksum->value()));
               header.checksum() != expected) {
      output.push_back(absl::StrCat(field_prefix, "checksum: Must be ",
                                    expected, ", but was ", header.checksum(),
                                    " instead."));
    }
  }
}

void TcpHeaderInvalidReasons(const TcpHeader& header,
                             const std::string& field_prefix,
                             const Packet& packet, int header_index,
                             std::vector<std::string>& output) {
  HexStringInvalidReasons<kUdpPortBitwidth>(
      header.source_port(), absl::StrCat(field_prefix, "source_port"), output);
  HexStringInvalidReasons<kUdpPortBitwidth>(
      header.destination_port(), absl::StrCat(field_prefix, "destination_port"),
      output);
  HexStringInvalidReasons<kTcpSequenceNumberBitwidth>(
      header.sequence_number(), absl::StrCat(field_prefix, "sequence_number"),
      output);
  HexStringInvalidReasons<kTcpAcknowledgementNumberBitwidth>(
      header.acknowledgement_number(),
      absl::StrCat(field_prefix, "acknowledgement_number"), output);
  bool data_offset_invalid = HexStringInvalidReasons<kTcpDataOffsetBitwidth>(
      header.data_offset(), absl::StrCat(field_prefix, "data_offset"), output);
  HexStringInvalidReasons<kTcpRestOfHeaderBitwidth>(
      header.rest_of_header(), absl::StrCat(field_prefix, "rest_of_header"),
      output);
  bool options_invalid = TcpUninterpretedOptionsInvalidReasons(
      header.uninterpreted_options(),
      absl::StrCat(field_prefix, "uninterpreted_options: "), output);

  // Check computed fields.
  if (!data_offset_invalid) {
    if (options_invalid) {
      output.push_back(absl::StrCat(field_prefix,
                                    "data_offset: Correct value undefined "
                                    "since uninterpreted_options is invalid."));
    } else {
      absl::string_view options = header.uninterpreted_options();
      // 4 bits for every hex char after "0x"-prefix.
      int options_bitwidth = options.empty() ? 0 : 4 * (options.size() - 2);
      int num_32bit_words = 5 + options_bitwidth / 32;
      std::string expected =
          pdpi::BitsetToHexString<kIpIhlBitwidth>(num_32bit_words);
      if (header.data_offset() != expected) {
        output.push_back(absl::StrCat(field_prefix, "data_offset: Must be ",
                                      expected, ", but was ",
                                      header.data_offset(), " instead."));
      }
    }
  }
}

void ArpHeaderInvalidReasons(const ArpHeader& header,
                             const std::string& field_prefix,
                             const Packet& packet, int header_index,
                             std::vector<std::string>& output) {
  bool hardware_type_invalid = HexStringInvalidReasons<kArpTypeBitwidth>(
      header.hardware_type(), absl::StrCat(field_prefix, "hardware_type"),
      output);
  bool protocol_type_invalid = HexStringInvalidReasons<kArpTypeBitwidth>(
      header.protocol_type(), absl::StrCat(field_prefix, "protocol_type"),
      output);
  bool hardware_length_invalid = HexStringInvalidReasons<kArpLengthBitwidth>(
      header.hardware_length(), absl::StrCat(field_prefix, "hardware_length"),
      output);
  bool protocol_length_invalid = HexStringInvalidReasons<kArpLengthBitwidth>(
      header.protocol_length(), absl::StrCat(field_prefix, "protocol_length"),
      output);
  HexStringInvalidReasons<kArpOperationBitwidth>(
      header.operation(), absl::StrCat(field_prefix, "operation"), output);
  MacAddressInvalidReasons(
      header.sender_hardware_address(),
      absl::StrCat(field_prefix, "sender_hardware_address"), output);
  Ipv4AddressInvalidReasons(
      header.sender_protocol_address(),
      absl::StrCat(field_prefix, "sender_protocol_address"), output);
  MacAddressInvalidReasons(
      header.target_hardware_address(),
      absl::StrCat(field_prefix, "target_hardware_address"), output);
  Ipv4AddressInvalidReasons(
      header.target_protocol_address(),
      absl::StrCat(field_prefix, "target_protocol_address"), output);

  if (!hardware_type_invalid && header.hardware_type() != "0x0001") {
    output.push_back(absl::StrCat(field_prefix,
                                  "hardware_type: Must be 0x0001, but was ",
                                  header.hardware_type(), " instead."));
  }
  if (!protocol_type_invalid && header.protocol_type() != "0x0800") {
    output.push_back(absl::StrCat(field_prefix,
                                  "protocol_type: Must be 0x0800, but was ",
                                  header.protocol_type(), " instead."));
  }
  if (!hardware_length_invalid && header.hardware_length() != "0x06") {
    output.push_back(absl::StrCat(field_prefix,
                                  "hardware_length: Must be 0x06, but was ",
                                  header.hardware_length(), " instead."));
  }
  if (!protocol_length_invalid && header.protocol_length() != "0x04") {
    output.push_back(absl::StrCat(field_prefix,
                                  "hardware_type: Must be 0x04, but was ",
                                  header.protocol_length(), " instead."));
  }
}

// Searches for a preceding IP header by skipping any IPv6 header extension
// options.
int FindPrecedingIpHeader(const Packet& packet, int header_index) {
  int ip_header_index = header_index - 1;
  if (ip_header_index >= 0 && packet.headers(ip_header_index).header_case() ==
                                  Header::kHopByHopOptionsHeader) {
    ip_header_index--;
  }
  return ip_header_index;
}

void IcmpHeaderInvalidReasons(const IcmpHeader& header,
                              const std::string& field_prefix,
                              const Packet& packet, int header_index,
                              std::vector<std::string>& output) {
  HexStringInvalidReasons<kIcmpTypeBitwidth>(
      header.type(), absl::StrCat(field_prefix, "type"), output);
  HexStringInvalidReasons<kIcmpCodeBitwidth>(
      header.code(), absl::StrCat(field_prefix, "code"), output);
  bool checksum_invalid = HexStringInvalidReasons<kIcmpChecksumBitwidth>(
      header.checksum(), absl::StrCat(field_prefix, "checksum"), output);
  HexStringInvalidReasons<kIcmpRestOfHeaderBitwidth>(
      header.rest_of_header(), absl::StrCat(field_prefix, "rest_of_header"),
      output);

  // ICMP should be preceded by either an IPv4 or IPv6 header.
  if (header_index <= 0) {
    output.push_back(absl::StrCat(field_prefix,
                                  "checksum: ICMP header must be preceded by "
                                  "IP header for checksum to be "
                                  "defined; found no header instead"));
    return;
  }
  // Searches for a preceding IP header.
  int ip_header_index = FindPrecedingIpHeader(packet, header_index);
  Header::HeaderCase previous = packet.headers(ip_header_index).header_case();
  if (previous != Header::kIpv4Header && previous != Header::kIpv6Header) {
    output.push_back(absl::StrCat(field_prefix,
                                  "checksum: ICMP header must be preceded by "
                                  "IP header for checksum to be "
                                  "defined; found ",
                                  HeaderCaseName(previous), " at headers[",
                                  (ip_header_index), "] instead"));
    return;
  }

  // Validate checksum if it isn't invalid.
  if (checksum_invalid) {
    return;
  }
  if (auto checksum = IcmpHeaderChecksum(packet, header_index);
      !checksum.ok()) {
    output.push_back(absl::StrCat(
        field_prefix, "checksum: Couldn't compute expected checksum: ",
        checksum.status().ToString()));
  } else {
    std::string expected =
        pdpi::BitsetToHexString(std::bitset<kIcmpChecksumBitwidth>(*checksum));
    if (header.checksum() != expected) {
      output.push_back(absl::StrCat(field_prefix, "checksum: Must be ",
                                    expected, ", but was ", header.checksum(),
                                    " instead."));
    }
  }
}

void VlanHeaderInvalidReasons(const VlanHeader& header,
                              const std::string& field_prefix,
                              const Packet& packet, int header_index,
                              std::vector<std::string>& output) {
  HexStringInvalidReasons<kVlanPriorityCodePointBitwidth>(
      header.priority_code_point(),
      absl::StrCat(field_prefix, "priority_code_point"), output);
  HexStringInvalidReasons<kVlanDropEligibilityIndicatorBitwidth>(
      header.drop_eligible_indicator(),
      absl::StrCat(field_prefix, "drop_eligible_indicator"), output);
  HexStringInvalidReasons<kVlanVlanIdentifierBitwidth>(
      header.vlan_identifier(), absl::StrCat(field_prefix, "vlan_identifier"),
      output);
  HexStringInvalidReasons<kVlanEthertypeBitwidth>(
      header.ethertype(), absl::StrCat(field_prefix, "ethertype"), output);
}

void GreHeaderInvalidReasons(const GreHeader& header,
                             const std::string& field_prefix,
                             const Packet& packet, int header_index,
                             std::vector<std::string>& output) {
  bool checksum_present_invalid =
      HexStringInvalidReasons<kGreChecksumPresentBitwidth>(
          header.checksum_present(),
          absl::StrCat(field_prefix, "checksum_present"), output);
  bool reserved0_invalid = HexStringInvalidReasons<kGreReserved0Bitwidth>(
      header.reserved0(), absl::StrCat(field_prefix, "reserved0"), output);
  bool version_invalid = HexStringInvalidReasons<kGreVersionBitwidth>(
      header.version(), absl::StrCat(field_prefix, "version"), output);

  if (!reserved0_invalid && header.reserved0() != "0x000") {
    output.push_back(absl::StrCat(field_prefix,
                                  "reserved0: Must be 0x000, but was ",
                                  header.reserved0(), " instead."));
  }

  if (!version_invalid && header.version() != "0x0") {
    output.push_back(absl::StrCat(field_prefix,
                                  "version: Must be 0x0, but was ",
                                  header.version(), " instead."));
  }

  if (checksum_present_invalid || header.checksum_present() != "0x1") {
    if (!header.checksum().empty())
      output.push_back(
          absl::StrCat(field_prefix,
                       "Checksum_present: checksum present bit is not set and "
                       "checksum must be empty, but was '",
                       header.checksum(), "' instead."));
    if (!header.reserved1().empty())
      output.push_back(
          absl::StrCat(field_prefix,
                       "Checksum_present: checksum present bit is not set and "
                       "reserved1 must be empty, but was ",
                       header.reserved1(), " instead."));
    return;
  }

  bool optional_fields_invalid = GreOptionalFieldsInvalidReasons(
      header.checksum(), header.reserved1(),
      absl::StrCat(field_prefix, "optional fields: "), output);

  if (optional_fields_invalid) {
    output.push_back(absl::StrCat(field_prefix,
                                  "checksum_present: checksum present bit is "
                                  "set, but optional fields are invalid."));
  } else {
    // Check computed field: checksum.
    if (auto checksum = GreHeaderChecksum(packet, header_index);
        !checksum.ok()) {
      output.push_back(absl::StrCat(
          field_prefix, "checksum: Couldn't compute expected checksum: ",
          checksum.status().ToString()));
    } else {
      std::string expected =
          pdpi::BitsetToHexString(std::bitset<kGreChecksumBitwidth>(*checksum));
      if (header.checksum() != expected) {
        output.push_back(absl::StrCat(field_prefix, "checksum: Must be ",
                                      expected, ", but was ", header.checksum(),
                                      " instead."));
      }
    }

    if (header.reserved1() != "0x0000") {
      output.push_back(absl::StrCat(field_prefix,
                                    "reserved1: Must be 0x0000, but was ",
                                    header.reserved1(), " instead."));
    }
  }
}

void SaiP4BMv2PacketInHeaderInvalidReasons(
    const SaiP4BMv2PacketInHeader& header, const std::string& field_prefix,
    const Packet& packet, int header_index, std::vector<std::string>& output) {
  HexStringInvalidReasons<kSaiP4BMv2PacketInIngressPortBitwidth>(
      header.ingress_port(), absl::StrCat(field_prefix, "ingress_port"),
      output);
  HexStringInvalidReasons<kSaiP4BMv2PacketInTargetEgressPortBitwidth>(
      header.target_egress_port(),
      absl::StrCat(field_prefix, "target_egress_port"), output);
  bool unused_pad_invalid =
      HexStringInvalidReasons<kSaiP4BMv2PacketInUnusedPadBitwidth>(
          header.unused_pad(), absl::StrCat(field_prefix, "unused_pad"),
          output);

  if (!unused_pad_invalid) {
    absl::StatusOr<int> unused_pad = pdpi::HexStringToInt(header.unused_pad());
    if (!unused_pad.ok()) {
      LOG(DFATAL) << "SHOULD NEVER HAPPEN: unused_pad badly formatted: "
                  << unused_pad.status();
    }
    if (*unused_pad != 0) {
      output.push_back(absl::StrCat(field_prefix,
                                    "unused_pad: Must be 0, but was ",
                                    header.unused_pad(), " instead."));
    }
  }
}

void IpfixHeaderInvalidReasons(const IpfixHeader& header,
                               const std::string& field_prefix,
                               const Packet& packet, int header_index,
                               std::vector<std::string>& output) {
  HexStringInvalidReasons<kIpfixVersionBitwidth>(
      header.version(), absl::StrCat(field_prefix, "version"), output);
  HexStringInvalidReasons<kIpfixExportTimeBitwidth>(
      header.export_time(), absl::StrCat(field_prefix, "export_time"), output);
  HexStringInvalidReasons<kIpfixSequenceNumberBitwidth>(
      header.sequence_number(), absl::StrCat(field_prefix, "sequence_number"),
      output);
  HexStringInvalidReasons<kIpfixObservationDomainIdBitwidth>(
      header.observation_domain_id(),
      absl::StrCat(field_prefix, "observation_domain_id"), output);

  bool length_invalid = HexStringInvalidReasons<kIpfixLengthBitwidth>(
      header.length(), absl::StrCat(field_prefix, "length"), output);
  // Check computed field: length.
  if (!length_invalid) {
    if (auto size = PacketSizeInBytes(packet, header_index); !size.ok()) {
      output.push_back(absl::StrCat(field_prefix,
                                    "length: Couldn't compute expected size: ",
                                    size.status().ToString()));
    } else {
      std::string expected =
          pdpi::BitsetToHexString(std::bitset<kIpfixLengthBitwidth>(*size));
      if (header.length() != expected) {
        output.push_back(absl::StrCat(field_prefix, "length: Must be ",
                                      expected, ", but was ", header.length(),
                                      " instead."));
      }
    }
  }
}

void PsampHeaderInvalidReasons(const PsampHeader& header,
                               const std::string& field_prefix,
                               const Packet& packet, int header_index,
                               std::vector<std::string>& output) {
  HexStringInvalidReasons<kPsampTemplateIdBitwidth>(
      header.template_id(), absl::StrCat(field_prefix, "template_id"), output);
  HexStringInvalidReasons<kPsampObservationTimeBitwidth>(
      header.observation_time(), absl::StrCat(field_prefix, "observation_time"),
      output);
  HexStringInvalidReasons<kPsampFlowsetBitwidth>(
      header.flowset(), absl::StrCat(field_prefix, "flowset"), output);
  HexStringInvalidReasons<kPsampNextHopIndexBitwidth>(
      header.next_hop_index(), absl::StrCat(field_prefix, "next_hop_index"),
      output);
  HexStringInvalidReasons<kPsampEpochBitwidth>(
      header.epoch(), absl::StrCat(field_prefix, "epoch"), output);
  HexStringInvalidReasons<kPsampIngressPortBitwidth>(
      header.ingress_port(), absl::StrCat(field_prefix, "ingress_port"),
      output);
  HexStringInvalidReasons<kPsampEgressPortBitwidth>(
      header.egress_port(), absl::StrCat(field_prefix, "egress_port"), output);
  HexStringInvalidReasons<kPsampUserMetaFieldBitwidth>(
      header.user_meta_field(), absl::StrCat(field_prefix, "user_meta_field"),
      output);
  HexStringInvalidReasons<kPsampDlbIdBitwidth>(
      header.dlb_id(), absl::StrCat(field_prefix, "dlb_id"), output);
  bool variable_length_invalid =
      HexStringInvalidReasons<kPsampVariableLengthBitwidth>(
          header.variable_length(),
          absl::StrCat(field_prefix, "variable_length"), output);

  if (!variable_length_invalid) {
    if (auto variable_length = pdpi::HexStringToInt(header.variable_length());
        !variable_length.ok()) {
      output.push_back(absl::StrCat(field_prefix,
                                    "variable_length: Couldn't parse value: ",
                                    variable_length.status().ToString()));
    } else {
      if (variable_length.value() != 0xff) {
        output.push_back(absl::StrCat(field_prefix,
                                      "variable_length: Must be 0xFF, but was ",
                                      header.variable_length(), " instead."));
      }
    }
  }

  // Check computed field length
  bool length_invalid = HexStringInvalidReasons<kPsampLengthBitwidth>(
      header.length(), absl::StrCat(field_prefix, "length"), output);
  if (!length_invalid) {
    if (auto size = PacketSizeInBytes(packet, header_index); !size.ok()) {
      output.push_back(absl::StrCat(field_prefix,
                                    "length: Couldn't compute expected size: ",
                                    size.status().ToString()));
    } else {
      std::string expected =
          pdpi::BitsetToHexString(std::bitset<kPsampLengthBitwidth>(*size));
      if (header.length() != expected) {
        output.push_back(absl::StrCat(field_prefix, "length: Must be ",
                                      expected, ", but was ", header.length(),
                                      " instead."));
      }
    }
  }

  // Check computed field packet_sampled_length
  bool packet_sampled_length_invalid =
      HexStringInvalidReasons<kPsampPacketSampledLengthBitwidth>(
          header.packet_sampled_length(),
          absl::StrCat(field_prefix, "packet_sampled_length"), output);
  if (!packet_sampled_length_invalid) {
    if (auto size = PacketSizeInBytes(packet, header_index + 1); !size.ok()) {
      output.push_back(absl::StrCat(field_prefix,
                                    "length: Couldn't compute expected size: ",
                                    size.status().ToString()));
    } else {
      std::string expected = pdpi::BitsetToHexString(
          std::bitset<kPsampPacketSampledLengthBitwidth>(*size));
      if (header.packet_sampled_length() != expected) {
        output.push_back(absl::StrCat(
            field_prefix, "packet_sampled_length: Must be ", expected,
            ", but was ", header.packet_sampled_length(), " instead."));
      }
    }
  }
}

void PspHeaderInvalidReasons(const PspHeader& header,
                             const std::string& field_prefix,
                             std::vector<std::string>& output) {
  HexStringInvalidReasons<kPspNextHeaderBitwidth>(
      header.next_header(), absl::StrCat(field_prefix, "next_header"), output);
  HexStringInvalidReasons<kPspHeaderExtLengthBitwidth>(
      header.header_ext_length(),
      absl::StrCat(field_prefix, "header_ext_length"), output);
  HexStringInvalidReasons<kPspCryptOffsetBitwidth>(
      header.crypt_offset(), absl::StrCat(field_prefix, "crypt_offset"),
      output);
  HexStringInvalidReasons<kPspSampleBitwidth>(
      header.sample_bit(), absl::StrCat(field_prefix, "sample_bit"), output);
  HexStringInvalidReasons<kPspDropBitwidth>(
      header.drop_bit(), absl::StrCat(field_prefix, "drop_bit"), output);
  HexStringInvalidReasons<kPspVersionBitwidth>(
      header.version(), absl::StrCat(field_prefix, "version"), output);
  HexStringInvalidReasons<kPspVirtualizationCookieBitwidth>(
      header.virtualization_cookie_present(),
      absl::StrCat(field_prefix, "virtualization_cookie_present"), output);
  HexStringInvalidReasons<kPspSecurityParametersIndexBitwidth>(
      header.security_parameters_index(),
      absl::StrCat(field_prefix, "security_parameters_index"), output);
  HexStringInvalidReasons<kPspInitializationVectorBitwidth>(
      header.initialization_vector(),
      absl::StrCat(field_prefix, "initialization_vector"), output);

  // Verify that the reserved fields are correct per the PSP spec.
  bool reserved0_invalid = HexStringInvalidReasons<kPspReserved0Bitwidth>(
      header.reserved0(), absl::StrCat(field_prefix, "reserved0"), output);
  if (!reserved0_invalid && header.reserved0() != "0x0") {
    output.push_back(absl::StrCat(field_prefix,
                                  "reserved0: Must be 0x0, but was ",
                                  header.reserved0(), " instead."));
  }

  // TODO: Enable once DVaaS handles invalid packets correctly.
  // bool reserved1_invalid = HexStringInvalidReasons<kPspReserved1Bitwidth>(
  //     header.reserved1(), absl::StrCat(field_prefix, "reserved1"), output);
  // if (!reserved1_invalid && header.reserved1() != "0x1") {
  //   output.push_back(absl::StrCat(field_prefix,
  //                                 "reserved1: Must be 0x1, but was ",
  //                                 header.reserved1(), " instead."));
  // }
}

}  // namespace

std::string HeaderCaseName(Header::HeaderCase header_case) {
  switch (header_case) {
    case Header::kEthernetHeader:
      return "EthernetHeader";
    case Header::kIpv4Header:
      return "Ipv4Header";
    case Header::kIpv6Header:
      return "Ipv6Header";
    case Header::kHopByHopOptionsHeader:
      return "HopByHopOptionsHeader";
    case Header::kUdpHeader:
      return "UdpHeader";
    case Header::kTcpHeader:
      return "TcpHeader";
    case Header::kArpHeader:
      return "ArpHeader";
    case Header::kIcmpHeader:
      return "IcmpHeader";
    case Header::kVlanHeader:
      return "VlanHeader";
    case Header::kGreHeader:
      return "GreHeader";
    case Header::kSaiP4Bmv2PacketInHeader:
      return "SaiP4BMv2PacketInHeader";
    case Header::kIpfixHeader:
      return "IpfixHeader";
    case Header::kPsampHeader:
      return "PsampHeader";
    case Header::kPspHeader:
      return "PspHeader";
    case Header::HEADER_NOT_SET:
      return "HEADER_NOT_SET";
  }
  LOG(DFATAL) << "unexpected HeaderCase: " << header_case;
  return "";
}

absl::StatusOr<std::string> GetEthernetTrailer(const Packet& packet) {
  // Make sure that the start contains a ETH header.
  if (packet.headers().empty() || !packet.headers(0).has_ethernet_header()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "The packet must start with an Ethernet header, but does not: "
           << gutil::PrintTextProto(packet);
  }
  // Skip VLAN headers.
  int header_index = 1;
  while (header_index < packet.headers().size() &&
         (packet.headers(header_index).has_vlan_header())) {
    ++header_index;
  }
  if (header_index >= packet.headers().size()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "The packet must contain at least one header after the "
              "Ethernet/VLAN headers, but none were found: "
           << gutil::PrintTextProto(packet);
  }
  ASSIGN_OR_RETURN(std::string raw_packet, RawSerializePacket(packet));
  const Header& header = packet.headers(header_index);
  switch (header.header_case()) {
    case Header::kIpv4Header: {
      ASSIGN_OR_RETURN(
          const int packet_size_starting_from_ipv4_according_to_ip_header,
          pdpi::HexStringToInt(header.ipv4_header().total_length()));
      ASSIGN_OR_RETURN(int actual_packet_size_starting_from_ipv4,
                       PacketSizeInBytes(packet, header_index));
      int trailer_size = actual_packet_size_starting_from_ipv4 -
                         packet_size_starting_from_ipv4_according_to_ip_header;
      if (trailer_size < 0) return "";
      if (trailer_size > raw_packet.size()) {
        return absl::InternalError(
            absl::StrCat("Impossible: ", gutil::PrintTextProto(packet)));
      }
      int trailer_offset_in_packet = raw_packet.size() - trailer_size;
      return raw_packet.substr(trailer_offset_in_packet);
    }
    case Header::kIpv6Header: {
      ASSIGN_OR_RETURN(
          const int packet_size_starting_after_ipv6_according_to_ip_header,
          pdpi::HexStringToInt(header.ipv6_header().payload_length()));
      ASSIGN_OR_RETURN(int actual_packet_size_starting_after_ipv6,
                       PacketSizeInBytes(packet, header_index + 1));
      int trailer_size = actual_packet_size_starting_after_ipv6 -
                         packet_size_starting_after_ipv6_according_to_ip_header;

      if (trailer_size < 0) return "";
      if (trailer_size > raw_packet.size()) {
        return absl::InternalError(
            absl::StrCat("Impossible: ", gutil::PrintTextProto(packet)));
      }
      int trailer_offset_in_packet = raw_packet.size() - trailer_size;
      return raw_packet.substr(trailer_offset_in_packet);
    }
    case Header::kArpHeader: {
      return raw_packet;
    }
    default: {
      return gutil::InvalidArgumentErrorBuilder()
             << "Expected an IPv4/IPv6/ARP header directly after the "
                "Ethernet/VLAN headers, but didn't find one:"
             << gutil::PrintTextProto(packet);
    }
  }
}

std::vector<std::string> PacketInvalidReasons(const Packet& packet) {
  std::vector<std::string> result;

  if (packet.ByteSize() == 0) {
    result.push_back("Packet is empty.");
    return result;
  }

  if (auto bitsize = PacketSizeInBits(packet); !bitsize.ok()) {
    result.push_back(absl::StrCat("Unable to determine total packet size: ",
                                  bitsize.status().ToString()));
  } else if (*bitsize % 8 != 0) {
    result.push_back(absl::StrCat(
        "Packet size must be multiple of 8 bits; found ", *bitsize, " bits"));
  }

  Header::HeaderCase expected_header_case =
      packet.headers().empty() ? Header::HEADER_NOT_SET
                               : packet.headers(0).header_case();
  int index = -1;
  for (const Header& header : packet.headers()) {
    index += 1;
    const std::string error_prefix = absl::StrFormat(
        "in %s headers[%d]: ", HeaderCaseName(header.header_case()), index);

    switch (header.header_case()) {
      case Header::kEthernetHeader:
        EthernetHeaderInvalidReasons(header.ethernet_header(), error_prefix,
                                     packet, index, result);
        break;
      case Header::kIpv4Header:
        Ipv4HeaderInvalidReasons(header.ipv4_header(), error_prefix, packet,
                                 index, result);
        break;
      case Header::kIpv6Header:
        Ipv6HeaderInvalidReasons(header.ipv6_header(), error_prefix, packet,
                                 index, result);
        break;
      case Header::kHopByHopOptionsHeader:
        HopByHopOptionsHeaderInvalidReasons(header.hop_by_hop_options_header(),
                                            error_prefix, packet, index,
                                            result);
        break;
      case Header::kUdpHeader: {
        UdpHeaderInvalidReasons(header.udp_header(), error_prefix, packet,
                                index, result);
        break;
      }
      case Header::kTcpHeader: {
        TcpHeaderInvalidReasons(header.tcp_header(), error_prefix, packet,
                                index, result);
        break;
      }
      case Header::kArpHeader: {
        ArpHeaderInvalidReasons(header.arp_header(), error_prefix, packet,
                                index, result);
        break;
      }
      case Header::kIcmpHeader: {
        IcmpHeaderInvalidReasons(header.icmp_header(), error_prefix, packet,
                                 index, result);
        break;
      }
      case Header::kVlanHeader: {
        VlanHeaderInvalidReasons(header.vlan_header(), error_prefix, packet,
                                 index, result);
        break;
      }
      case Header::kGreHeader: {
        GreHeaderInvalidReasons(header.gre_header(), error_prefix, packet,
                                index, result);
        break;
      }
      case Header::kSaiP4Bmv2PacketInHeader: {
        SaiP4BMv2PacketInHeaderInvalidReasons(
            header.sai_p4_bmv2_packet_in_header(), error_prefix, packet, index,
            result);
        break;
      }
      case Header::kIpfixHeader: {
        IpfixHeaderInvalidReasons(header.ipfix_header(), error_prefix, packet,
                                  index, result);
        break;
      }
      case Header::kPsampHeader: {
        PsampHeaderInvalidReasons(header.psamp_header(), error_prefix, packet,
                                  index, result);
        break;
      }
      case Header::kPspHeader: {
        PspHeaderInvalidReasons(header.psp_header(), error_prefix, result);
        break;
      }
      case Header::HEADER_NOT_SET:
        result.push_back(absl::StrCat(error_prefix, "header uninitialized"));
        continue;  // skip expected_header_case check
    }

    // Check order of headers.
    if (expected_header_case == Header::HEADER_NOT_SET) {
      result.push_back(absl::StrCat(
          error_prefix,
          "expected no header (because the previous header demands either no "
          "header or an unsupported header), got ",
          HeaderCaseName(header.header_case())));
    } else if (header.header_case() != expected_header_case) {
      result.push_back(absl::StrCat(
          error_prefix, "expected ", HeaderCaseName(expected_header_case),
          " (because the previous header demands it), got ",
          HeaderCaseName(header.header_case())));
    }

    // Update `expected_header_case`.
    if (absl::StatusOr<NextHeader> next = GetNextHeader(header); next.ok()) {
      expected_header_case = absl::visit(
          gutil::Overload{
              [](Header::HeaderCase next) { return next; },
              [](UnsupportedNextHeader) { return Header::HEADER_NOT_SET; }},
          *next);
    } else {
      expected_header_case = Header::HEADER_NOT_SET;
    }
  }

  if (expected_header_case != Header::HEADER_NOT_SET) {
    result.push_back(absl::StrCat("headers[", packet.headers().size(),
                                  "]: header missing - expected ",
                                  HeaderCaseName(expected_header_case)));
  }

  return result;
}

// ---- Serialization ----------------------------------------------------------

namespace {

absl::Status SerializeMacAddress(absl::string_view address,
                                 pdpi::BitString& output) {
  ASSIGN_OR_RETURN(MacAddress parsed_address, MacAddress::OfString(address));
  output.AppendBits(parsed_address.ToBitset());
  return absl::OkStatus();
}
absl::Status SerializeIpv4Address(absl::string_view address,
                                  pdpi::BitString& output) {
  ASSIGN_OR_RETURN(Ipv4Address parsed_address, Ipv4Address::OfString(address));
  output.AppendBits(parsed_address.ToBitset());
  return absl::OkStatus();
}
absl::Status SerializeIpv6Address(absl::string_view address,
                                  pdpi::BitString& output) {
  ASSIGN_OR_RETURN(Ipv6Address parsed_address, Ipv6Address::OfString(address));
  output.AppendBits(parsed_address.ToBitset());
  return absl::OkStatus();
}
template <size_t num_bits>
absl::Status SerializeBits(absl::string_view hex_string,
                           pdpi::BitString& output) {
  ASSIGN_OR_RETURN(auto bitset, pdpi::HexStringToBitset<num_bits>(hex_string));
  output.AppendBits(bitset);
  return absl::OkStatus();
}

absl::Status SerializeEthernetHeader(const EthernetHeader& header,
                                     pdpi::BitString& output) {
  RETURN_IF_ERROR(SerializeMacAddress(header.ethernet_destination(), output));
  RETURN_IF_ERROR(SerializeMacAddress(header.ethernet_source(), output));
  RETURN_IF_ERROR(
      SerializeBits<kEthernetEthertypeBitwidth>(header.ethertype(), output));
  return absl::OkStatus();
}

absl::Status SerializeIpv4Header(const Ipv4Header& header,
                                 pdpi::BitString& output) {
  RETURN_IF_ERROR(SerializeBits<kIpVersionBitwidth>(header.version(), output));
  RETURN_IF_ERROR(SerializeBits<kIpIhlBitwidth>(header.ihl(), output));
  RETURN_IF_ERROR(SerializeBits<kIpDscpBitwidth>(header.dscp(), output));
  RETURN_IF_ERROR(SerializeBits<kIpEcnBitwidth>(header.ecn(), output));
  RETURN_IF_ERROR(
      SerializeBits<kIpTotalLengthBitwidth>(header.total_length(), output));
  RETURN_IF_ERROR(SerializeBits<kIpIdentificationBitwidth>(
      header.identification(), output));
  RETURN_IF_ERROR(SerializeBits<kIpFlagsBitwidth>(header.flags(), output));
  RETURN_IF_ERROR(SerializeBits<kIpFragmentOffsetBitwidth>(
      header.fragment_offset(), output));
  RETURN_IF_ERROR(SerializeBits<kIpTtlBitwidth>(header.ttl(), output));
  RETURN_IF_ERROR(
      SerializeBits<kIpProtocolBitwidth>(header.protocol(), output));
  RETURN_IF_ERROR(
      SerializeBits<kIpChecksumBitwidth>(header.checksum(), output));
  RETURN_IF_ERROR(SerializeIpv4Address(header.ipv4_source(), output));
  RETURN_IF_ERROR(SerializeIpv4Address(header.ipv4_destination(), output));
  if (!header.uninterpreted_options().empty()) {
    RETURN_IF_ERROR(output.AppendHexString(header.uninterpreted_options()));
  }
  return absl::OkStatus();
}

absl::Status SerializeIpv6Header(const Ipv6Header& header,
                                 pdpi::BitString& output) {
  RETURN_IF_ERROR(SerializeBits<kIpVersionBitwidth>(header.version(), output));
  RETURN_IF_ERROR(SerializeBits<kIpDscpBitwidth>(header.dscp(), output));
  RETURN_IF_ERROR(SerializeBits<kIpEcnBitwidth>(header.ecn(), output));
  RETURN_IF_ERROR(
      SerializeBits<kIpFlowLabelBitwidth>(header.flow_label(), output));
  RETURN_IF_ERROR(
      SerializeBits<kIpPayloadLengthBitwidth>(header.payload_length(), output));
  RETURN_IF_ERROR(
      SerializeBits<kIpNextHeaderBitwidth>(header.next_header(), output));
  RETURN_IF_ERROR(
      SerializeBits<kIpHopLimitBitwidth>(header.hop_limit(), output));
  RETURN_IF_ERROR(SerializeIpv6Address(header.ipv6_source(), output));
  RETURN_IF_ERROR(SerializeIpv6Address(header.ipv6_destination(), output));
  return absl::OkStatus();
}

absl::Status SerializeHopByHopOptionsHeader(const HopByHopOptionsHeader& header,
                                            pdpi::BitString& output) {
  RETURN_IF_ERROR(
      SerializeBits<kHopByHopNextHeaderBitwidth>(header.next_header(), output));
  RETURN_IF_ERROR(SerializeBits<kHopByHopHeaderExtensionLengthBitwidth>(
      header.header_extension_length(), output));
  RETURN_IF_ERROR(SerializeBits<kHopByHopOptionsAndPaddingBitwidth>(
      header.options_and_padding(), output));
  return absl::OkStatus();
}

absl::Status SerializeUdpHeader(const UdpHeader& header,
                                pdpi::BitString& output) {
  RETURN_IF_ERROR(
      SerializeBits<kUdpPortBitwidth>(header.source_port(), output));
  RETURN_IF_ERROR(
      SerializeBits<kUdpPortBitwidth>(header.destination_port(), output));
  RETURN_IF_ERROR(SerializeBits<kUdpLengthBitwidth>(header.length(), output));
  RETURN_IF_ERROR(
      SerializeBits<kUdpChecksumBitwidth>(header.checksum(), output));
  return absl::OkStatus();
}

absl::Status SerializeTcpHeader(const TcpHeader& header,
                                pdpi::BitString& output) {
  RETURN_IF_ERROR(
      SerializeBits<kTcpPortBitwidth>(header.source_port(), output));
  RETURN_IF_ERROR(
      SerializeBits<kTcpPortBitwidth>(header.destination_port(), output));
  RETURN_IF_ERROR(SerializeBits<kTcpSequenceNumberBitwidth>(
      header.sequence_number(), output));
  RETURN_IF_ERROR(SerializeBits<kTcpAcknowledgementNumberBitwidth>(
      header.acknowledgement_number(), output));
  RETURN_IF_ERROR(
      SerializeBits<kTcpDataOffsetBitwidth>(header.data_offset(), output));
  RETURN_IF_ERROR(
      SerializeBits<kTcpRestOfHeaderBitwidth>(header.rest_of_header(), output));
  if (!header.uninterpreted_options().empty()) {
    RETURN_IF_ERROR(output.AppendHexString(header.uninterpreted_options()));
  }
  return absl::OkStatus();
}

absl::Status SerializeArpHeader(const ArpHeader& header,
                                pdpi::BitString& output) {
  RETURN_IF_ERROR(
      SerializeBits<kArpTypeBitwidth>(header.hardware_type(), output));
  RETURN_IF_ERROR(
      SerializeBits<kArpTypeBitwidth>(header.protocol_type(), output));
  RETURN_IF_ERROR(
      SerializeBits<kArpLengthBitwidth>(header.hardware_length(), output));
  RETURN_IF_ERROR(
      SerializeBits<kArpLengthBitwidth>(header.protocol_length(), output));
  RETURN_IF_ERROR(
      SerializeBits<kArpOperationBitwidth>(header.operation(), output));
  RETURN_IF_ERROR(
      SerializeMacAddress(header.sender_hardware_address(), output));
  RETURN_IF_ERROR(
      SerializeIpv4Address(header.sender_protocol_address(), output));
  RETURN_IF_ERROR(
      SerializeMacAddress(header.target_hardware_address(), output));
  RETURN_IF_ERROR(
      SerializeIpv4Address(header.target_protocol_address(), output));
  return absl::OkStatus();
}

absl::Status SerializeIcmpHeader(const IcmpHeader& header,
                                 pdpi::BitString& output) {
  RETURN_IF_ERROR(SerializeBits<kIcmpTypeBitwidth>(header.type(), output));
  RETURN_IF_ERROR(SerializeBits<kIcmpCodeBitwidth>(header.code(), output));
  RETURN_IF_ERROR(
      SerializeBits<kIcmpChecksumBitwidth>(header.checksum(), output));
  RETURN_IF_ERROR(SerializeBits<kIcmpRestOfHeaderBitwidth>(
      header.rest_of_header(), output));
  return absl::OkStatus();
}

absl::Status SerializeVlanHeader(const VlanHeader& header,
                                 pdpi::BitString& output) {
  RETURN_IF_ERROR(SerializeBits<kVlanPriorityCodePointBitwidth>(
      header.priority_code_point(), output));
  RETURN_IF_ERROR(SerializeBits<kVlanDropEligibilityIndicatorBitwidth>(
      header.drop_eligible_indicator(), output));
  RETURN_IF_ERROR(SerializeBits<kVlanVlanIdentifierBitwidth>(
      header.vlan_identifier(), output));
  RETURN_IF_ERROR(
      SerializeBits<kVlanEthertypeBitwidth>(header.ethertype(), output));
  return absl::OkStatus();
}

absl::Status SerializeGreHeader(const GreHeader& header,
                                pdpi::BitString& output) {
  RETURN_IF_ERROR(SerializeBits<kGreChecksumPresentBitwidth>(
      header.checksum_present(), output));
  RETURN_IF_ERROR(
      SerializeBits<kGreReserved0Bitwidth>(header.reserved0(), output));
  RETURN_IF_ERROR(SerializeBits<kGreVersionBitwidth>(header.version(), output));
  RETURN_IF_ERROR(
      SerializeBits<kGreProtocolTypeBitwidth>(header.protocol_type(), output));
  if (header.checksum_present() == "0x1") {
    RETURN_IF_ERROR(output.AppendHexString(header.checksum()));
    RETURN_IF_ERROR(output.AppendHexString(header.reserved1()));
  }
  return absl::OkStatus();
}

absl::Status SerializeSaiP4BMv2PacketInHeader(
    const SaiP4BMv2PacketInHeader& header, pdpi::BitString& output) {
  RETURN_IF_ERROR(SerializeBits<kSaiP4BMv2PacketInIngressPortBitwidth>(
      header.ingress_port(), output));
  RETURN_IF_ERROR(SerializeBits<kSaiP4BMv2PacketInTargetEgressPortBitwidth>(
      header.target_egress_port(), output));
  RETURN_IF_ERROR(SerializeBits<kSaiP4BMv2PacketInUnusedPadBitwidth>(
      header.unused_pad(), output));
  return absl::OkStatus();
}

absl::Status SerializeIpfixHeader(const IpfixHeader& header,
                                  pdpi::BitString& output) {
  RETURN_IF_ERROR(
      SerializeBits<kIpfixVersionBitwidth>(header.version(), output));
  RETURN_IF_ERROR(SerializeBits<kIpfixLengthBitwidth>(header.length(), output));
  RETURN_IF_ERROR(
      SerializeBits<kIpfixExportTimeBitwidth>(header.export_time(), output));
  RETURN_IF_ERROR(SerializeBits<kIpfixSequenceNumberBitwidth>(
      header.sequence_number(), output));
  RETURN_IF_ERROR(SerializeBits<kIpfixObservationDomainIdBitwidth>(
      header.observation_domain_id(), output));
  return absl::OkStatus();
}

absl::Status SerializePsampHeader(const PsampHeader& header,
                                  pdpi::BitString& output) {
  RETURN_IF_ERROR(
      SerializeBits<kPsampTemplateIdBitwidth>(header.template_id(), output));
  RETURN_IF_ERROR(SerializeBits<kPsampLengthBitwidth>(header.length(), output));
  RETURN_IF_ERROR(SerializeBits<kPsampObservationTimeBitwidth>(
      header.observation_time(), output));
  RETURN_IF_ERROR(
      SerializeBits<kPsampFlowsetBitwidth>(header.flowset(), output));
  RETURN_IF_ERROR(SerializeBits<kPsampNextHopIndexBitwidth>(
      header.next_hop_index(), output));
  RETURN_IF_ERROR(SerializeBits<kPsampEpochBitwidth>(header.epoch(), output));
  RETURN_IF_ERROR(
      SerializeBits<kPsampIngressPortBitwidth>(header.ingress_port(), output));
  RETURN_IF_ERROR(
      SerializeBits<kPsampEgressPortBitwidth>(header.egress_port(), output));
  RETURN_IF_ERROR(SerializeBits<kPsampUserMetaFieldBitwidth>(
      header.user_meta_field(), output));
  RETURN_IF_ERROR(SerializeBits<kPsampDlbIdBitwidth>(header.dlb_id(), output));
  RETURN_IF_ERROR(SerializeBits<kPsampVariableLengthBitwidth>(
      header.variable_length(), output));
  RETURN_IF_ERROR(SerializeBits<kPsampPacketSampledLengthBitwidth>(
      header.packet_sampled_length(), output));
  return absl::OkStatus();
}

absl::Status SerializePspHeader(const PspHeader& header,
                                pdpi::BitString& output) {
  RETURN_IF_ERROR(
      SerializeBits<kPspNextHeaderBitwidth>(header.next_header(), output));
  RETURN_IF_ERROR(SerializeBits<kPspHeaderExtLengthBitwidth>(
      header.header_ext_length(), output));
  RETURN_IF_ERROR(
      SerializeBits<kPspReserved0Bitwidth>(header.reserved0(), output));
  RETURN_IF_ERROR(
      SerializeBits<kPspCryptOffsetBitwidth>(header.crypt_offset(), output));
  RETURN_IF_ERROR(
      SerializeBits<kPspSampleBitwidth>(header.sample_bit(), output));
  RETURN_IF_ERROR(SerializeBits<kPspDropBitwidth>(header.drop_bit(), output));
  RETURN_IF_ERROR(SerializeBits<kPspVersionBitwidth>(header.version(), output));
  RETURN_IF_ERROR(SerializeBits<kPspVirtualizationCookieBitwidth>(
      header.virtualization_cookie_present(), output));
  RETURN_IF_ERROR(
      SerializeBits<kPspReserved1Bitwidth>(header.reserved1(), output));
  RETURN_IF_ERROR(SerializeBits<kPspSecurityParametersIndexBitwidth>(
      header.security_parameters_index(), output));
  RETURN_IF_ERROR(SerializeBits<kPspInitializationVectorBitwidth>(
      header.initialization_vector(), output));
  return absl::OkStatus();
}

absl::Status SerializeHeader(const Header& header, pdpi::BitString& output) {
  switch (header.header_case()) {
    case Header::kEthernetHeader:
      return SerializeEthernetHeader(header.ethernet_header(), output);
    case Header::kIpv4Header:
      return SerializeIpv4Header(header.ipv4_header(), output);
    case Header::kIpv6Header:
      return SerializeIpv6Header(header.ipv6_header(), output);
    case Header::kHopByHopOptionsHeader:
      return SerializeHopByHopOptionsHeader(header.hop_by_hop_options_header(),
                                            output);
    case Header::kUdpHeader:
      return SerializeUdpHeader(header.udp_header(), output);
    case Header::kTcpHeader:
      return SerializeTcpHeader(header.tcp_header(), output);
    case Header::kArpHeader:
      return SerializeArpHeader(header.arp_header(), output);
    case Header::kIcmpHeader:
      return SerializeIcmpHeader(header.icmp_header(), output);
    case Header::kIpfixHeader:
      return SerializeIpfixHeader(header.ipfix_header(), output);
    case Header::kPsampHeader:
      return SerializePsampHeader(header.psamp_header(), output);
    case Header::kVlanHeader:
      return SerializeVlanHeader(header.vlan_header(), output);
    case Header::kGreHeader:
      return SerializeGreHeader(header.gre_header(), output);
    case Header::kSaiP4Bmv2PacketInHeader:
      return SerializeSaiP4BMv2PacketInHeader(
          header.sai_p4_bmv2_packet_in_header(), output);
    case Header::kPspHeader:
      return SerializePspHeader(header.psp_header(), output);
    case Header::HEADER_NOT_SET:
      return gutil::InvalidArgumentErrorBuilder()
             << "Found invalid HEADER_NOT_SET in header.";
  }
}

}  // namespace

absl::Status RawSerializePacket(const Packet& packet, int start_header_index,
                                pdpi::BitString& output) {
  if (start_header_index > packet.headers_size() || start_header_index < 0) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Invalid header index " << start_header_index
           << " for a packet with " << packet.headers_size() << " headers.";
  }

  for (int i = start_header_index; i < packet.headers().size(); ++i) {
    RETURN_IF_ERROR(SerializeHeader(packet.headers(i), output)).SetPrepend()
        << "while trying to serialize packet.headers(" << i << "): ";
  }
  output.AppendBytes(packet.payload());
  return absl::OkStatus();
}

absl::StatusOr<std::string> RawSerializePacket(const Packet& packet) {
  pdpi::BitString bits;
  RETURN_IF_ERROR(RawSerializePacket(packet, 0, bits));
  return bits.ToByteString();
}

absl::StatusOr<std::string> SerializePacket(Packet packet) {
  RETURN_IF_ERROR(PadPacketToMinimumSize(packet).status());
  RETURN_IF_ERROR(UpdateMissingComputedFields(packet).status());
  RETURN_IF_ERROR(ValidatePacket(packet));
  return RawSerializePacket(std::move(packet));
}

absl::StatusOr<std::string> SerializePacket(
    absl::string_view packet_text_proto) {
  ASSIGN_OR_RETURN(Packet packet,
                   gutil::ParseTextProto<Packet>(packet_text_proto));
  return SerializePacket(std::move(packet));
}

// ---- Computed field logic ---------------------------------------------------

absl::StatusOr<bool> UpdateComputedFields(Packet& packet, bool overwrite) {
  bool changes = false;

  // When updating fields we start with the innermost header. This is important
  // for things like checksum computations. For example, IPFIX headers are
  // inside a UDP header and we would want to update IPFIX's length before
  // updating UDP's checksum.
  for (int header_index = packet.headers_size() - 1; header_index >= 0;
       --header_index) {
    Header& header = *packet.mutable_headers(header_index);
    std::string error_prefix =
        absl::StrFormat("%s: failed to compute packet.headers[%d].",
                        HeaderCaseName(header.header_case()), header_index);
    switch (header.header_case()) {
      case Header::kEthernetHeader: {
        EthernetHeader& ethernet_header = *header.mutable_ethernet_header();
        // Read current ethertype.
        int ethertype = 0;
        if (!ethernet_header.ethertype().empty()) {
          ASSIGN_OR_RETURN(ethertype,
                           pdpi::HexStringToInt(ethernet_header.ethertype()));
        }
        // If ethertype <= 1500, it must be equal to the payload size and we
        // thus consider it a computed field that we should update.
        // To avoid surprises, we only perform an update if the ethernet header
        // is the final header, indicating that a size-encoding ethertype is
        // indeed appropriate.
        if ((ethernet_header.ethertype().empty() || overwrite) &&
            ethertype <= 1500 && header_index == packet.headers_size() - 1) {
          if (auto size = PacketSizeInBytes(packet, header_index + 1);
              !size.ok()) {
            return gutil::InvalidArgumentErrorBuilder()
                   << "unable to compute payload size: " << size.status();
          } else if (*size > 1500) {
            return gutil::InvalidArgumentErrorBuilder()
                   << "payload size " << *size << " exceeds MTU";
          } else {
            ethernet_header.set_ethertype(EtherType(*size));
            changes = true;
          }
        }
        break;
      }
      case Header::kIpv4Header: {
        Ipv4Header& ipv4_header = *header.mutable_ipv4_header();
        if (ipv4_header.version().empty() || overwrite) {
          ipv4_header.set_version("0x4");
          changes = true;
        }
        if (ipv4_header.ihl().empty() || overwrite) {
          absl::string_view options = ipv4_header.uninterpreted_options();
          if (options.empty()) {
            ipv4_header.set_ihl("0x5");
            changes = true;
          } else if (absl::ConsumePrefix(&options, "0x") &&
                     (options.size() * 4) % 32 == 0) {
            // 4 bits per hex char.
            int num_32bit_words_in_options = (options.size() * 4) / 32;
            ipv4_header.set_ihl(pdpi::BitsetToHexString<kIpIhlBitwidth>(
                5 + num_32bit_words_in_options));
            changes = true;
          } else {
            return gutil::InvalidArgumentErrorBuilder()
                   << error_prefix
                   << "ihl: uninterpreted_options field is invalid";
          }
        }
        if (ipv4_header.total_length().empty() || overwrite) {
          ASSIGN_OR_RETURN(int size, PacketSizeInBytes(packet, header_index),
                           _.SetPrepend() << error_prefix << "total_length: ");
          ipv4_header.set_total_length(pdpi::BitsetToHexString(
              std::bitset<kIpTotalLengthBitwidth>(size)));
          changes = true;
        }
        if (ipv4_header.checksum().empty() || overwrite) {
          ASSIGN_OR_RETURN(int checksum, Ipv4HeaderChecksum(ipv4_header),
                           _.SetPrepend() << error_prefix << "checksum: ");
          ipv4_header.set_checksum(pdpi::BitsetToHexString(
              std::bitset<kIpChecksumBitwidth>(checksum)));
          changes = true;
        }
        break;
      }
      case Header::kIpv6Header: {
        Ipv6Header& ipv6_header = *header.mutable_ipv6_header();
        if (ipv6_header.version().empty() || overwrite) {
          ipv6_header.set_version("0x6");
          changes = true;
        }
        if (ipv6_header.payload_length().empty() || overwrite) {
          // `+1` to skip the IPv6 header and previous headers in calculation.
          ASSIGN_OR_RETURN(
              int size, PacketSizeInBytes(packet, header_index + 1),
              _.SetPrepend() << error_prefix << "payload_length: ");
          ipv6_header.set_payload_length(pdpi::BitsetToHexString(
              std::bitset<kIpTotalLengthBitwidth>(size)));
          changes = true;
        }
        break;
      }
      case Header::kHopByHopOptionsHeader: {
        if (header.hop_by_hop_options_header()
                .header_extension_length()
                .empty() ||
            overwrite) {
          *header.mutable_hop_by_hop_options_header()
               ->mutable_header_extension_length() = "0x00";
          changes = true;
        }
        std::string* options_and_padding =
            header.mutable_hop_by_hop_options_header()
                ->mutable_options_and_padding();
        if (options_and_padding->empty()) {
          *options_and_padding = "0x010400000000";
          changes = true;
          break;
        }
        // TODO: b/386218372 - Cleanup the computed field logic for hop-by-hop
        // options to overwrite the options and padding to a more strict and
        // correct state.
        if (overwrite) {
          // Adds padding to fill the `options_and_padding` if needed.
          // The maximum bit width for `options_and_padding` is divided by 4 to
          // get the number of bytes. `options_and_padding`'s size is subtracted
          // by 2 to exclude the "0x" characters. We divide the difference
          // between the maximum number of bytes and the number of currently
          // used bytes by 2, since each byte of padding consists of 2 zeroes.
          int num_missing_padding = ((kHopByHopOptionsAndPaddingBitwidth / 4) -
                                     (options_and_padding->size() - 2)) /
                                    2;
          if (num_missing_padding >= 2) {
            // `num_missing_padding` will never exceed 4 so we do not
            // need to worry about bit overflow when performing string
            // concatenation.
            *options_and_padding =
                absl::StrCat(*options_and_padding, "010",
                             std::to_string(num_missing_padding - 2));
            for (int i = 2; i < num_missing_padding; ++i) {
              *options_and_padding = absl::StrCat(*options_and_padding, "00");
            }
          } else if (num_missing_padding == 1) {
            *options_and_padding = absl::StrCat(*options_and_padding, "00");
          }
          changes = true;
        }
        break;
      }
      case Header::kUdpHeader: {
        UdpHeader& udp_header = *header.mutable_udp_header();
        if (udp_header.length().empty() || overwrite) {
          ASSIGN_OR_RETURN(int size, PacketSizeInBytes(packet, header_index),
                           _.SetPrepend() << error_prefix << "length: ");
          udp_header.set_length(
              pdpi::BitsetToHexString(std::bitset<kUdpLengthBitwidth>(size)));
          changes = true;
        }
        if (udp_header.checksum().empty() || overwrite) {
          ASSIGN_OR_RETURN(std::optional<int> checksum,
                           UdpHeaderChecksum(packet, header_index),
                           _.SetPrepend() << error_prefix << "checksum: ");
          // If UdpHeaderChecksum returns a value then we will always use that
          // expected value. If it did not return a value that means the
          // checksum can be anything. So we take into consideration the current
          // header:
          //   * checksum was set then leave it as is.
          //   * checksum is empty then assign it 0.
          if (checksum.has_value()) {
            udp_header.set_checksum(pdpi::BitsetToHexString(
                std::bitset<kUdpChecksumBitwidth>(*checksum)));
            changes = true;
          } else if (udp_header.checksum().empty()) {
            udp_header.set_checksum(UdpChecksum(0));
            changes = true;
          }
        }
        break;
      }
      case Header::kArpHeader: {
        ArpHeader& arp_header = *header.mutable_arp_header();
        if (arp_header.hardware_type().empty() || overwrite) {
          arp_header.set_hardware_type("0x0001");
          changes = true;
        }
        if (arp_header.protocol_type().empty() || overwrite) {
          arp_header.set_protocol_type("0x0800");
          changes = true;
        }
        if (arp_header.hardware_length().empty() || overwrite) {
          arp_header.set_hardware_length("0x06");
          changes = true;
        }
        if (arp_header.protocol_length().empty() || overwrite) {
          arp_header.set_protocol_length("0x04");
          changes = true;
        }
        break;
      }
      case Header::kIcmpHeader: {
        IcmpHeader& icmp_header = *header.mutable_icmp_header();
        if (icmp_header.checksum().empty() || overwrite) {
          ASSIGN_OR_RETURN(int checksum,
                           IcmpHeaderChecksum(packet, header_index));
          icmp_header.set_checksum(pdpi::BitsetToHexString(
              std::bitset<kIcmpChecksumBitwidth>(checksum)));
          changes = true;
        }
        break;
      }
      case Header::kTcpHeader: {
        TcpHeader& tcp_header = *header.mutable_tcp_header();
        if (tcp_header.data_offset().empty() || overwrite) {
          ASSIGN_OR_RETURN(int size, PacketSizeInBits(packet, header_index),
                           _.SetPrepend() << error_prefix << "data_offset: ");
          ASSIGN_OR_RETURN(int payload_size,
                           PacketSizeInBits(packet, header_index + 1),
                           _.SetPrepend() << error_prefix << "data_offset: ");
          int data_offset_in_bits = size - payload_size;
          if (data_offset_in_bits % 32 != 0) {
            return gutil::InvalidArgumentErrorBuilder()
                   << error_prefix << "data_offset: comuted offset of "
                   << data_offset_in_bits
                   << " bits is not a multiple of 32 bits; this indicates that "
                   << "uninterpreted_options is of invalid length";
          }
          int data_offset = data_offset_in_bits / 32;
          if (data_offset < 5 || data_offset > 15) {
            return gutil::InvalidArgumentErrorBuilder()
                   << "data_offset: computed offset of " << data_offset
                   << " is outside of legal range [5, 15]; this indicates that "
                   << "uninterpreted_options is of invalid length";
          }
          tcp_header.set_data_offset(
              pdpi::BitsetToHexString<kTcpDataOffsetBitwidth>(data_offset));
          changes = true;
        }
        break;
      }
      case Header::kGreHeader: {
        GreHeader& gre_header = *header.mutable_gre_header();
        if (gre_header.checksum_present() == "0x1") {
          if (gre_header.checksum().empty() || overwrite) {
            ASSIGN_OR_RETURN(int checksum,
                             GreHeaderChecksum(packet, header_index));
            gre_header.set_checksum(pdpi::BitsetToHexString(
                std::bitset<kGreChecksumBitwidth>(checksum)));
            changes = true;
          }
          if (gre_header.reserved1().empty() || overwrite) {
            gre_header.set_reserved1("0x0000");
            changes = true;
          }
        }
        break;
      }
      case Header::kSaiP4Bmv2PacketInHeader:
        break;
      case Header::kIpfixHeader: {
        IpfixHeader& ipfix_header = *header.mutable_ipfix_header();
        if (ipfix_header.length().empty() || overwrite) {
          ASSIGN_OR_RETURN(int size, PacketSizeInBytes(packet, header_index),
                           _.SetPrepend() << error_prefix << "length: ");
          ipfix_header.set_length(
              pdpi::BitsetToHexString(std::bitset<kIpfixLengthBitwidth>(size)));
          changes = true;
        }
        break;
      }
      case Header::kPsampHeader: {
        PsampHeader& psamp_header = *header.mutable_psamp_header();
        if (psamp_header.length().empty() || overwrite) {
          ASSIGN_OR_RETURN(int size, PacketSizeInBytes(packet, header_index),
                           _.SetPrepend() << error_prefix << "length: ");
          psamp_header.set_length(
              pdpi::BitsetToHexString(std::bitset<kPsampLengthBitwidth>(size)));
          changes = true;
        }
        if (psamp_header.variable_length().empty() || overwrite) {
          psamp_header.set_variable_length("0xff");
          changes = true;
        }
        if (psamp_header.packet_sampled_length().empty() || overwrite) {
          ASSIGN_OR_RETURN(
              int size, PacketSizeInBytes(packet, header_index + 1),
              _.SetPrepend() << error_prefix << "packet_sampled_length: ");
          psamp_header.set_packet_sampled_length(pdpi::BitsetToHexString(
              std::bitset<kPsampPacketSampledLengthBitwidth>(size)));
          changes = true;
        }
        break;
      }
      case Header::kVlanHeader:
      case Header::kPspHeader: {
        // No computed fields.
        break;
      }
      case Header::HEADER_NOT_SET:
        return gutil::InvalidArgumentErrorBuilder()
               << "Invalid packet with HEADER_NOT_SET: "
               << packet.DebugString();
    }
  }

  return changes;
}

absl::StatusOr<bool> UpdateMissingComputedFields(Packet& packet) {
  return UpdateComputedFields(packet, /*overwrite=*/false);
}

absl::StatusOr<bool> UpdateAllComputedFields(Packet& packet) {
  return UpdateComputedFields(packet, /*overwrite=*/true);
}

absl::StatusOr<bool> PadPacketToMinimumSizeFromHeaderIndex(Packet& packet,
                                                           int header_index) {
  if (packet.headers().size() <= header_index) return false;
  switch (packet.headers(header_index).header_case()) {
    case Header::kEthernetHeader: {
      if (auto after_eth_size = PacketSizeInBytes(packet, header_index + 1);
          !after_eth_size.ok()) {
        return gutil::InvalidArgumentErrorBuilder()
               << "couldn't compute packet size: " << after_eth_size.status();
      } else {
        if (*after_eth_size >= kMinNumBytesInEthernetPayload) return false;
        int target_payload_size = kMinNumBytesInEthernetPayload -
                                  (*after_eth_size - packet.payload().size());
        packet.mutable_payload()->resize(target_payload_size);
        return true;
      }
    }
    case Header::kIpv4Header:
    case Header::kIpv6Header:
    case Header::kHopByHopOptionsHeader:
    case Header::kUdpHeader:
    case Header::kTcpHeader:
    case Header::kArpHeader:
    case Header::kIcmpHeader:
    case Header::kVlanHeader:
    case Header::kGreHeader:
    case Header::kSaiP4Bmv2PacketInHeader:
    case Header::kIpfixHeader:
    case Header::kPsampHeader:
    case Header::kPspHeader:
      return PadPacketToMinimumSizeFromHeaderIndex(packet, header_index + 1);
    case Header::HEADER_NOT_SET:
      return false;
  }
  LOG(DFATAL) << "exhaustive switch statement failed: " << packet.DebugString();
  return false;
}

absl::StatusOr<bool> PadPacketToMinimumSize(Packet& packet) {
  return PadPacketToMinimumSizeFromHeaderIndex(packet, 0);
}

absl::StatusOr<bool> PadPacket(int num_bytes, Packet& packet) {
  ASSIGN_OR_RETURN(int current_size, PacketSizeInBytes(packet));
  if (current_size >= num_bytes) return false;
  int header_size = current_size - packet.payload().size();
  int target_payload_size = num_bytes - header_size;
  packet.mutable_payload()->resize(target_payload_size);
  return true;
}

absl::StatusOr<int> PacketSizeInBytes(const Packet& packet,
                                      int start_header_index) {
  ASSIGN_OR_RETURN(int bit_size, PacketSizeInBits(packet, start_header_index));
  if (bit_size % 8 != 0) {
    return gutil::InvalidArgumentErrorBuilder()
           << "packet size of " << bit_size << " cannot be converted to bytes";
  }
  return bit_size / 8;
}

absl::StatusOr<int> PacketSizeInBits(const Packet& packet,
                                     int start_header_index) {
  if (start_header_index > packet.headers_size() || start_header_index < 0) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Invalid header index " << start_header_index
           << " for a packet with " << packet.headers_size() << " headers.";
  }

  int size = 0;

  for (auto* header :
       absl::MakeSpan(packet.headers()).subspan(start_header_index)) {
    switch (header->header_case()) {
      case Header::kEthernetHeader:
        size += kEthernetHeaderBitwidth;
        break;
      case Header::kIpv4Header: {
        size += kStandardIpv4HeaderBitwidth;
        if (const auto& options = header->ipv4_header().uninterpreted_options();
            !options.empty()) {
          ASSIGN_OR_RETURN(
              auto bytes, pdpi::HexStringToByteString(options),
              _.SetPrepend()
                  << "failed to parse uninterpreted_options in Ipv4Header: ");
          size += 8 * bytes.size();
        }
        break;
      }
      case Header::kIpv6Header:
        size += kIpv6HeaderBitwidth;
        break;
      case Header::kHopByHopOptionsHeader:
        size += kMinHopByHopOptionsHeaderBitwidth;
        break;
      case Header::kUdpHeader:
        size += kUdpHeaderBitwidth;
        break;
      case Header::kTcpHeader: {
        size += kStandardTcpHeaderBitwidth;
        if (const auto& options = header->tcp_header().uninterpreted_options();
            !options.empty()) {
          ASSIGN_OR_RETURN(
              auto bytes, pdpi::HexStringToByteString(options),
              _.SetPrepend()
                  << "failed to parse uninterpreted_options in TcpHeader: ");
          size += 8 * bytes.size();
        }
        break;
      }
      case Header::kArpHeader:
        size += kArpHeaderBitwidth;
        break;
      case Header::kIcmpHeader:
        size += kIcmpHeaderBitwidth;
        break;
      case Header::kVlanHeader:
        size += kVlanHeaderBitwidth;
        break;
      case Header::kGreHeader:
        size += kRfc2784GreHeaderWithoutOptionalsBitwidth;
        if (header->gre_header().checksum_present() == "0x1") {
          size += kGreChecksumBitwidth + kGreReserved1Bitwidth;
        }
        break;
      case Header::kSaiP4Bmv2PacketInHeader:
        size += kSaiP4BMv2PacketInHeaderBitwidth;
        break;
      case Header::kIpfixHeader:
        size += kIpfixHeaderBitwidth;
        break;
      case Header::kPsampHeader:
        size += kPsampHeaderBitwidth;
        break;
      case Header::kPspHeader:
        size += kPspHeaderBitwidth;
        break;
      case Header::HEADER_NOT_SET:
        return gutil::InvalidArgumentErrorBuilder()
               << "Found invalid HEADER_NOT_SET in header.";
    }
  }

  size += 8 * packet.payload().size();
  return size;
}

// Returns 16-bit ones' complement of the ones' complement sum of all 16-bit
// words in the given BitString.
static absl::StatusOr<int> OnesComplementChecksum(pdpi::BitString data) {
  // Pad string to be 16-bit multiple.
  while (data.size() % 16 != 0) data.AppendBit(0);

  // Following RFC 1071 and
  // wikipedia.org/wiki/IPv4_header_checksum#Calculating_the_IPv4_header_checksum
  int sum = 0;
  while (data.size() != 0) {
    ASSIGN_OR_RETURN(std::bitset<16> word, data.ConsumeBitset<16>(),
                     _.SetCode(absl::StatusCode::kInternal));
    // This looks wrong because we're not taking the ones' complement, but
    // turns out to work.
    sum += word.to_ulong();
  }
  // Add carry bits until sum fits into 16 bits.
  while (sum >> 16 != 0) {
    sum = (sum & 0xffff) + (sum >> 16);
  }
  // Return 16 bit ones' complement.
  return (~sum) & 0xffff;
}

absl::StatusOr<int> Ipv4HeaderChecksum(Ipv4Header header) {
  // The checksum field is the 16-bit ones' complement of the ones' complement
  // sum of all 16-bit words in the header. For purposes of computing the
  // checksum, the value of the checksum field is zero.

  // We compute the checksum by setting the checksum field to 0, serializing
  // the header, and then going over all 16-bit words.
  header.set_checksum("0x0000");
  pdpi::BitString data;
  RETURN_IF_ERROR(SerializeIpv4Header(header, data));
  return OnesComplementChecksum(std::move(data));
}

absl::StatusOr<std::optional<int>> UdpHeaderChecksum(Packet packet,
                                                     int udp_header_index) {
  if (udp_header_index < 1) {
    return absl::InvalidArgumentError(
        absl::StrFormat("UDP header must be preceded by an IP or PSP header, "
                        "but no header was found"));
  }
  if (udp_header_index >= packet.headers().size()) {
    return absl::InvalidArgumentError(
        absl::StrFormat("UDP header index %d is too large for the packet which "
                        "only has %d header(s).",
                        udp_header_index, packet.headers().size()));
  }

  int ip_header_index = FindPrecedingIpHeader(packet, udp_header_index);
  const Header& preceding_header = packet.headers(ip_header_index);
  if (auto header_case = packet.headers(udp_header_index).header_case();
      header_case != Header::kUdpHeader) {
    return gutil::InvalidArgumentErrorBuilder()
           << "UdpHeaderChecksum(packet, udp_header_index = "
           << udp_header_index << "): packet.headers[" << udp_header_index
           << "] is a " << HeaderCaseName(header_case)
           << ", expected UdpHeader";
  }
  UdpHeader& udp_header =
      *packet.mutable_headers(udp_header_index)->mutable_udp_header();

  // Serialize "pseudo header" for checksum calculation, following
  // https://en.wikipedia.org/wiki/User_Datagram_Protocol#Checksum_computation.
  pdpi::BitString data;
  switch (preceding_header.header_case()) {
    case Header::kIpv4Header: {
      udp_header.set_checksum("0x0000");
      auto& header = preceding_header.ipv4_header();
      RETURN_IF_ERROR(SerializeIpv4Address(header.ipv4_source(), data));
      RETURN_IF_ERROR(SerializeIpv4Address(header.ipv4_destination(), data));
      data.AppendBits<8>(0);
      RETURN_IF_ERROR(
          SerializeBits<kIpProtocolBitwidth>(header.protocol(), data));
      RETURN_IF_ERROR(
          SerializeBits<kUdpLengthBitwidth>(udp_header.length(), data));
      break;
    }
    case Header::kIpv6Header: {
      udp_header.set_checksum("0x0000");
      auto& header = preceding_header.ipv6_header();
      RETURN_IF_ERROR(SerializeIpv6Address(header.ipv6_source(), data));
      RETURN_IF_ERROR(SerializeIpv6Address(header.ipv6_destination(), data));
      data.AppendBits<16>(0);
      RETURN_IF_ERROR(
          SerializeBits<kUdpLengthBitwidth>(udp_header.length(), data));
      data.AppendBits<24>(0);

      // The `next_header` field for a UDP header identifies the upper-layer
      // protocol. It differs from the typical `next_header` field in an IPv6
      // header when there are IPV6 extension headers. See
      // https://datatracker.ietf.org/doc/html/rfc2460#section-8.1, which
      // specifies that the `next_header` field for a UDP header must be 17
      // (0x11). Note that the `next_header` field can be 6 (0x06) to denote a
      // TCP header.
      RETURN_IF_ERROR(SerializeBits<kIpNextHeaderBitwidth>("0x11", data));
      break;
    }
    case Header::kPspHeader: {
      return std::nullopt;
    }
    default:
      return absl::InvalidArgumentError(absl::StrFormat(
          "UDP header must be preceded by an IP or PSP header, but got %s",
          HeaderCaseName(preceding_header.header_case())));
  }
  RETURN_IF_ERROR(RawSerializePacket(packet, udp_header_index, data));
  return OnesComplementChecksum(std::move(data));
}

absl::StatusOr<int> IcmpHeaderChecksum(Packet packet, int icmp_header_index) {
  auto invalid_argument = gutil::InvalidArgumentErrorBuilder()
                          << "IcmpHeaderChecksum(packet, icmp_header_index = "
                          << icmp_header_index << "): ";
  if (icmp_header_index < 1 || icmp_header_index >= packet.headers().size()) {
    return invalid_argument
           << "icmp_header_index must be in [1, " << packet.headers().size()
           << ") since the given packet has " << packet.headers().size()
           << " headers and the ICMP header must be preceded by an IP header";
  }
  if (auto header_case = packet.headers(icmp_header_index).header_case();
      header_case != Header::kIcmpHeader) {
    return invalid_argument << "packet.headers[" << icmp_header_index
                            << "] is a " << HeaderCaseName(header_case)
                            << ", expected IcmpHeader";
  }

  IcmpHeader& icmp_header =
      *packet.mutable_headers(icmp_header_index)->mutable_icmp_header();
  icmp_header.set_checksum("0x0000");

  int ip_header_index = FindPrecedingIpHeader(packet, icmp_header_index);
  const Header& preceding_header = packet.headers(ip_header_index);
  pdpi::BitString data;
  switch (preceding_header.header_case()) {
    case Header::kIpv6Header: {
      // Serialize "pseudo header" for checksum calculation, following
      // https://en.wikipedia.org/wiki/Internet_Control_Message_Protocol_for_IPv6#Checksum.
      auto& header = preceding_header.ipv6_header();
      RETURN_IF_ERROR(SerializeIpv6Address(header.ipv6_source(), data));
      RETURN_IF_ERROR(SerializeIpv6Address(header.ipv6_destination(), data));
      ASSIGN_OR_RETURN(int icmpv6_size,
                       PacketSizeInBytes(packet, icmp_header_index));
      data.AppendBits<32>(icmpv6_size);
      data.AppendBits<24>(0);
      // The `next_header` field for a ICMP header identifies the upper-layer
      // protocol. It differs from the typical `next_header` field in an IPv6
      // header when there are IPV6 extension headers. See
      // https://datatracker.ietf.org/doc/html/rfc2463#section-2.3, which
      // specifies that the `next_header` field for a ICMP header must be 58
      // (0x3a).
      RETURN_IF_ERROR(SerializeBits<kIpNextHeaderBitwidth>("0x3a", data));
      break;
    }
    case Header::kIpv4Header: {
      // For ICMPv4, only the ICMP header and payload is used in the checksum
      // calculation.
      break;
    }
    default:
      return invalid_argument << "expected packet.headers[udp_header_index - "
                                 "1] to be an IP header, got "
                              << HeaderCaseName(preceding_header.header_case());
  }
  RETURN_IF_ERROR(RawSerializePacket(packet, icmp_header_index, data));
  return OnesComplementChecksum(std::move(data));
}

absl::StatusOr<int> GreHeaderChecksum(Packet packet, int gre_header_index) {
  auto invalid_argument = gutil::InvalidArgumentErrorBuilder()
                          << "GreHeaderChecksum(packet, gre_header_index = "
                          << gre_header_index << "): ";
  if (gre_header_index >= packet.headers().size()) {
    return invalid_argument
           << "gre_header_index must be in [0, " << packet.headers().size()
           << ") since the given packet has " << packet.headers().size()
           << " headers.";
  }
  if (auto header_case = packet.headers(gre_header_index).header_case();
      header_case != Header::kGreHeader) {
    return invalid_argument << "packet.headers[" << gre_header_index
                            << "] is a " << HeaderCaseName(header_case)
                            << ", expected GreHeader";
  }
  GreHeader& gre_header =
      *packet.mutable_headers(gre_header_index)->mutable_gre_header();

  gre_header.set_checksum("0x0000");
  pdpi::BitString data;

  RETURN_IF_ERROR(RawSerializePacket(packet, gre_header_index, data));

  return OnesComplementChecksum(std::move(data));
}

std::string EtherType(uint32_t ether_type) {
  return ValidateAndConvertToHexString<kEthernetEthertypeBitwidth>(ether_type);
}

std::string VlanId(uint32_t vlan_id) {
  return ValidateAndConvertToHexString<kVlanVlanIdentifierBitwidth>(vlan_id);
}

std::string IpVersion(uint32_t version) {
  return ValidateAndConvertToHexString<kIpVersionBitwidth>(version);
}

std::string IpIhl(uint32_t ihl) {
  return ValidateAndConvertToHexString<kIpIhlBitwidth>(ihl);
}

std::string IpDscp(uint32_t dscp) {
  return ValidateAndConvertToHexString<kIpDscpBitwidth>(dscp);
}

std::string IpEcn(uint32_t ecn) {
  return ValidateAndConvertToHexString<kIpEcnBitwidth>(ecn);
}

std::string IpTotalLength(uint32_t total_length) {
  return ValidateAndConvertToHexString<kIpTotalLengthBitwidth>(total_length);
}

std::string IpIdentification(uint32_t identification) {
  return ValidateAndConvertToHexString<kIpIdentificationBitwidth>(
      identification);
}

std::string IpFlags(uint32_t flag) {
  return ValidateAndConvertToHexString<kIpFlagsBitwidth>(flag);
}

std::string IpFragmentOffset(uint32_t fragment_offset) {
  return ValidateAndConvertToHexString<kIpFragmentOffsetBitwidth>(
      fragment_offset);
}

std::string IpTtl(uint32_t ttl) {
  return ValidateAndConvertToHexString<kIpTtlBitwidth>(ttl);
}

std::string IpProtocol(uint32_t protocol) {
  return ValidateAndConvertToHexString<kIpProtocolBitwidth>(protocol);
}

std::string IpChecksum(uint32_t checksum) {
  return ValidateAndConvertToHexString<kIpChecksumBitwidth>(checksum);
}

std::string IpFlowLabel(uint32_t flow_label) {
  return ValidateAndConvertToHexString<kIpFlowLabelBitwidth>(flow_label);
}

std::string IpPayloadLength(uint32_t payload_length) {
  return ValidateAndConvertToHexString<kIpPayloadLengthBitwidth>(
      payload_length);
}

std::string IpNextHeader(uint32_t next_header) {
  return ValidateAndConvertToHexString<kIpNextHeaderBitwidth>(next_header);
}

std::string IpHopLimit(uint32_t hop_limit) {
  return ValidateAndConvertToHexString<kIpHopLimitBitwidth>(hop_limit);
}

std::string UdpPort(uint32_t udp_port) {
  return ValidateAndConvertToHexString<kUdpPortBitwidth>(udp_port);
}

std::string UdpChecksum(uint32_t checksum) {
  return ValidateAndConvertToHexString<kUdpChecksumBitwidth>(checksum);
}

std::string UdpLength(uint32_t udp_length) {
  return ValidateAndConvertToHexString<kUdpLengthBitwidth>(udp_length);
}

std::string TcpPort(uint32_t tcp_port) {
  return ValidateAndConvertToHexString<kTcpPortBitwidth>(tcp_port);
}

std::string TcpSequenceNumber(uint32_t sequence_number) {
  return ValidateAndConvertToHexString<kTcpSequenceNumberBitwidth>(
      sequence_number);
}

std::string TcpAcknowledgementNumber(uint32_t ackowledgement_number) {
  return ValidateAndConvertToHexString<kTcpAcknowledgementNumberBitwidth>(
      ackowledgement_number);
}

std::string TcpDataOffset(uint32_t data_offset) {
  return ValidateAndConvertToHexString<kTcpDataOffsetBitwidth>(data_offset);
}

std::string TcpRestOfHeader(uint64_t rest_of_header) {
  return ValidateAndConvertToHexString<kTcpRestOfHeaderBitwidth>(
      rest_of_header);
}

std::string ArpType(uint32_t type) {
  return ValidateAndConvertToHexString<kArpTypeBitwidth>(type);
}

std::string ArpLength(uint32_t length) {
  return ValidateAndConvertToHexString<kArpLengthBitwidth>(length);
}

std::string ArpOperation(uint32_t operation) {
  return ValidateAndConvertToHexString<kArpOperationBitwidth>(operation);
}

std::string IcmpType(uint32_t type) {
  return ValidateAndConvertToHexString<kIcmpTypeBitwidth>(type);
}

std::string IcmpCode(uint32_t code) {
  return ValidateAndConvertToHexString<kIcmpCodeBitwidth>(code);
}

std::string IcmpChecksum(uint32_t checksum) {
  return ValidateAndConvertToHexString<kIcmpChecksumBitwidth>(checksum);
}

std::string IcmpRestOfHeader(uint32_t rest_of_header) {
  return ValidateAndConvertToHexString<kIcmpRestOfHeaderBitwidth>(
      rest_of_header);
}

std::string GreChecksumPresent(uint32_t checksum_present) {
  return ValidateAndConvertToHexString<kGreChecksumPresentBitwidth>(
      checksum_present);
}

std::string GreReserved0(uint32_t reserved0) {
  return ValidateAndConvertToHexString<kGreReserved0Bitwidth>(reserved0);
}

std::string GreVersion(uint32_t version) {
  return ValidateAndConvertToHexString<kGreVersionBitwidth>(version);
}

std::string GreProtocolType(uint32_t protocol_type) {
  return ValidateAndConvertToHexString<kGreProtocolTypeBitwidth>(protocol_type);
}

std::string GreChecksum(uint32_t checksum) {
  return ValidateAndConvertToHexString<kGreChecksumBitwidth>(checksum);
}

std::string GreReserved1(uint32_t reserved1) {
  return ValidateAndConvertToHexString<kGreReserved1Bitwidth>(reserved1);
}

std::string IpfixVersion(uint32_t version) {
  return ValidateAndConvertToHexString<kIpfixVersionBitwidth>(version);
}

std::string IpfixLength(uint32_t length) {
  return ValidateAndConvertToHexString<kIpfixLengthBitwidth>(length);
}

std::string IpfixExportTime(uint32_t exported_time) {
  return ValidateAndConvertToHexString<kIpfixExportTimeBitwidth>(exported_time);
}

std::string IpfixSequenceNumber(uint32_t sequence_number) {
  return ValidateAndConvertToHexString<kIpfixSequenceNumberBitwidth>(
      sequence_number);
}

std::string IpfixObservationDomainId(uint32_t observation_domain_id) {
  return ValidateAndConvertToHexString<kIpfixObservationDomainIdBitwidth>(
      observation_domain_id);
}

std::string PsampTemplateId(uint32_t template_id) {
  return ValidateAndConvertToHexString<kPsampTemplateIdBitwidth>(template_id);
}

std::string PsampObservationTime(uint64_t observation_time) {
  return ValidateAndConvertToHexString<kPsampObservationTimeBitwidth>(
      observation_time);
}

std::string PsampFlowset(uint32_t flowset) {
  return ValidateAndConvertToHexString<kPsampFlowsetBitwidth>(flowset);
}

std::string PsampNextHopIndex(uint32_t next_hop_index) {
  return ValidateAndConvertToHexString<kPsampNextHopIndexBitwidth>(
      next_hop_index);
}

std::string PsampEpoch(uint32_t epoch) {
  return ValidateAndConvertToHexString<kPsampEpochBitwidth>(epoch);
}

std::string PsampIngressPort(uint32_t ingress_port) {
  return ValidateAndConvertToHexString<kPsampIngressPortBitwidth>(ingress_port);
}

std::string PsampEgressPort(uint32_t egress_port) {
  return ValidateAndConvertToHexString<kPsampEgressPortBitwidth>(egress_port);
}

std::string PsampUserMetaField(uint32_t user_meta_field) {
  return ValidateAndConvertToHexString<kPsampUserMetaFieldBitwidth>(
      user_meta_field);
}

std::string PsampDlbId(uint32_t dlb_id) {
  return ValidateAndConvertToHexString<kPsampDlbIdBitwidth>(dlb_id);
}
}  // namespace packetlib
