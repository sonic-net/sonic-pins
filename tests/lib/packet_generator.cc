// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "tests/lib/packet_generator.h"

#include <netinet/in.h>

#include <algorithm>
#include <bitset>
#include <cstdint>
#include <limits>
#include <random>
#include <string>
#include <vector>

#include "absl/container/btree_set.h"
#include "absl/numeric/int128.h"
#include "absl/random/distributions.h"
#include "absl/status/status.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "glog/logging.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status.h"
#include "p4_infra/p4_pdpi/netaddr/ipv4_address.h"
#include "p4_infra/p4_pdpi/netaddr/ipv6_address.h"
#include "p4_infra/p4_pdpi/netaddr/mac_address.h"
#include "p4_infra/p4_pdpi/packetlib/bit_widths.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.pb.h"

namespace pins_test {
namespace packetgen {
namespace {

// Minimum number of TTL / HopLimit allowed for a generated packet. Any fewer
// may cause the packet to not return back to the control switch.
constexpr int kMinHops = 3;

template <typename Proto>
Proto ParseTextProtoOrDie(absl::string_view text) {
  auto proto = gutil::ParseTextProto<Proto>(text);
  if (!proto.ok()) {
    LOG(FATAL) << proto.status();  // Crash OK
  }
  return std::move(*proto);
}

const packetlib::EthernetHeader& DefaultEthernetHeader() {
  static const auto* const kHeader = new packetlib::EthernetHeader(
      ParseTextProtoOrDie<packetlib::EthernetHeader>(R"pb(
        ethernet_source: "00:00:00:00:00:7B"
        ethernet_destination: "00:00:00:10:02:34"
      )pb"));
  return *kHeader;
}

const packetlib::Ipv4Header& DefaultIpv4Header() {
  static const auto* const kHeader =
      new packetlib::Ipv4Header(ParseTextProtoOrDie<packetlib::Ipv4Header>(R"pb(
        ihl: "0x5"
        ipv4_source: "10.2.3.4"
        ipv4_destination: "10.3.4.5"
        ttl: "0x20"  # 32
        dscp: "0x0A"
        ecn: "0x0"
        identification: "0x0000"
        flags: "0x0"
        fragment_offset: "0x0000"
      )pb"));
  return *kHeader;
}

const packetlib::Ipv6Header& DefaultIpv6Header() {
  static const auto* const kHeader =
      new packetlib::Ipv6Header(ParseTextProtoOrDie<packetlib::Ipv6Header>(R"pb(
        ipv6_source: "0001:0002:0003:0004::"
        ipv6_destination: "0002:0003:0004:0005::"
        hop_limit: "0x20"  # 32
        dscp: "0x0A"
        ecn: "0x0"
        flow_label: "0x00000"
      )pb"));
  return *kHeader;
}

const packetlib::Ipv4Header& DefaultInnerIpv4Header() {
  static const auto* const kHeader =
      new packetlib::Ipv4Header(ParseTextProtoOrDie<packetlib::Ipv4Header>(R"pb(
        ihl: "0x5"
        ipv4_source: "10.4.5.6"
        ipv4_destination: "10.5.6.7"
        ttl: "0x21"  # 33
        dscp: "0x0B"
        ecn: "0x0"
        identification: "0x0000"
        flags: "0x0"
        fragment_offset: "0x0000"
      )pb"));
  return *kHeader;
}

const packetlib::Ipv6Header& DefaultInnerIpv6Header() {
  static const auto* const kHeader =
      new packetlib::Ipv6Header(ParseTextProtoOrDie<packetlib::Ipv6Header>(R"pb(
        ipv6_source: "0003:0004:0005:0006::"
        ipv6_destination: "0004:0005:0006:0007::"
        hop_limit: "0x21"  # 33
        dscp: "0x0B"
        ecn: "0x0"
        flow_label: "0x00000"
      )pb"));
  return *kHeader;
}

const packetlib::UdpHeader& DefaultUdpHeader() {
  static const auto* const kHeader =
      new packetlib::UdpHeader(ParseTextProtoOrDie<packetlib::UdpHeader>(R"pb(
        source_port: "0x0929"       # 2345
        destination_port: "0x11D7"  # 4567
      )pb"));
  return *kHeader;
}

packetlib::Packet DefaultIpv4Packet() {
  packetlib::Packet packet;
  {
    packetlib::EthernetHeader l2_header = DefaultEthernetHeader();
    l2_header.set_ethertype(packetlib::EtherType(ETHERTYPE_IP));
    *packet.add_headers()->mutable_ethernet_header() = l2_header;
  }
  {
    packetlib::Ipv4Header l3_header = DefaultIpv4Header();
    l3_header.set_protocol(packetlib::IpProtocol(IPPROTO_UDP));
    *packet.add_headers()->mutable_ipv4_header() = l3_header;
  }
  *packet.add_headers()->mutable_udp_header() = DefaultUdpHeader();
  return packet;
}

packetlib::Packet DefaultIpv6Packet() {
  packetlib::Packet packet;
  {
    packetlib::EthernetHeader l2_header = DefaultEthernetHeader();
    l2_header.set_ethertype(packetlib::EtherType(ETHERTYPE_IPV6));
    *packet.add_headers()->mutable_ethernet_header() = l2_header;
  }
  {
    packetlib::Ipv6Header l3_header = DefaultIpv6Header();
    l3_header.set_next_header(packetlib::IpNextHeader(IPPROTO_UDP));
    *packet.add_headers()->mutable_ipv6_header() = l3_header;
  }
  *packet.add_headers()->mutable_udp_header() = DefaultUdpHeader();
  return packet;
}

packetlib::Packet Default4In4Packet() {
  packetlib::Packet packet;
  {
    packetlib::EthernetHeader l2_header = DefaultEthernetHeader();
    l2_header.set_ethertype(packetlib::EtherType(ETHERTYPE_IP));
    *packet.add_headers()->mutable_ethernet_header() = l2_header;
  }
  {
    packetlib::Ipv4Header l3_header = DefaultIpv4Header();
    l3_header.set_protocol(packetlib::IpProtocol(IPPROTO_IPIP));
    *packet.add_headers()->mutable_ipv4_header() = l3_header;
  }
  {
    packetlib::Ipv4Header inner_l3_header = DefaultInnerIpv4Header();
    inner_l3_header.set_protocol(packetlib::IpProtocol(IPPROTO_UDP));
    *packet.add_headers()->mutable_ipv4_header() = inner_l3_header;
  }
  *packet.add_headers()->mutable_udp_header() = DefaultUdpHeader();
  return packet;
}

packetlib::Packet Default6In4Packet() {
  packetlib::Packet packet;
  {
    packetlib::EthernetHeader l2_header = DefaultEthernetHeader();
    l2_header.set_ethertype(packetlib::EtherType(ETHERTYPE_IP));
    *packet.add_headers()->mutable_ethernet_header() = l2_header;
  }
  {
    packetlib::Ipv4Header l3_header = DefaultIpv4Header();
    l3_header.set_protocol(packetlib::IpProtocol(IPPROTO_IPV6));
    *packet.add_headers()->mutable_ipv4_header() = l3_header;
  }
  {
    packetlib::Ipv6Header inner_l3_header = DefaultInnerIpv6Header();
    inner_l3_header.set_next_header(packetlib::IpNextHeader(IPPROTO_UDP));
    *packet.add_headers()->mutable_ipv6_header() = inner_l3_header;
  }
  *packet.add_headers()->mutable_udp_header() = DefaultUdpHeader();
  return packet;
}

packetlib::Packet Default4In6Packet() {
  packetlib::Packet packet;
  {
    packetlib::EthernetHeader l2_header = DefaultEthernetHeader();
    l2_header.set_ethertype(packetlib::EtherType(ETHERTYPE_IPV6));
    *packet.add_headers()->mutable_ethernet_header() = l2_header;
  }
  {
    packetlib::Ipv6Header l3_header = DefaultIpv6Header();
    l3_header.set_next_header(packetlib::IpNextHeader(IPPROTO_IPIP));
    *packet.add_headers()->mutable_ipv6_header() = l3_header;
  }
  {
    packetlib::Ipv4Header inner_l3_header = DefaultInnerIpv4Header();
    inner_l3_header.set_protocol(packetlib::IpProtocol(IPPROTO_UDP));
    *packet.add_headers()->mutable_ipv4_header() = inner_l3_header;
  }
  *packet.add_headers()->mutable_udp_header() = DefaultUdpHeader();
  return packet;
}

packetlib::Packet Default6In6Packet() {
  packetlib::Packet packet;
  {
    packetlib::EthernetHeader l2_header = DefaultEthernetHeader();
    l2_header.set_ethertype(packetlib::EtherType(ETHERTYPE_IPV6));
    *packet.add_headers()->mutable_ethernet_header() = l2_header;
  }
  {
    packetlib::Ipv6Header l3_header = DefaultIpv6Header();
    l3_header.set_next_header(packetlib::IpNextHeader(IPPROTO_IPV6));
    *packet.add_headers()->mutable_ipv6_header() = l3_header;
  }
  {
    packetlib::Ipv6Header inner_l3_header = DefaultInnerIpv6Header();
    inner_l3_header.set_next_header(packetlib::IpNextHeader(IPPROTO_UDP));
    *packet.add_headers()->mutable_ipv6_header() = inner_l3_header;
  }
  *packet.add_headers()->mutable_udp_header() = DefaultUdpHeader();
  return packet;
}

packetlib::Packet DefaultPacket(const Options& options) {
  switch (options.ip_type) {
    case IpType::kIpv4:
      if (!options.inner_ip_type.has_value()) return DefaultIpv4Packet();
      switch (*options.inner_ip_type) {
        case IpType::kIpv4:
          return Default4In4Packet();
        case IpType::kIpv6:
          return Default6In4Packet();
      }
    case IpType::kIpv6:
      if (!options.inner_ip_type.has_value()) return DefaultIpv6Packet();
      switch (*options.inner_ip_type) {
        case IpType::kIpv4:
          return Default4In6Packet();
        case IpType::kIpv6:
          return Default6In6Packet();
      }
  }
  return packetlib::Packet();
}

// Header lookup for the test packet only. Assume one of the following layouts.
// * <Ethernet> | <ipv4/ipv6> | <udp>
// * <Ethernet> | <ipv4/ipv6> | <inner ipv4/ipv6> | <udp>
packetlib::EthernetHeader& EthernetHeader(packetlib::Packet& packet) {
  return *packet.mutable_headers(0)->mutable_ethernet_header();
}
packetlib::Ipv4Header& Ipv4Header(packetlib::Packet& packet) {
  return *packet.mutable_headers(1)->mutable_ipv4_header();
}
packetlib::Ipv6Header& Ipv6Header(packetlib::Packet& packet) {
  return *packet.mutable_headers(1)->mutable_ipv6_header();
}
packetlib::Ipv4Header& InnerIpv4Header(packetlib::Packet& packet) {
  return *packet.mutable_headers(2)->mutable_ipv4_header();
}
packetlib::Ipv6Header& InnerIpv6Header(packetlib::Packet& packet) {
  return *packet.mutable_headers(2)->mutable_ipv6_header();
}
packetlib::UdpHeader& UdpHeader(packetlib::Packet& packet) {
  return *packet.mutable_headers()->rbegin()->mutable_udp_header();
}
IpType OuterIpHeaderType(const packetlib::Packet& packet) {
  return packet.headers(1).has_ipv4_header() ? IpType::kIpv4 : IpType::kIpv6;
}
IpType InnerIpHeaderType(const packetlib::Packet& packet) {
  return packet.headers(2).has_ipv4_header() ? IpType::kIpv4 : IpType::kIpv6;
}

std::string Ipv4AddressAtIndex(int value) {
  constexpr uint32_t kMinIpv4Address = 0x0a000000;  // 10.0.0.0
  return netaddr::Ipv4Address(std::bitset<32>(kMinIpv4Address + value))
      .ToString();
}
std::string Ipv6Upper64AtIndex(int value) {
  constexpr uint64_t kMinIpv6Upper64 = 0x2002000000000000;  // 2002::
  return netaddr::Ipv6Address(absl::MakeUint128(kMinIpv6Upper64 + value, 0))
      .ToString();
}
std::string MacAddressAtIndex(int value) {
  return netaddr::MacAddress(std::bitset<48>(value)).ToString();
}
std::string HopLimitAtIndex(int value, IpType ip_type) {
  return ip_type == IpType::kIpv4 ? packetlib::IpTtl(kMinHops + value)
                                  : packetlib::IpHopLimit(kMinHops + value);
}

// Set the contents of a packet field based on the given value. Depending on the
// field, a static offset may be applied to generate the contents.
//
// value is assumed to always be between [0, field range)
void SetFieldValue(Field field, int value, packetlib::Packet& packet) {
  IpType ip_type = InnerIpFields().contains(field) ? InnerIpHeaderType(packet)
                                                   : OuterIpHeaderType(packet);
  switch (field) {
    case Field::kEthernetSrc:
      EthernetHeader(packet).set_ethernet_source(MacAddressAtIndex(value));
      break;
    case Field::kEthernetDst:
      EthernetHeader(packet).set_ethernet_destination(MacAddressAtIndex(value));
      break;
    case Field::kIpSrc:
      ip_type == IpType::kIpv4
          ? Ipv4Header(packet).set_ipv4_source(Ipv4AddressAtIndex(value))
          : Ipv6Header(packet).set_ipv6_source(Ipv6Upper64AtIndex(value));
      break;
    case Field::kIpDst:
      ip_type == IpType::kIpv4
          ? Ipv4Header(packet).set_ipv4_destination(Ipv4AddressAtIndex(value))
          : Ipv6Header(packet).set_ipv6_destination(Ipv6Upper64AtIndex(value));
      break;
    case Field::kHopLimit:
      ip_type == IpType::kIpv4
          ? Ipv4Header(packet).set_ttl(HopLimitAtIndex(value, ip_type))
          : Ipv6Header(packet).set_hop_limit(HopLimitAtIndex(value, ip_type));
      break;
    case Field::kDscp:
      ip_type == IpType::kIpv4
          ? Ipv4Header(packet).set_dscp(packetlib::IpDscp(value))
          : Ipv6Header(packet).set_dscp(packetlib::IpDscp(value));
      break;
    case Field::kFlowLabelLower16:
    case Field::kFlowLabelUpper4: {
      uint32_t flow_label = 0;
      if (!absl::SimpleHexAtoi(Ipv6Header(packet).flow_label(), &flow_label)) {
        LOG(FATAL) << "Failed to parse default flow label: '"  // Crash OK
                   << Ipv6Header(packet).flow_label();
      }
      flow_label = field == Field::kFlowLabelLower16
                       ? (flow_label & ~0xffff) + value
                       : (flow_label & 0xffff) + (value << 16);
      Ipv6Header(packet).set_flow_label(packetlib::IpFlowLabel(flow_label));
    } break;
    case Field::kInnerIpSrc:
      ip_type == IpType::kIpv4
          ? InnerIpv4Header(packet).set_ipv4_source(Ipv4AddressAtIndex(value))
          : InnerIpv6Header(packet).set_ipv6_source(Ipv6Upper64AtIndex(value));
      break;
    case Field::kInnerIpDst:
      ip_type == IpType::kIpv4 ? InnerIpv4Header(packet).set_ipv4_destination(
                                     Ipv4AddressAtIndex(value))
                               : InnerIpv6Header(packet).set_ipv6_destination(
                                     Ipv6Upper64AtIndex(value));
      break;
    case Field::kInnerHopLimit:
      ip_type == IpType::kIpv4
          ? InnerIpv4Header(packet).set_ttl(HopLimitAtIndex(value, ip_type))
          : InnerIpv6Header(packet).set_hop_limit(
                HopLimitAtIndex(value, ip_type));
      break;
    case Field::kInnerDscp:
      ip_type == IpType::kIpv4
          ? InnerIpv4Header(packet).set_dscp(packetlib::IpDscp(value))
          : InnerIpv6Header(packet).set_dscp(packetlib::IpDscp(value));
      break;
    case Field::kInnerFlowLabelLower16:
    case Field::kInnerFlowLabelUpper4: {
      uint32_t flow_label = 0;
      if (!absl::SimpleHexAtoi(InnerIpv6Header(packet).flow_label(),
                               &flow_label)) {
        LOG(FATAL) << "Failed to parse default inner flow label: '"  // Crash OK
                   << InnerIpv6Header(packet).flow_label() << "'";
      }
      flow_label = field == Field::kInnerFlowLabelLower16
                       ? (flow_label & ~0xffff) + value
                       : (flow_label & 0xffff) + (value << 16);
      InnerIpv6Header(packet).set_flow_label(
          packetlib::IpFlowLabel(flow_label));
    } break;
    case Field::kL4SrcPort:
      // TODO: Re-allow PTP ports when traffic forwards.
      if (value > 318) value += 2;  // Skip PTP ports 319 & 320.
      UdpHeader(packet).set_source_port(packetlib::UdpPort(value));
      break;
    case Field::kL4DstPort:
      // TODO: Re-allow PTP ports when traffic forwards.
      if (value > 318) value += 2;  // Skip PTP ports 319 & 320.
      // TODO: Reserved ports in packetlib will generate invalid
      // packets.
      if (value > 999) value += 1;   // Skip PSP port 1000.
      if (value > 4738) value += 1;  // Skip Ipfix port 4739.
      UdpHeader(packet).set_destination_port(packetlib::UdpPort(value));
      break;
  }
}

int NormalizeIndex(int index) {
  if (index >= 0) return index;
  if (index == std::numeric_limits<int>::min()) return 0;
  return -index;
}

int BitwidthToInt(int bitwidth) {
  return bitwidth > std::numeric_limits<int>::digits
             ? std::numeric_limits<int>::max()
             : 1 << bitwidth;
}

}  // namespace

const absl::btree_set<Field>& AllFields() {
  static const auto* const kFields = new absl::btree_set<Field>({
      Field::kEthernetSrc,
      Field::kEthernetDst,
      Field::kIpSrc,
      Field::kIpDst,
      Field::kHopLimit,
      Field::kDscp,
      Field::kFlowLabelLower16,
      Field::kFlowLabelUpper4,
      Field::kInnerIpSrc,
      Field::kInnerIpDst,
      Field::kInnerHopLimit,
      Field::kInnerDscp,
      Field::kInnerFlowLabelLower16,
      Field::kInnerFlowLabelUpper4,
      Field::kL4SrcPort,
      Field::kL4DstPort,
  });
  return *kFields;
}

std::string FieldName(Field field) {
  switch (field) {
    case Field::kEthernetSrc:
      return "ETHERNET_SRC";
    case Field::kEthernetDst:
      return "ETHERNET_DST";
    case Field::kIpSrc:
      return "IP_SRC";
    case Field::kIpDst:
      return "IP_DST";
    case Field::kHopLimit:
      return "HOP_LIMIT";
    case Field::kDscp:
      return "DSCP";
    case Field::kFlowLabelLower16:
      return "FLOW_LABEL_LOWER_16";
    case Field::kFlowLabelUpper4:
      return "FLOW_LABEL_UPPER_4";
    case Field::kInnerIpSrc:
      return "INNER_IP_SRC";
    case Field::kInnerIpDst:
      return "INNER_IP_DST";
    case Field::kInnerHopLimit:
      return "INNER_HOP_LIMIT";
    case Field::kInnerDscp:
      return "INNER_DSCP";
    case Field::kInnerFlowLabelLower16:
      return "INNER_FLOW_LABEL_16";
    case Field::kInnerFlowLabelUpper4:
      return "INNER_FLOW_LABEL_UPPER_4";
    case Field::kL4SrcPort:
      return "L4_SRC_PORT";
    case Field::kL4DstPort:
      return "L4_DST_PORT";
  }
  return "";
}

const absl::btree_set<Field>& InnerIpFields() {
  static const auto* const kFields = new absl::btree_set<Field>({
      Field::kInnerIpSrc,
      Field::kInnerIpDst,
      Field::kInnerHopLimit,
      Field::kInnerDscp,
      Field::kInnerFlowLabelLower16,
      Field::kInnerFlowLabelUpper4,
  });
  return *kFields;
}

std::string ToString(const Options& options) {
  std::string packet_type;
  if (!options.inner_ip_type.has_value()) {
    packet_type = options.ip_type == IpType::kIpv4 ? "IPv4" : "IPv6";
  } else {
    packet_type = absl::Substitute(
        "$0In$1", options.inner_ip_type == IpType::kIpv4 ? 4 : 6,
        options.ip_type == IpType::kIpv4 ? 4 : 6);
  }
  return absl::Substitute(
      "$0 Fields:{$1}", packet_type,
      options.variables.empty()
          ? "none"
          : absl::StrJoin(options.variables, ",",
                          [](std::string* out, Field field) {
                            absl::StrAppend(out, FieldName(field));
                          }));
}

absl::Status IsValid(const Options& options) {
  if (!options.inner_ip_type.has_value()) {
    for (Field field : options.variables) {
      if (InnerIpFields().contains(field)) {
        return gutil::InvalidArgumentErrorBuilder()
               << "Invalid PacketGenerator Options. Inner IP Field '"
               << FieldName(field)
               << "' was specified without an Inner IP type.";
      }
    }
  }
  if (options.ip_type == IpType::kIpv4) {
    for (Field field : options.variables) {
      if (field == Field::kFlowLabelLower16 ||
          field == Field::kFlowLabelUpper4) {
        return gutil::InvalidArgumentErrorBuilder()
               << "Invalid PacketGenerator Options. IPv6 Field '"
               << FieldName(field) << "' was specified with ip_type IPv4.";
      }
    }
  }
  if (options.inner_ip_type.has_value() &&
      options.inner_ip_type == IpType::kIpv4) {
    for (Field field : options.variables) {
      if (field == Field::kInnerFlowLabelLower16 ||
          field == Field::kInnerFlowLabelUpper4) {
        return gutil::InvalidArgumentErrorBuilder()
               << "Invalid PacketGenerator Options. IPv6 Field '"
               << FieldName(field)
               << "' was specified with inner_ip_type IPv4.";
      }
    }
  }
  return absl::OkStatus();
}

packetlib::Packet PacketGenerator::Packet(int index) const {
  static std::mt19937 bit_gen;
  packetlib::Packet packet = DefaultPacket(options_);
  packet.set_payload(Description());
  if (options_.variables.empty()) return packet;

  if (options_.variables.size() == 1) {
    Field field = *options_.variables.begin();
    IpType ip_type = InnerIpFields().contains(field) ? *options_.inner_ip_type
                                                     : options_.ip_type;
    SetFieldValue(field,
                  NormalizeIndex(index) % packetgen::Range(field, ip_type),
                  packet);
    return packet;
  }

  bit_gen.seed(index);
  for (Field field : options_.variables) {
    IpType ip_type = InnerIpFields().contains(field) ? *options_.inner_ip_type
                                                     : options_.ip_type;
    SetFieldValue(field,
                  absl::Uniform(bit_gen, 0, packetgen::Range(field, ip_type)),
                  packet);
  }
  return packet;
}

std::vector<packetlib::Packet> PacketGenerator::Packets(int count,
                                                        int offset) const {
  std::vector<packetlib::Packet> packets;
  for (int i = offset; i < offset + count; ++i) {
    packets.push_back(Packet(i));
  }
  return packets;
}

int Range(Field field, IpType ip_type) {
  switch (field) {
    case Field::kIpSrc:
    case Field::kIpDst:
    case Field::kInnerIpSrc:
    case Field::kInnerIpDst:
      // Reserve top prefix (8 bits for IPv4, 16 bits for IPv6).
      return ip_type == IpType::kIpv4 ? BitwidthToInt(24) : BitwidthToInt(48);
    case Field::kEthernetSrc:
    case Field::kEthernetDst:
      return BitwidthToInt(48);
    case Field::kHopLimit:
    case Field::kInnerHopLimit:
      return ip_type == IpType::kIpv4
                 ? BitwidthToInt(packetlib::kIpTtlBitwidth) - kMinHops
                 : BitwidthToInt(packetlib::kIpHopLimitBitwidth) - kMinHops;
    case Field::kDscp:
    case Field::kInnerDscp:
      return BitwidthToInt(packetlib::kIpDscpBitwidth);
    case Field::kFlowLabelLower16:
    case Field::kInnerFlowLabelLower16:
      return BitwidthToInt(16);
    case Field::kFlowLabelUpper4:
    case Field::kInnerFlowLabelUpper4:
      return BitwidthToInt(4);
    case Field::kL4SrcPort:
    case Field::kL4DstPort:
      // TODO: Re-allow PTP ports when traffic forwards.
      // Reserve PTP ports 319 & 320.
      // TODO: Re-allow PSP (1000) and IpFix (4739) when this
      // library generates packets below L4.
      return BitwidthToInt(packetlib::kUdpPortBitwidth) - 4;
  }
  return 0;
}

int PacketGenerator::NumPossiblePackets() const {
  uint64_t full_range = 1;
  for (Field field : options_.variables) {
    IpType ip_type = InnerIpFields().contains(field) ? *options_.inner_ip_type
                                                     : options_.ip_type;
    full_range *= packetgen::Range(field, ip_type);
    if (full_range >= std::numeric_limits<int>::max())
      return std::numeric_limits<int>::max();
  }
  return full_range;
}

}  // namespace packetgen
}  // namespace pins_test
