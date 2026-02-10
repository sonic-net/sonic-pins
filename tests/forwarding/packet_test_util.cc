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

#include "tests/forwarding/packet_test_util.h"

#include <algorithm>
#include <limits>

#include "p4_infra/p4_pdpi/netaddr/ipv6_address.h"

namespace pins {

using ::packetlib::EthernetHeader;
using ::packetlib::IpDscp;
using ::packetlib::IpEcn;
using ::packetlib::IpFlags;
using ::packetlib::IpFlowLabel;
using ::packetlib::IpFragmentOffset;
using ::packetlib::IpHopLimit;
using ::packetlib::IpIdentification;
using ::packetlib::IpIhl;
using ::packetlib::IpNextHeader;
using ::packetlib::IpProtocol;
using ::packetlib::IpTtl;
using ::packetlib::Ipv4Header;
using ::packetlib::Ipv6Header;
using ::packetlib::UdpHeader;
using ::packetlib::UdpPort;

namespace {
// Choose a base DstMac that is far enough away from the base SrcMac to minimize
// collision between the address spaces.
constexpr uint64_t kBaseDstMac = 100234;
constexpr uint64_t kBaseSrcMac = 123;
constexpr uint64_t kMacAddrSize = static_cast<uint64_t>(1) << (48);
constexpr uint64_t kHopLimitRange = 256 - 3; // Minimum hop limit is 3.

// Base IPv4 address for generating the outer IP header for packets that are not
// supposed to be decapped.
constexpr uint32_t kBaseIpV4Src = 0x01020304;       // 1.2.3.4
constexpr uint32_t kBaseIpV4Dst = 0x02030405;       // 2.3.4.5
constexpr uint32_t kBaseDecapIpV4Src = 0x0a020304;  // 10.2.3.4
constexpr uint32_t kBaseDecapIpV4Dst = 0x14030405;  // 20.3.4.5

std::string PacketFieldToString(const PacketField field) {
  switch (field) {
    case PacketField::kEthernetSrc:
      return "ETHERNET_SRC";
    case PacketField::kEthernetDst:
      return "ETHERNET_DST";
    case PacketField::kIpSrc:
      return "IP_SRC";
    case PacketField::kIpDst:
      return "IP_DST";
    case PacketField::kHopLimit:
      return "HOP_LIMIT";
    case PacketField::kDscp:
      return "DSCP";
    case PacketField::kFlowLabelLower16:
      return "FLOW_LABEL_LOWER_16";
    case PacketField::kFlowLabelUpper4:
      return "FLOW_LABEL_UPPER_4";
    case PacketField::kInnerIpSrc:
      return "INNER_IP_SRC";
    case PacketField::kInnerIpDst:
      return "INNER_IP_DST";
    case PacketField::kInnerHopLimit:
      return "INNER_HOP_LIMIT";
    case PacketField::kInnerDscp:
      return "INNER_DSCP";
    case PacketField::kInnerFlowLabelLower16:
      return "INNER_FLOW_LABEL_16";
    case PacketField::kInnerFlowLabelUpper4:
      return "INNER_FLOW_LABEL_UPPER_4";
    case PacketField::kL4SrcPort:
      return "L4_SRC_PORT";
    case PacketField::kL4DstPort:
      return "L4_DST_PORT";
    case PacketField::kInputPort:
      return "INPUT_PORT";
  }
  return "";
}

// Is this a inner IP field?
bool IsInnerIpField(const PacketField field) {
  switch (field) {
    case PacketField::kInnerIpSrc:
    case PacketField::kInnerIpDst:
    case PacketField::kInnerHopLimit:
    case PacketField::kInnerDscp:
    case PacketField::kInnerFlowLabelLower16:
    case PacketField::kInnerFlowLabelUpper4:
      return true;
    default:
      return false;
  }
}

// Returns the ith L4 port, given a base port
uint32_t GetIthL4Port(int i, uint32_t base) {
  return (base + i) & 0xffff;  // limit to 16 bits.
}

}  // namespace

const std::vector<PacketField> &AllPacketFields() {
  static const auto *const kPacketFields = new std::vector<PacketField>({
      PacketField::kEthernetSrc,
      PacketField::kEthernetDst,
      PacketField::kIpSrc,
      PacketField::kIpDst,
      PacketField::kHopLimit,
      PacketField::kDscp,
      PacketField::kFlowLabelLower16,
      PacketField::kFlowLabelUpper4,
      PacketField::kInnerIpSrc,
      PacketField::kInnerIpDst,
      PacketField::kInnerHopLimit,
      PacketField::kInnerDscp,
      PacketField::kInnerFlowLabelLower16,
      PacketField::kInnerFlowLabelUpper4,
      PacketField::kL4SrcPort,
      PacketField::kL4DstPort,
      PacketField::kInputPort,
  });
  return *kPacketFields;
}

// Clears the received packet output vector and the packet statistics counters.
void TestData::ClearReceivedPackets() {
  absl::MutexLock lock(&mutex);
  for (auto& [packet, input_output] : input_output_per_packet) {
    input_output.output.clear();
  }
  total_packets_sent = 0;
  total_packets_received = 0;
  total_invalid_packets_received = 0;
}

// Is this a valid test configuration?  Not all configurations are valid, e.g.
// you can't modify the flow label in an IPv4 packet (because there is no flow
// label there).
bool IsValidTestConfiguration(const TestConfiguration& config) {
  // FLOW_LABEL only exists for IPv6
  if (config.field == PacketField::kFlowLabelLower16 && config.ipv4)
    return false;
  if (config.field == PacketField::kFlowLabelUpper4 && config.ipv4)
    return false;
  if (config.field == PacketField::kInnerFlowLabelLower16 && config.inner_ipv4)
    return false;
  if (config.field == PacketField::kInnerFlowLabelUpper4 && config.inner_ipv4)
    return false;
  // If the packet is not encapped, various things don't make sense
  if (!config.encapped) {
    // Can only decap an encapped packet
    if (config.decap) return false;
    // inner_ipv4 is ignored for non-encapped packets, so only use one of the
    // two values.
    if (config.inner_ipv4) return false;
    // Cannot vary inner fields if not encapped.
    if (IsInnerIpField(config.field)) return false;
  }
  // encapped traffic with v6 outer is not currently a use-case, so we are not
  // testing it.
  if (config.encapped && !config.ipv4) return false;
  return true;
}

// Returns the number of values available within the packet field.
int Range(const TestConfiguration &config) {
  // GenerateIthPacket takes in an int index. Any field with 31 or more bits
  // may be limited by the int range before the header field range.
  static constexpr int kIpv4Range =
      0x7f000000 - kBaseDecapIpV4Dst;  // Exclude 127.x.x.x
  static constexpr int kInt64Range =
      std::min(static_cast<uint64_t>(std::numeric_limits<int>::max()),
               std::numeric_limits<uint64_t>::max());
  static constexpr int kEthernetRange = std::min(
      static_cast<uint64_t>(std::numeric_limits<int>::max()), kMacAddrSize);
  switch (config.field) {
  case PacketField::kEthernetSrc:
  case PacketField::kEthernetDst:
    return kEthernetRange;
  case PacketField::kIpSrc:
  case PacketField::kIpDst:
  case PacketField::kInnerIpSrc:
  case PacketField::kInnerIpDst:
    return config.ipv4 ? kIpv4Range : kInt64Range;
  case PacketField::kHopLimit:
  case PacketField::kInnerHopLimit:
    return kHopLimitRange;
  case PacketField::kDscp:
    return 1 << 6;
  case PacketField::kFlowLabelLower16:
  case PacketField::kInnerFlowLabelLower16:
    return 1 << 16;
  case PacketField::kFlowLabelUpper4:
  case PacketField::kInnerFlowLabelUpper4:
    return 1 << 4;
  case PacketField::kL4SrcPort:
  case PacketField::kL4DstPort:
    return 1 << 16;
  // Not used by the packet generator
  case PacketField::kInputPort:
  case PacketField::kInnerDscp:
    return 1;
  }
  return 0; // Not reachable.
}

// Returns the ith destination MAC that is used when varying that field.
netaddr::MacAddress GetIthDstMac(int i) {
  return netaddr::MacAddress(std::bitset<48>(kBaseDstMac + i % kMacAddrSize));
}

// Returns a human-readable description of a test config.
std::string DescribeTestConfig(const TestConfiguration& config) {
  return absl::StrCat("field=", PacketFieldToString(config.field),
                      " ipv4=", config.ipv4, " encapped=", config.encapped,
                      " inner_ipv4=", config.inner_ipv4,
                      " decap=", config.decap);
}

std::string TestConfigurationToPayload(const TestConfiguration& config) {
  std::string desc = DescribeTestConfig(config);
  if (desc.size() >= 64) return desc;
  // Pad to 64 bytes
  return absl::StrCat(desc, std::string(64 - desc.size(), '.'));
}

// Returns the i-th packet for the given test configuration.  The packets all
// follow the requirements of the config (e.g., is this a IPv4 or IPv6 packet),
// and vary in exactly one field (the one specified in the config).
absl::StatusOr<packetlib::Packet> GenerateIthPacket(
    const TestConfiguration& config, int index) {
  constexpr uint64_t kDefaultSrcIpUpper = 0x0001000200030004;
  constexpr uint64_t kDefaultDstIpUpper = 0x0002000300040005;

  packetlib::Packet packet;
  const auto& field = config.field;

  EthernetHeader* eth = packet.add_headers()->mutable_ethernet_header();

  eth->set_ethernet_source(
      netaddr::MacAddress(std::bitset<48>(kBaseSrcMac)).ToString());
  if (field == PacketField::kEthernetSrc) {
    eth->set_ethernet_source(
        netaddr::MacAddress(std::bitset<48>(kBaseSrcMac + index % kMacAddrSize))
            .ToString());
  }
  eth->set_ethernet_destination(
      netaddr::MacAddress(std::bitset<48>(kBaseDstMac)).ToString());
  if (field == PacketField::kEthernetDst) {
    eth->set_ethernet_destination(GetIthDstMac(index).ToString());
  }
  eth->set_ethertype(config.ipv4 ? packetlib::EtherType(ETHERTYPE_IP)
                                 : packetlib::EtherType(ETHERTYPE_IPV6));
  {
    uint8_t hop_limit = 32;
    // Avoid hop_limit of 0,1,2 to avoid drops.
    if (field == PacketField::kHopLimit)
      hop_limit = 3 + (index % kHopLimitRange);

    uint8_t dscp = 10;
    if (field == PacketField::kDscp) {
      dscp = index % static_cast<uint8_t>(1 << 6);
    }

    int next_protocol = IPPROTO_UDP;
    if (config.encapped)
      next_protocol = config.inner_ipv4 ? IPPROTO_IPIP : IPPROTO_IPV6;

    if (config.ipv4) {
      Ipv4Header* ip = packet.add_headers()->mutable_ipv4_header();
      ip->set_ihl(IpIhl(5));
      uint32_t default_src = config.decap ? kBaseDecapIpV4Src : kBaseIpV4Src;
      if (field == PacketField::kIpSrc) {
        ip->set_ipv4_source(
            netaddr::Ipv4Address(std::bitset<32>(default_src + index))
                .ToString());
      } else {
        ip->set_ipv4_source(
            netaddr::Ipv4Address(std::bitset<32>(default_src)).ToString());
      }
      auto default_dst = config.decap ? kBaseDecapIpV4Dst : kBaseIpV4Dst;
      if (field == PacketField::kIpDst) {
        ip->set_ipv4_destination(
            netaddr::Ipv4Address(std::bitset<32>(default_dst + index))
                .ToString());
      } else {
        ip->set_ipv4_destination(
            netaddr::Ipv4Address(std::bitset<32>(default_dst)).ToString());
      }
      ip->set_ttl(IpTtl(hop_limit));
      ip->set_dscp(IpDscp(dscp));
      ip->set_protocol(IpProtocol(next_protocol));

      // Fill other default (required) fields.
      ip->set_ecn(IpEcn(0));
      ip->set_identification(IpIdentification(0));
      ip->set_flags(IpFlags(0));
      ip->set_fragment_offset(IpFragmentOffset(0));
    } else {
      Ipv6Header* ip = packet.add_headers()->mutable_ipv6_header();
      auto src_ip = absl::MakeUint128(
          kDefaultSrcIpUpper + (field == PacketField::kIpSrc ? index : 0), 0);
      ip->set_ipv6_source(netaddr::Ipv6Address(src_ip).ToString());

      auto dst_ip = absl::MakeUint128(
          kDefaultDstIpUpper + (field == PacketField::kIpDst ? index : 0), 0);
      ip->set_ipv6_destination(netaddr::Ipv6Address(dst_ip).ToString());

      ip->set_hop_limit(IpHopLimit(hop_limit));
      ip->set_dscp(IpDscp(dscp));
      uint32_t flow_label = 0;
      if (field == PacketField::kFlowLabelLower16) {
        flow_label = index % (1 << 16);
      }
      if (field == PacketField::kFlowLabelUpper4) {
        flow_label = (index % (1 << 4)) << 16;
      }
      ip->set_flow_label(IpFlowLabel(flow_label));
      ip->set_next_header(IpNextHeader(next_protocol));
      ip->set_ecn(IpEcn(0));
    }
  }

  // Add inner header
  if (config.encapped) {
    uint8_t inner_hop_limit = 33;
    // Avoid hop_limit of 0,1,2 to avoid drops.
    if (field == PacketField::kInnerHopLimit)
      inner_hop_limit = 3 + (index % kHopLimitRange);

    uint8_t inner_dscp = index % static_cast<uint8_t>(1 << 6);

    if (config.inner_ipv4) {
      Ipv4Header* ip = packet.add_headers()->mutable_ipv4_header();
      ip->set_ihl(IpIhl(5));
      uint32_t default_inner_src = 0x03040506;
      if (field == PacketField::kInnerIpSrc) {
        ip->set_ipv4_source(
            netaddr::Ipv4Address(std::bitset<32>(default_inner_src + index))
                .ToString());
      } else {
        ip->set_ipv4_source(
            netaddr::Ipv4Address(std::bitset<32>(default_inner_src))
                .ToString());
      }
      uint32_t default_inner_dst = 0x04050607;
      if (field == PacketField::kInnerIpDst) {
        ip->set_ipv4_destination(
            netaddr::Ipv4Address(std::bitset<32>(default_inner_dst + index))
                .ToString());
      } else {
        ip->set_ipv4_destination(
            netaddr::Ipv4Address(std::bitset<32>(default_inner_dst))
                .ToString());
      }
      ip->set_ttl(IpTtl(inner_hop_limit));
      ip->set_dscp(IpDscp(inner_dscp));
      ip->set_protocol(IpProtocol(IPPROTO_UDP));
      // Fill other default (required) fields.
      ip->set_ecn(IpEcn(0));
      ip->set_identification(IpIdentification(0));
      ip->set_flags(IpFlags(0));
      ip->set_fragment_offset(IpFragmentOffset(0));
    } else {
      Ipv6Header* ip = packet.add_headers()->mutable_ipv6_header();
      auto default_inner_src = absl::MakeUint128(0x0003000400050006, 0);
      if (field == PacketField::kInnerIpSrc) {
        ip->set_ipv6_source(
            netaddr::Ipv6Address(default_inner_src + index).ToString());
      } else {
        ip->set_ipv6_source(netaddr::Ipv6Address(default_inner_src).ToString());
      }
      auto default_inner_dst = absl::MakeUint128(0x0004000500060007, 0);
      if (field == PacketField::kInnerIpDst) {
        ip->set_ipv6_destination(
            netaddr::Ipv6Address(default_inner_dst + index).ToString());
      } else {
        ip->set_ipv6_destination(
            netaddr::Ipv6Address(default_inner_dst).ToString());
      }
      ip->set_hop_limit(IpTtl(inner_hop_limit));
      ip->set_dscp(IpDscp(inner_dscp));
      uint32_t inner_flow_label = 0;
      if (field == PacketField::kInnerFlowLabelLower16) {
        inner_flow_label = index % (1 << 16);
      }
      if (field == PacketField::kInnerFlowLabelUpper4) {
        inner_flow_label = (index % (1 << 4)) << 16;
      }
      ip->set_flow_label(IpFlowLabel(inner_flow_label));
      ip->set_next_header(IpProtocol(IPPROTO_UDP));
      ip->set_ecn(IpEcn(0));
    }
  }

  UdpHeader* udp = packet.add_headers()->mutable_udp_header();
  uint32_t default_src_port = 2345;
  uint32_t default_dst_port = 4567;
  udp->set_source_port(UdpPort(default_src_port));
  if (field == PacketField::kL4SrcPort) {
    udp->set_source_port(UdpPort(GetIthL4Port(index, default_src_port)));
  }
  udp->set_destination_port(UdpPort(default_dst_port));
  if (field == PacketField::kL4DstPort) {
    udp->set_destination_port(UdpPort(GetIthL4Port(index, default_dst_port)));
  }

  packet.set_payload(TestConfigurationToPayload(config));

  return packet;
}

} // namespace pins
