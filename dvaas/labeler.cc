#include "dvaas/labeler.h"

#include <bitset>

#include "absl/algorithm/container.h"
#include "absl/log/log.h"
#include "absl/status/statusor.h"
#include "dvaas/packet_trace.pb.h"
#include "dvaas/test_vector.pb.h"
#include "gutil/gutil/status.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/netaddr/ipv4_address.h"
#include "p4_pdpi/netaddr/ipv6_address.h"
#include "p4_pdpi/netaddr/mac_address.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"

namespace dvaas {

namespace {

bool IsVlanTagged(const packetlib::Packet& packet) {
  return absl::c_any_of(packet.headers(), [](const auto& header) {
    return header.has_vlan_header();
  });
}

absl::StatusOr<bool> IsUnicast(const netaddr::MacAddress& mac) {
  // The least significant bit of the first byte (40) of the destination MAC
  // address must be set to 0 for unicast packets.
  // The destination MAC address must not be all zeros because it is an
  // invalid address.
  return !mac.IsAllZeros() && !mac.ToBitset().test(40);
}

absl::StatusOr<bool> IsMulticast(const netaddr::Ipv4Address& ipv4) {
  std::bitset<8> ipv4_top_8_bits = (ipv4.ToBitset() >> 24).to_ulong();
  // IPv4 multicast address ranges from 224.0.0.0/4 to 239.255.255.255/4.
  return (ipv4_top_8_bits.to_ulong() & 0xF0) == 224;
}

absl::StatusOr<bool> IsMulticast(const netaddr::Ipv6Address& ipv6) {
  std::bitset<128> ipv6_bits = ipv6.ToBitset();
  std::bitset<8> ipv6_top_8_bits = (ipv6_bits >> 120).to_ulong();
  // IPv6 multicast address prefix is ff00::/8.
  return ipv6_top_8_bits.to_ulong() == 0xFF;
}

}  // namespace

absl::StatusOr<Labels> VlanTaggedInputLabeler(const PacketTestRun& test_run) {
  Labels labels;
  if (IsVlanTagged(test_run.test_vector().input().packet().parsed())) {
    labels.add_labels("vlan_tagged_input");
  }
  return labels;
}

absl::StatusOr<Labels> UnicastDstMacMulticastDstIpInputLabeler(
    const PacketTestRun& test_run) {
  Labels labels;
  bool is_dst_mac_unicast = false;
  bool is_dst_ip_multicast = false;
  const auto& headers =
      test_run.test_vector().input().packet().parsed().headers();
  for (const auto& header : headers) {
    if (header.has_ethernet_header()) {
      ASSIGN_OR_RETURN(netaddr::MacAddress mac_address,
                       netaddr::MacAddress::OfString(
                           header.ethernet_header().ethernet_destination()));
      ASSIGN_OR_RETURN(is_dst_mac_unicast, IsUnicast(mac_address));
    }
    if (header.has_ipv4_header()) {
      ASSIGN_OR_RETURN(netaddr::Ipv4Address ipv4_dst_address,
                       netaddr::Ipv4Address::OfString(
                           header.ipv4_header().ipv4_destination()));
      ASSIGN_OR_RETURN(is_dst_ip_multicast, IsMulticast(ipv4_dst_address));
      // For IP-in-IP packets, we only check the outer IP header so we can
      // break early.
      break;
    }
    if (header.has_ipv6_header()) {
      ASSIGN_OR_RETURN(netaddr::Ipv6Address ipv6_dst_address,
                       netaddr::Ipv6Address::OfString(
                           header.ipv6_header().ipv6_destination()));
      ASSIGN_OR_RETURN(is_dst_ip_multicast, IsMulticast(ipv6_dst_address));
      // For IP-in-IP packets, we only check the outer IP header so we can
      // break early.
      break;
    }
  }

  if (is_dst_mac_unicast && is_dst_ip_multicast) {
    labels.add_labels("unicast_dst_mac_multicast_dst_ip_input");
  }

  return labels;
}
}  // namespace dvaas
