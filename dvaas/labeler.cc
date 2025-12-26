#include "dvaas/labeler.h"

#include <bitset>
#include <functional>
#include <string>
#include <vector>

#include "absl/algorithm/container.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "dvaas/packet_trace.pb.h"
#include "dvaas/test_vector.pb.h"
#include "gutil/gutil/status.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/netaddr/ipv4_address.h"
#include "p4_pdpi/netaddr/ipv6_address.h"
#include "p4_pdpi/netaddr/mac_address.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "re2/re2.h"

namespace dvaas {

namespace {

// Returns the first packet trace found in the test run. Returns an error if no
// packet trace is found.
absl::StatusOr<PacketTrace> GetPacketTrace(const PacketTestRun& test_run) {
  for (const auto& acceptable_output :
       test_run.test_vector().acceptable_outputs()) {
    if (acceptable_output.has_packet_trace()) {
      return acceptable_output.packet_trace();
    }
  }
  return absl::NotFoundError("No packet trace found in test run");
}

bool IsVlanTagged(const packetlib::Packet& packet) {
  return absl::c_any_of(packet.headers(), [](const auto& header) {
    return header.has_vlan_header();
  });
}

bool IsIcmpTagged(const packetlib::Packet& packet) {
  return absl::c_any_of(packet.headers(), [](const auto& header) {
    return header.has_icmp_header();
  });
}

absl::StatusOr<bool> IsUnicast(const netaddr::MacAddress& mac) {
  // The least significant bit of the first byte (40) of the destination MAC
  // address must be set to 0 for unicast packets.
  // The destination MAC address must not be all zeros because it is an
  // invalid address.
  return !mac.IsAllZeros() && !mac.ToBitset().test(40);
}

absl::StatusOr<bool> IsMulticast(const netaddr::MacAddress& mac) {
  // The least significant bit of the first byte (40) of the destination MAC
  // address must be set to 1 for multicast packets.
  return mac.ToBitset().test(40);
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

bool IsAclTableInIngressStage(absl::string_view table_name) {
  return RE2::FullMatch(table_name, "acl_ingress(_.+)?_table");
}

bool IsAclTableInEgressStage(absl::string_view table_name) {
  return RE2::FullMatch(table_name, "acl_egress(_.+)?_table");
}

}  // namespace

std::vector<std::function<absl::StatusOr<Labels>(const PacketTestRun&)>>
DefaultPacketTestRunLabelers() {
  return {
      VlanTaggedInputLabeler,
      SubmitToIngressVlanTaggedInputLabeler,
      MulticastSrcMacInputLabeler,
      UnicastDstMacMulticastDstIpInputLabeler,
      SubmitToIngressMulticastDstIpInputLabeler,
      Ttl01InputForwardingLabeler,
      IcmpInputForwardingLabeler,
  };
}

absl::StatusOr<Labels> VlanTaggedInputLabeler(const PacketTestRun& test_run) {
  Labels labels;
  if (IsVlanTagged(test_run.test_vector().input().packet().parsed())) {
    labels.add_labels("vlan_tagged_input");
  }
  return labels;
}

absl::StatusOr<Labels> SubmitToIngressVlanTaggedInputLabeler(
    const PacketTestRun& test_run) {
  Labels labels;
  if (test_run.test_vector().input().type() ==
          dvaas::SwitchInput::SUBMIT_TO_INGRESS &&
      IsVlanTagged(test_run.test_vector().input().packet().parsed())) {
    labels.add_labels("submit_to_ingress_vlan_tagged_input");
  }
  return labels;
}

absl::StatusOr<Labels> MulticastSrcMacInputLabeler(
    const PacketTestRun& test_run) {
  Labels labels;
  bool is_src_mac_multicast = false;
  const auto& headers =
      test_run.test_vector().input().packet().parsed().headers();
  for (const auto& header : headers) {
    if (header.has_ethernet_header()) {
      ASSIGN_OR_RETURN(netaddr::MacAddress mac_address,
                       netaddr::MacAddress::OfString(
                           header.ethernet_header().ethernet_source()));
      ASSIGN_OR_RETURN(is_src_mac_multicast, IsMulticast(mac_address));
      // For IPFIX encap, packets can have nested ethernet headers. We only
      // check the outer ethernet header so we can break early.
      break;
    }
  }

  if (is_src_mac_multicast) {
    labels.add_labels("multicast_src_mac_input");
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

absl::StatusOr<Labels> SubmitToIngressMulticastDstIpInputLabeler(
    const PacketTestRun& test_run) {
  Labels labels;
  // Only considering submit-to-ingress packets.
  if (test_run.test_vector().input().type() !=
      dvaas::SwitchInput::SUBMIT_TO_INGRESS) {
    return labels;
  }
  const auto& headers =
      test_run.test_vector().input().packet().parsed().headers();
  bool is_dst_ip_multicast = false;
  for (const auto& header : headers) {
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
  if (is_dst_ip_multicast) {
    labels.add_labels("submit_to_ingress_multicast_dst_ip_input");
  }
  return labels;
}

absl::StatusOr<Labels> Ttl01InputForwardingLabeler(
    const PacketTestRun& test_run) {
  Labels labels;
  bool has_ttl_0_or_1 = false;
  bool hit_l3_route = false;
  bool acl_prevents_forwarding = false;
  for (const auto& header :
       test_run.test_vector().input().packet().parsed().headers()) {
    if ((header.has_ipv4_header() && (header.ipv4_header().ttl() == "0x00" ||
                                      header.ipv4_header().ttl() == "0x01")) ||
        (header.has_ipv6_header() &&
         (header.ipv6_header().hop_limit() == "0x00" ||
          header.ipv6_header().hop_limit() == "0x01"))) {
      has_ttl_0_or_1 = true;
    }
    // For IP-in-IP packets, we only check the outer IP header so we can
    // break early.
    if (header.has_ipv4_header() || header.has_ipv6_header()) {
      break;
    }
  }

  ASSIGN_OR_RETURN(const PacketTrace& packet_trace, GetPacketTrace(test_run));
  for (const auto& event : packet_trace.events()) {
    if (event.has_table_apply() && event.table_apply().has_hit()) {
      pdpi::IrTableEntry ir_table_entry =
          event.table_apply().hit().table_entry();

      // Packet hits an L3 route (ipv4_table or ipv6_table).
      if (ir_table_entry.table_name() == "ipv4_table" ||
          ir_table_entry.table_name() == "ipv6_table") {
        hit_l3_route = true;
      }

      // Packet hits any ingress/egress ACL and the ACL action is drop, deny,
      // or trap.
      if (IsAclTableInIngressStage(ir_table_entry.table_name()) ||
          IsAclTableInEgressStage(ir_table_entry.table_name())) {
	const std::string& action_name = ir_table_entry.action().name();
        if (action_name == "acl_deny" || action_name == "acl_drop" ||
            action_name == "acl_trap") {
          acl_prevents_forwarding = true;
        }
      }
    }
  }
  if (has_ttl_0_or_1 && hit_l3_route && !acl_prevents_forwarding) {
    labels.add_labels("ttl_01_input_forward");
  }
  return labels;
}

absl::StatusOr<Labels> IcmpInputForwardingLabeler(
    const PacketTestRun& test_run) {
  Labels labels;
  // If the input packet is not ICMP tagged, then we can skip this labeler.
  if (!IsIcmpTagged(test_run.test_vector().input().packet().parsed())) {
    return labels;
  }

  // Checking if packet is expected to be forwarded.
  // Even though there are multiple acceptable outcomes (corresponding to the
  // non-determinism caused by WCMP members), we only check one of the
  // acceptable outcomes. Although not guaranteed in general, in practical use
  // cases, all outcomes typically have the same type of output (e.g. drop, put,
  // forwards, etc.) despite the content of the packets (e.g. egress port, smac)
  // varying in different acceptable outcomes. Given that we only check
  // the output packet fate and not the content, checking one acceptable outcome
  // here is enough (and is more consistent with checking only one packet
  // trace).
  if (!test_run.test_vector().acceptable_outputs().empty() &&
      !test_run.test_vector().acceptable_outputs(0).packets().empty()) {
    labels.add_labels("icmp_input_forward");
  }
  return labels;
}

}  // namespace dvaas
