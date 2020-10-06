#ifndef SAI_ACL_INGRESS_P4_
#define SAI_ACL_INGRESS_P4_

#include <v1model.p4>
#include "../../fixed/headers.p4"
#include "../../fixed/metadata.p4"
#include "acl_common_actions.p4"
#include "ids.h"
#include "minimum_guaranteed_sizes.p4"

control acl_ingress(in headers_t headers,
                    inout local_metadata_t local_metadata,
                    inout standard_metadata_t standard_metadata) {
  // IPv4 TTL or IPv6 hoplimit bits (or 0, for non-IP packets)
  bit<8> ttl = 0;
  // First 6 bits of IPv4 TOS or IPv6 traffic class (or 0, for non-IP packets)
  bit<6> dscp = 0;
  // Last 2 bits of IPv4 TOS or IPv6 traffic class (or 0, for non-IP packets)
  bit<2> ecn = 0;
  // IPv4 IP protocol or IPv6 next_header (or 0, for non-IP packets)
  bit<8> ip_protocol = 0;

  @id(ACL_INGRESS_METER_ID)
  direct_meter<MeterColor_t>(MeterType.bytes) acl_ingress_meter;

  @id(ACL_INGRESS_COUNTER_ID)
  direct_counter(CounterType.packets_and_bytes) acl_ingress_counter;

  // Copy the packet to the CPU, and forward the original packet.
  @id(ACL_INGRESS_COPY_ACTION_ID)
  @sai_action(SAI_PACKET_ACTION_COPY, SAI_PACKET_COLOR_GREEN)
  @sai_action(SAI_PACKET_ACTION_FORWARD, SAI_PACKET_COLOR_YELLOW)
  @sai_action(SAI_PACKET_ACTION_FORWARD, SAI_PACKET_COLOR_RED)
  action acl_copy(@sai_action_param(QOS_QUEUE) @id(1) qos_queue_t qos_queue) {
    acl_ingress_counter.count();
    acl_ingress_meter.read(local_metadata.color);

    // We model the behavior for GREEN packes only below.
    // TODO: Branch on color and model behavior for all colors.
    clone(CloneType.I2E, COPY_TO_CPU_SESSION_ID);
  }

  // Copy the packet to the CPU. The original packet is dropped.
  @id(ACL_INGRESS_TRAP_ACTION_ID)
  @sai_action(SAI_PACKET_ACTION_TRAP, SAI_PACKET_COLOR_GREEN)
  @sai_action(SAI_PACKET_ACTION_DROP, SAI_PACKET_COLOR_YELLOW)
  @sai_action(SAI_PACKET_ACTION_DROP, SAI_PACKET_COLOR_RED)
  action acl_trap(@sai_action_param(QOS_QUEUE) @id(1) qos_queue_t qos_queue) {
    acl_copy(qos_queue);
    mark_to_drop(standard_metadata);
  }

  // An experimental, metered version of `acl_trap`.
  // TODO: Remove this action and meter the existing `acl_trap`
  // action.
  @id(ACL_INGRESS_EXPERIMENTAL_TRAP_ACTION_ID)
  @sai_action(SAI_PACKET_ACTION_TRAP, SAI_PACKET_COLOR_GREEN)
  @sai_action(SAI_PACKET_ACTION_DROP, SAI_PACKET_COLOR_YELLOW)
  @sai_action(SAI_PACKET_ACTION_DROP, SAI_PACKET_COLOR_RED)
  action acl_experimental_trap(@sai_action_param(QOS_QUEUE) @id(1) qos_queue_t qos_queue) {
    acl_ingress_meter.read(local_metadata.color);
    // TODO: model metering by branching on color.
    acl_trap(qos_queue);
  }

  // Forward the packet normally (i.e., perform no action). This is useful as
  // the default action, and to specify a meter but not otherwise perform any
  // action.
  @id(ACL_INGRESS_FORWARD_ACTION_ID)
  @sai_action(SAI_PACKET_ACTION_FORWARD, SAI_PACKET_COLOR_GREEN)
  @sai_action(SAI_PACKET_ACTION_DROP, SAI_PACKET_COLOR_YELLOW)
  @sai_action(SAI_PACKET_ACTION_DROP, SAI_PACKET_COLOR_RED)
  action acl_forward() {
    acl_ingress_counter.count();
    acl_ingress_meter.read(local_metadata.color);
    // We model the behavior for GREEN packes only here.
    // TODO: Branch on color and model behavior for all colors.
  }

  @id(ACL_INGRESS_MIRROR_ACTION_ID)
  @sai_action(SAI_PACKET_ACTION_FORWARD)
  action acl_mirror(
      @id(1)
      @refers_to(mirror_session_table, mirror_session_id)
      @sai_action_param(SAI_ACL_ENTRY_ATTR_ACTION_MIRROR_INGRESS)
      mirror_session_id_t mirror_session_id) {
    acl_ingress_counter.count();
    local_metadata.mirror_session_id_valid = true;
    local_metadata.mirror_session_id_value = mirror_session_id;
  }

  @p4runtime_role(P4RUNTIME_ROLE_SDN_CONTROLLER)
  @id(ACL_INGRESS_TABLE_ID)
  @sai_acl(INGRESS)
  @entry_restriction("
    // Forbid using ether_type for IP packets (by convention, use is_ip* instead).
    ether_type != 0x0800 && ether_type != 0x86dd;
    // Only allow IP field matches for IP packets.
    dst_ip::mask != 0 -> is_ipv4 == 1;
    dst_ipv6::mask != 0 -> is_ipv6 == 1;
    ttl::mask != 0 -> (is_ip == 1 || is_ipv4 == 1 || is_ipv6 == 1);
    dscp::mask != 0 -> (is_ip == 1 || is_ipv4 == 1 || is_ipv6 == 1);
    ecn::mask != 0 -> (is_ip == 1 || is_ipv4 == 1 || is_ipv6 == 1);
    ip_protocol::mask != 0 -> (is_ip == 1 || is_ipv4 == 1 || is_ipv6 == 1);
    // Only allow l4_dst_port and l4_src_port matches for TCP/UDP packets.
    l4_src_port::mask != 0 -> (ip_protocol == 6 || ip_protocol == 17);
    l4_dst_port::mask != 0 -> (ip_protocol == 6 || ip_protocol == 17);
#ifdef SAI_INSTANTIATION_MIDDLEBLOCK
    // Only allow arp_tpa matches for ARP packets.
    arp_tpa::mask != 0 -> ether_type == 0x0806;
#endif
    // Only allow icmp_type matches for ICMP packets
#ifdef SAI_INSTANTIATION_FABRIC_BORDER_ROUTER
    icmp_type::mask != 0 -> ip_protocol == 1;
#endif
    icmpv6_type::mask != 0 -> ip_protocol == 58;
    // Forbid illegal combinations of IP_TYPE fields.
    is_ip::mask != 0 -> (is_ipv4::mask == 0 && is_ipv6::mask == 0);
    is_ipv4::mask != 0 -> (is_ip::mask == 0 && is_ipv6::mask == 0);
    is_ipv6::mask != 0 -> (is_ip::mask == 0 && is_ipv4::mask == 0);
    // Forbid unsupported combinations of IP_TYPE fields.
    is_ipv4::mask != 0 -> (is_ipv4 == 1);
    is_ipv6::mask != 0 -> (is_ipv6 == 1);
  ")
  table acl_ingress_table {
    key = {
      headers.ipv4.isValid() || headers.ipv6.isValid() : optional @name("is_ip") @id(1)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_ACL_IP_TYPE/IP);
      headers.ipv4.isValid() : optional @name("is_ipv4") @id(2)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_ACL_IP_TYPE/IPV4ANY);
      headers.ipv6.isValid() : optional @name("is_ipv6") @id(3)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_ACL_IP_TYPE/IPV6ANY);
      headers.ethernet.ether_type : ternary @name("ether_type") @id(4)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_ETHER_TYPE);
      headers.ethernet.dst_addr : ternary @name("dst_mac") @id(5)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_DST_MAC) @format(MAC_ADDRESS);
      headers.ipv4.src_addr : ternary @name("src_ip") @id(6)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_SRC_IP) @format(IPV4_ADDRESS);
      headers.ipv4.dst_addr : ternary @name("dst_ip") @id(7)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_DST_IP) @format(IPV4_ADDRESS);
      headers.ipv6.src_addr[127:64] : ternary @name("src_ipv6") @id(8)
          @composite_field(
              @sai_field(SAI_ACL_TABLE_ATTR_FIELD_SRC_IPV6_WORD3),
              @sai_field(SAI_ACL_TABLE_ATTR_FIELD_SRC_IPV6_WORD2)
          ) @format(IPV6_ADDRESS);
      headers.ipv6.dst_addr[127:64] : ternary @name("dst_ipv6") @id(9)
          @composite_field(
              @sai_field(SAI_ACL_TABLE_ATTR_FIELD_DST_IPV6_WORD3),
              @sai_field(SAI_ACL_TABLE_ATTR_FIELD_DST_IPV6_WORD2)
          ) @format(IPV6_ADDRESS);
      // Field for v4 TTL and v6 hop_limit
      ttl : ternary @name("ttl") @id(10)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_TTL);
      // Field for v4 and v6 DSCP bits.
      dscp : ternary @name("dscp") @id(11)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_DSCP);
      // Field for v4 and v6 ECN bits.
      ecn : ternary @name("ecn") @id(12)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_ECN);
      // Field for v4 IP protocol and v6 next header.
      ip_protocol : ternary @name("ip_protocol") @id(13)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_IP_PROTOCOL);
#ifdef SAI_INSTANTIATION_FABRIC_BORDER_ROUTER
      headers.icmp.type : ternary @name("icmp_type") @id(19)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_ICMP_TYPE);
#endif
      headers.icmp.type : ternary @name("icmpv6_type") @id(14)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_ICMPV6_TYPE);
      local_metadata.l4_src_port : ternary @name("l4_src_port") @id(20)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_L4_SRC_PORT);
      local_metadata.l4_dst_port : ternary @name("l4_dst_port") @id(15)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_L4_DST_PORT);
#ifdef SAI_INSTANTIATION_MIDDLEBLOCK
      headers.arp.target_proto_addr : ternary @name("arp_tpa") @id(16)
          @composite_field(
              @sai_udf(base=SAI_UDF_BASE_L3, offset=24, length=2),
              @sai_udf(base=SAI_UDF_BASE_L3, offset=26, length=2)
          ) @format(IPV4_ADDRESS);
#endif
#ifdef SAI_INSTANTIATION_FABRIC_BORDER_ROUTER
      local_metadata.ingress_port : optional @name("in_port") @id(17)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_IN_PORT);
      local_metadata.route_metadata : optional @name("route_metadata") @id(18)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_ROUTE_DST_USER_META);
#endif
    }
    actions = {
      // TODO: add action to set color to yellow
      @proto_id(1) acl_copy();
      @proto_id(2) acl_trap();
      @proto_id(3) acl_forward();
      @proto_id(4) acl_mirror();
      @proto_id(5) acl_drop(standard_metadata);
      @proto_id(99) acl_experimental_trap();
      @defaultonly NoAction;
    }
    const default_action = NoAction;
    meters = acl_ingress_meter;
    counters = acl_ingress_counter;
    size = ACL_INGRESS_TABLE_MINIMUM_GUARANTEED_SIZE;
  }

  apply {
    if (headers.ipv4.isValid()) {
      ttl = headers.ipv4.ttl;
      dscp = headers.ipv4.dscp;
      ecn = headers.ipv4.ecn;
      ip_protocol = headers.ipv4.protocol;
    } else if (headers.ipv6.isValid()) {
      ttl = headers.ipv6.hop_limit;
      dscp = headers.ipv6.dscp;
      ecn = headers.ipv6.ecn;
      ip_protocol = headers.ipv6.next_header;
    }

    acl_ingress_table.apply();
  }
}  // control ACL_INGRESS

#endif  // SAI_ACL_INGRESS_P4_
