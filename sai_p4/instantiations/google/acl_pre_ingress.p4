#ifndef SAI_ACL_PRE_INGRESS_P4_
#define SAI_ACL_PRE_INGRESS_P4_

#include <v1model.p4>
#include "../../fixed/headers.p4"
#include "../../fixed/metadata.p4"
#include "ids.h"
#include "roles.h"
#include "minimum_guaranteed_sizes.p4"

control acl_pre_ingress(in headers_t headers,
                   inout local_metadata_t local_metadata,
                   in standard_metadata_t standard_metadata) {
  // First 6 bits of IPv4 TOS or IPv6 traffic class (or 0, for non-IP packets)
  bit<6> dscp = 0;

  @id(ACL_PRE_INGRESS_COUNTER_ID)
  direct_counter(CounterType.packets_and_bytes) acl_pre_ingress_counter;

  @id(ACL_PRE_INGRESS_SET_VRF_ACTION_ID)
  @sai_action(SAI_PACKET_ACTION_FORWARD)
  action set_vrf(@sai_action_param(SAI_ACL_ENTRY_ATTR_ACTION_SET_VRF)
                 @refers_to(vrf_table, vrf_id)
                 @id(1)
                 vrf_id_t vrf_id) {
    local_metadata.vrf_id = vrf_id;
    acl_pre_ingress_counter.count();
  }

  @p4runtime_role(P4RUNTIME_ROLE_SDN_CONTROLLER)
  @id(ACL_PRE_INGRESS_TABLE_ID)
  @sai_acl(PRE_INGRESS)
  @entry_restriction("
    // Only allow IP field matches for IP packets.
    dscp::mask != 0 -> (is_ip == 1 || is_ipv4 == 1 || is_ipv6 == 1);
    dst_ip::mask != 0 -> is_ipv4 == 1;
    dst_ipv6::mask != 0 -> is_ipv6 == 1;
    // Forbid illegal combinations of IP_TYPE fields.
    is_ip::mask != 0 -> (is_ipv4::mask == 0 && is_ipv6::mask == 0);
    is_ipv4::mask != 0 -> (is_ip::mask == 0 && is_ipv6::mask == 0);
    is_ipv6::mask != 0 -> (is_ip::mask == 0 && is_ipv4::mask == 0);
    // Forbid unsupported combinations of IP_TYPE fields.
    is_ipv4::mask != 0 -> (is_ipv4 == 1);
    is_ipv6::mask != 0 -> (is_ipv6 == 1);
    // Reserve high priorities for switch-internal use.
    // TODO: Remove once inband workaround is obsolete.
    ::priority < 0x7fffffff;
  ")
  table acl_pre_ingress_table {
    key = {
      headers.ipv4.isValid() || headers.ipv6.isValid() : optional @name("is_ip") @id(1)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_ACL_IP_TYPE/IP);
      headers.ipv4.isValid() : optional @name("is_ipv4") @id(2)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_ACL_IP_TYPE/IPV4ANY);
      headers.ipv6.isValid() : optional @name("is_ipv6") @id(3)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_ACL_IP_TYPE/IPV6ANY);
      headers.ethernet.src_addr : ternary @name("src_mac") @id(4)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_SRC_MAC) @format(MAC_ADDRESS);
#ifdef SAI_INSTANTIATION_FABRIC_BORDER_ROUTER
      headers.ethernet.dst_addr : ternary @name("dst_mac") @id(9)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_DST_MAC) @format(MAC_ADDRESS);
#endif
      headers.ipv4.dst_addr : ternary @name("dst_ip") @id(5)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_DST_IP) @format(IPV4_ADDRESS);
      headers.ipv6.dst_addr[127:64] : ternary @name("dst_ipv6") @id(6)
          @composite_field(
              @sai_field(SAI_ACL_TABLE_ATTR_FIELD_DST_IPV6_WORD3),
              @sai_field(SAI_ACL_TABLE_ATTR_FIELD_DST_IPV6_WORD2)
          ) @format(IPV6_ADDRESS);
      dscp : ternary @name("dscp") @id(7)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_DSCP);
      local_metadata.ingress_port : optional @name("in_port") @id(8)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_IN_PORT);
    }
    actions = {
      @proto_id(1) set_vrf;
      @defaultonly NoAction;
    }
    const default_action = NoAction;
    counters = acl_pre_ingress_counter;
    size = ACL_PRE_INGRESS_TABLE_MINIMUM_GUARANTEED_SIZE;
  }

  apply {
    if (headers.ipv4.isValid()) {
      dscp = headers.ipv4.dscp;
    } else if (headers.ipv6.isValid()) {
      dscp = headers.ipv6.dscp;
    }

    local_metadata.vrf_id = kDefaultVrf;
    acl_pre_ingress_table.apply();
  }
}  // control acl_pre_ingress

#endif  // SAI_ACL_PRE_INGRESS_P4_
