#ifndef SAI_ACL_EGRESS_P4_
#define SAI_ACL_EGRESS_P4_

#include <v1model.p4>
#include "../../fixed/headers.p4"
#include "../../fixed/metadata.p4"
#include "acl_common_actions.p4"
#include "ids.h"
#include "minimum_guaranteed_sizes.p4"
#include "roles.h"

control acl_egress(in headers_t headers,
                    inout local_metadata_t local_metadata,
                    inout standard_metadata_t standard_metadata) {
  // First 6 bits of IPv4 TOS or IPv6 traffic class (or 0, for non-IP packets)
  bit<6> dscp = 0;
  // IPv4 IP protocol or IPv6 next_header (or 0, for non-IP packets)
  bit<8> ip_protocol = 0;

  @id(ACL_EGRESS_COUNTER_ID)
  direct_counter(CounterType.packets_and_bytes) acl_egress_counter;

  @p4runtime_role(P4RUNTIME_ROLE_SDN_CONTROLLER)
  @id(ACL_EGRESS_TABLE_ID)
  @sai_acl(EGRESS)
  @entry_restriction("
    // Forbid using ether_type for IP packets (by convention, use is_ip* instead).
    ether_type != 0x0800 && ether_type != 0x86dd;
    dscp::mask != 0 -> (is_ip == 1 || is_ipv4 == 1 || is_ipv6 == 1);
    // Only allow IP field matches for IP packets.
    // TODO: Enable once p4-constraints bug is fixed.
    // ip_protocol::mask != 0 -> (is_ip == 1 || is_ipv4 == 1 || is_ipv6 == 1);
    // Only allow l4_dst_port matches for TCP/UDP packets.
    l4_dst_port::mask != 0 -> (ip_protocol == 6 || ip_protocol == 17);
    // Forbid illegal combinations of IP_TYPE fields.
    is_ip::mask != 0 -> (is_ipv4::mask == 0 && is_ipv6::mask == 0);
    is_ipv4::mask != 0 -> (is_ip::mask == 0 && is_ipv6::mask == 0);
    is_ipv6::mask != 0 -> (is_ip::mask == 0 && is_ipv4::mask == 0);
    // Forbid unsupported combinations of IP_TYPE fields.
    is_ipv4::mask != 0 -> (is_ipv4 == 1);
    is_ipv6::mask != 0 -> (is_ipv6 == 1);
  ")
  table acl_egress_table {
    key = {
      headers.ethernet.ether_type : ternary @name("ether_type") @id(1)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_ETHER_TYPE);
      ip_protocol : ternary @name("ip_protocol") @id(2)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_IP_PROTOCOL);
      local_metadata.l4_dst_port : ternary @name("l4_dst_port") @id(3)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_L4_DST_PORT);
      (port_id_t)standard_metadata.egress_port: optional @name("out_port")
          @id(4) @sai_field(SAI_ACL_TABLE_ATTR_FIELD_OUT_PORT);
      headers.ipv4.isValid() || headers.ipv6.isValid() : optional @name("is_ip")
          @id(5) @sai_field(SAI_ACL_TABLE_ATTR_FIELD_ACL_IP_TYPE/IP);
      headers.ipv4.isValid() : optional @name("is_ipv4") @id(6)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_ACL_IP_TYPE/IPV4ANY);
      headers.ipv6.isValid() : optional @name("is_ipv6") @id(7)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_ACL_IP_TYPE/IPV6ANY);
      // Field for v4 and v6 DSCP bits.
      dscp : ternary @name("dscp") @id(8)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_DSCP);
    }
    actions = {
      @proto_id(1) acl_drop(standard_metadata);
      @defaultonly NoAction;
    }
    const default_action = NoAction;
    counters = acl_egress_counter;
    size = ACL_EGRESS_TABLE_MINIMUM_GUARANTEED_SIZE;
  }

  apply {
    if (headers.ipv4.isValid()) {
      dscp = headers.ipv4.dscp;
      ip_protocol = headers.ipv4.protocol;
    } else if (headers.ipv6.isValid()) {
      dscp = headers.ipv6.dscp;
      ip_protocol = headers.ipv6.next_header;
    } else {
      ip_protocol = 0;
    }

    acl_egress_table.apply();
  }
}  // control ACL_EGRESS

#endif  // SAI_ACL_EGRESS_P4_
