#ifndef SAI_ACL_PUNT_P4_
#define SAI_ACL_PUNT_P4_

#include "v1model.p4"
#include "headers.p4"
#include "metadata.p4"
#include "ids.h"
#include "resource_limits.p4"
#include "acl_actions.p4"

control acl_punt(inout headers_t headers,
                 inout local_metadata_t local_metadata,
                 inout standard_metadata_t standard_metadata) {

  @proto_package("sai")
  @id(ACL_PUNT_TABLE_ID)
  @sai_acl(INGRESS)
  table sai_punt_table {
    key = {
      headers.ethernet.ether_type : ternary @name("ether_type") @id(1)
          @sai_field(SAI_ACL_ENTRY_ATTR_FIELD_ETHER_TYPE);
      headers.ethernet.dst_addr : ternary @name("ether_dst") @id(2)
          @sai_field(SAI_ACL_ENTRY_ATTR_FIELD_DST_MAC) @format(MAC_ADDRESS);
      headers.ipv6.dst_addr : ternary @name("ipv6_dst") @id(3)
          @sai_field(SAI_ACL_ENTRY_ATTR_FIELD_DST_IPV6) @format(IPV6_ADDRESS);
      headers.ipv6.next_header : ternary @name("ipv6_next_header") @id(4)
          @sai_field(SAI_ACL_ENTRY_ATTR_FIELD_IPV6_NEXT_HEADER);
      headers.ipv6.hop_limit : ternary @name("ttl") @id(5)
          @sai_field(SAI_ACL_ENTRY_ATTR_FIELD_TTL);
      headers.icmp.type : ternary @name("icmp_type") @id(6)
          @sai_field(SAI_ACL_ENTRY_ATTR_FIELD_ICMP_TYPE);
      local_metadata.l4_dst_port : ternary @name("l4_dst_port") @id(7)
          @sai_field(SAI_ACL_ENTRY_ATTR_FIELD_L4_DST_PORT);
    }
    actions = {
      @proto_id(1) copy(standard_metadata);
      @proto_id(2) trap(standard_metadata);
      @defaultonly NoAction;
    }
    const default_action = NoAction;
    size = PUNT_TABLE_SIZE;
  }

  apply {
    sai_punt_table.apply();
  }
}  // control acl_punt

#endif  // SAI_ACL_PUNT_P4_
