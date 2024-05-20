#ifndef SAI_PUNT_ACL_P4_
#define SAI_PUNT_ACL_P4_

#include "v1model.p4"
#include "headers.p4"
#include "metadata.p4"
#include "ids.h"
#include "resource_limits.p4"
#include "acl_actions.p4"

control punt_acl(inout headers_t headers,
                 inout local_metadata_t local_metadata,
                 inout standard_metadata_t standard_metadata) {

  @proto_package("punt")
  @id(PUNT_ACL_TABLE_ID)
  @sai_acl(INGRESS)
  table punt_table {
    key = {
      headers.ethernet.ether_type : ternary @name("ether_type")
          @proto_tag(1) @sai_field(SAI_ACL_ENTRY_ATTR_FIELD_ETHER_TYPE);
      headers.ethernet.dst_addr : ternary @name("ether_dst")
          @proto_tag(2) @sai_field(SAI_ACL_ENTRY_ATTR_FIELD_DST_MAC);
      headers.ipv6.dst_addr : ternary @name("ipv6_dst")
          @proto_tag(3) @sai_field(SAI_ACL_ENTRY_ATTR_FIELD_DST_IPV6);
      headers.ipv6.next_header : ternary @name("ipv6_next_header")
          @proto_tag(4) @sai_field(SAI_ACL_ENTRY_ATTR_FIELD_IPV6_NEXT_HEADER);
      headers.ipv6.hop_limit : ternary @name("ttl")
          @proto_tag(5) @sai_field(SAI_ACL_ENTRY_ATTR_FIELD_TTL);
      headers.icmp.type : ternary @name("icmp_type")
          @proto_tag(6) @sai_field(SAI_ACL_ENTRY_ATTR_FIELD_ICMP_TYPE);
      local_metadata.l4_dst_port : ternary @name("l4_dst_port")
          @proto_tag(7) @sai_field(SAI_ACL_ENTRY_ATTR_FIELD_L4_DST_PORT);
    }
    actions = {
      @proto_tag(1) copy(standard_metadata);
      @proto_tag(2) trap(standard_metadata);
    }
    size = PUNT_TABLE_SIZE;
  }

  apply {
    punt_table.apply();
  }
}  // control punt_acl

#endif  // SAI_PUNT_ACL_P4_
