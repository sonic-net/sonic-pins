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
  // IPv4 IP protocol or IPv6 next_header (or 0, for non-IP packets)
  bit<8> ip_protocol = 0;

  @p4runtime_role(P4RUNTIME_ROLE_SDN_CONTROLLER)
  @id(ACL_EGRESS_TABLE_ID)
  @sai_acl(EGRESS)

  table acl_egress_table {
    key = {
      headers.ethernet.ether_type : ternary @name("ether_type") @id(1)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_ETHER_TYPE);
      ip_protocol : ternary @name("ip_protocol") @id(2)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_IP_PROTOCOL);
      local_metadata.l4_dst_port : ternary @name("l4_dst_port") @id(3)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_L4_DST_PORT);
      (port_id_t)standard_metadata.egress_port: optional @name("out_port") @id(4)
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_OUT_PORT);
    }
    actions = {
      @proto_id(1) acl_drop(standard_metadata);
      @defaultonly NoAction;
    }
    const default_action = NoAction;
    size = ACL_EGRESS_TABLE_MINIMUM_GUARANTEED_SIZE;
  }

  apply {
    acl_egress_table.apply();
  }
}  // control ACL_EGRESS

#endif  // SAI_ACL_EGRESS_P4_
