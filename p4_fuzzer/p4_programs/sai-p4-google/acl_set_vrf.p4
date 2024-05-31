#ifndef SAI_ACL_SET_VRF_P4_
#define SAI_ACL_SET_VRF_P4_

#include "v1model.p4"
#include "headers.p4"
#include "metadata.p4"
#include "ids.h"
#include "resource_limits.p4"
#include "acl_actions.p4"

control acl_set_vrf(inout headers_t headers,
                    inout local_metadata_t local_metadata,
                    inout standard_metadata_t standard_metadata) {

  @id(ACL_SET_VRF_SET_VRF_ACTION_ID)
  @sai_action(SAI_PACKET_ACTION_FORWARD)
  action set_vrf(@sai_action_param(SAI_ACL_ENTRY_ATTR_ACTION_SET_VRF)
                 @id(1) vrf_id_t vrf_id) {
    local_metadata.vrf_id = vrf_id;
  }

  @proto_package("sai")
  @id(ACL_SET_VRF_TABLE_ID)
  @sai_acl(PREINGRESS)
  @entry_constraint("ether_type == 0x86DD")
  table set_vrf_table {
    key = {
      headers.ethernet.ether_type : exact @name("ether_type") @id(1)
          @sai_field(SAI_ACL_ENTRY_ATTR_FIELD_ETHER_TYPE);
      headers.ipv6.dst_addr : ternary @name("ipv6_dst") @id(2)
          @sai_field(SAI_ACL_ENTRY_ATTR_FIELD_DST_IPV6) @format(IPV6_ADDRESS);
      headers.ipv6.dscp : ternary @name("dscp") @id(3)
          @sai_field(SAI_ACL_ENTRY_ATTR_FIELD_DSCP);
    }
    actions = {
      @proto_id(1) set_vrf;
      @defaultonly NoAction;
    }
    const default_action = NoAction;
    size = SET_VRF_TABLE_SIZE;
  }

  apply {
    set_vrf_table.apply();
  }
}  // control acl_set_vrf

#endif  // SAI_ACL_SET_VRF_P4_
