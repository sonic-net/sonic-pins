#ifndef SAI_L3_ADMIT_P4_
#define SAI_L3_ADMIT_P4_

#include <v1model.p4>
#include "headers.p4"
#include "metadata.p4"
#include "ids.h"
#include "roles.h"
#include "minimum_guaranteed_sizes.h"

control l3_admit(in headers_t headers,
                 inout local_metadata_t local_metadata,
                 in standard_metadata_t standard_metadata) {
  @id(L3_ADMIT_ACTION_ID)
  action admit_to_l3() {
    local_metadata.admit_to_l3 = true;
  }

  @p4runtime_role(P4RUNTIME_ROLE_ROUTING)
  @id(L3_ADMIT_TABLE_ID)
  table l3_admit_table {
    key = {
      headers.ethernet.dst_addr : ternary @name("dst_mac") @id(1)
                                          @format(MAC_ADDRESS);
#if defined(L3_ADMIT_SUPPORTS_IN_PORT)
      local_metadata.ingress_port : optional @name("in_port") @id(2);
#endif
    }
    actions = {
      @proto_id(1) admit_to_l3;
      @defaultonly NoAction;
    }
    const default_action = NoAction;
    size = L3_ADMIT_TABLE_MINIMUM_GUARANTEED_SIZE;
  }

  apply {
    if (local_metadata.marked_to_drop_by_ingress_vlan_checks) {
      // Explicitly reject VLAN tagged packets that fail ingress VLAN checks
      // from L3 routing to cancel override in other parts of the code
      local_metadata.admit_to_l3 = false;
    } else {
      l3_admit_table.apply();
    }
  }
}  // control l3_admit

#endif  // SAI_L3_ADMIT_P4_
