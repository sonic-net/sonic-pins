#ifndef SAI_LOOPBACK_P4_
#define SAI_LOOPBACK_P4_

#include <v1model.p4>
#include "headers.p4"
#include "metadata.p4"
#include "ids.h"
#include "bmv2_intrinsics.h"


control egress_port_loopback(inout headers_t headers,
                        inout local_metadata_t local_metadata,
                        inout standard_metadata_t standard_metadata) {
  @id(EGRESS_LOOPBACK_ACTION_ID)
  action egress_loopback() {
    local_metadata.loopback_port = standard_metadata.egress_port;
    recirculate_preserving_field_list((bit<8>)PreservedFieldList.RECIRCULATE);
  }

  // This table models SAI_PORT_LOOPBACK_MODE_MAC on front panel ports: an entry
  // in this table matching on an `out_port` P indicates that a packet going
  // out of P will be recirculated back as an input packet.
  // This table is only used in v1model targets (e.g. BMv2).
  // The loopback mode is configured via gNMI config for the port rather than
  // P4.
  @id(EGRESS_PORT_LOOPBACK_TABLE_ID)
  @p4runtime_role(P4RUNTIME_ROLE_V1MODEL_AUXILIARY_CONTROLLER)
  // TODO: Remove @unsupported once we can ignore this table
  // in P4Info verification
  @unsupported
  table egress_port_loopback_table {
    key = {
      (port_id_t)standard_metadata.egress_port: exact
          @id(1) @name("out_port");
    }
    actions = {
      @proto_id(1) egress_loopback;
      @defaultonly NoAction;
    }
    const default_action = NoAction;
  }

  apply {
    egress_port_loopback_table.apply();
  }
}  // control egress_port_loopback

#endif  // SAI_LOOPBACK_P4_
