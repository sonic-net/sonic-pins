#ifndef SAI_MIRRORING_P4_
#define SAI_MIRRORING_P4_

#include <v1model.p4>
#include "headers.p4"
#include "metadata.p4"
#include "ids.h"
#include "minimum_guaranteed_sizes.p4"
#include "bmv2_intrinsics.h"

control mirror_session_lookup(inout headers_t headers,
                              inout local_metadata_t local_metadata,
                              inout standard_metadata_t standard_metadata) {
  // Sets
  // SAI_MIRROR_SESSION_ATTR_TYPE to ENHANCED_REMOTE,
  // SAI_MIRROR_SESSION_ATTR_ERSPAN_ENCAPSULATION_TYPE to L3_GRE_TUNNEL,
  // SAI_MIRROR_SESSION_ATTR_IPHDR_VERSION to 4,
  // SAI_MIRROR_SESSION_ATTR_GRE_PROTOCOL_TYPE to 0x88BE,
  // SAI_MIRROR_SESSION_ATTR_MONITOR_PORT,
  // SAI_MIRROR_SESSION_ATTR_SRC_IP_ADDRESS,
  // SAI_MIRROR_SESSION_ATTR_DST_IP_ADDRESS,
  // SAI_MIRROR_SESSION_ATTR_SRC_MAC_ADDRESS
  // SAI_MIRROR_SESSION_ATTR_DST_MAC_ADDRESS
  // SAI_MIRROR_SESSION_ATTR_TTL
  // SAI_MIRROR_SESSION_ATTR_TOS
  // TODO: Remove mirror_as_ipv4_erspan once the the switch
  // supports mirror_with_psamp_encapsulation. This action is currently needed
  // for mirror_session_table since it is the only action by the switch in this
  // table.
  @id(MIRRORING_MIRROR_AS_IPV4_ERSPAN_ACTION_ID)
  action mirror_as_ipv4_erspan(
      @id(1) port_id_t port,
      @id(2) @format(IPV4_ADDRESS) ipv4_addr_t src_ip,
      @id(3) @format(IPV4_ADDRESS) ipv4_addr_t dst_ip,
      @id(4) @format(MAC_ADDRESS) ethernet_addr_t src_mac,
      @id(5) @format(MAC_ADDRESS) ethernet_addr_t dst_mac,
      @id(6) bit<8> ttl,
      @id(7) bit<8> tos) {
  }

  // Sets
  // * SAI_MIRROR_SESSION_ATTR_TYPE to SAI_MIRROR_SESSION_TYPE_PSAMP
  // * SAI_MIRROR_SESSION_ATTR_PSAMP_ENCAPSULATION_TYPE to
  // SAI_PSAMP_ENCAPSULATION_TYPE_EXTENDED
  // * SAI_MIRROR_SESSION_ATTR_MONITOR_PORT to `monitor_port`
  @id(CLONING_MIRROR_WITH_PSAMP_ENCAPSULATION_ACTION_ID)
  // TODO: Add params needed for PSAMP mirroring.
  // TODO: Remove unsupported annotation once the switch stack
  // supports this table.
  @unsupported
  action mirror_with_psamp_encapsulation(@id(1) port_id_t monitor_port) {
    local_metadata.mirror_egress_port = monitor_port;
  }

  // Corresponding SAI object: SAI_OBJECT_TYPE_MIRROR_SESSION

  @p4runtime_role(P4RUNTIME_ROLE_SDN_CONTROLLER)
  @id(MIRROR_SESSION_TABLE_ID)
  table mirror_session_table {
    key = {
      local_metadata.mirror_session_id : exact
        @id(1) @name("mirror_session_id");
    }
    actions = {
      @proto_id(1) mirror_as_ipv4_erspan;
      @proto_id(2) mirror_with_psamp_encapsulation;
      @defaultonly NoAction;
    }

    const default_action = NoAction;
    size = MIRROR_SESSION_TABLE_MINIMUM_GUARANTEED_SIZE;
  }

  apply {
    // TODO: Consider unconditionally apply mirror_session_table.
    if (local_metadata.marked_to_mirror) {
      mirror_session_table.apply();
    }
  }
}  // control mirror_session_lookup

control mirroring_encap(inout headers_t headers,
                        inout local_metadata_t local_metadata,
                        inout standard_metadata_t standard_metadata) {
  apply {
    if (IS_MIRROR_COPY(standard_metadata)) {
      // TODO: Implements mirroring encap.
    }
  }
}  // control mirroring_encap

#endif  // SAI_MIRRORING_P4_
