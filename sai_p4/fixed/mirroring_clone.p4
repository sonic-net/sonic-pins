#ifndef SAI_MIRRORING_CLONE_P4_
#define SAI_MIRRORING_CLONE_P4_

#include <v1model.p4>
#include "headers.p4"
#include "metadata.p4"
#include "ids.h"
#include "roles.h"
#include "minimum_guaranteed_sizes.p4"

control mirroring_clone(inout headers_t headers,
                        inout local_metadata_t local_metadata,
                        inout standard_metadata_t standard_metadata) {
  port_id_t mirror_port;
  bit<32> pre_session;

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
  @id(MIRRORING_MIRROR_AS_IPV4_ERSPAN_ACTION_ID)
  action mirror_as_ipv4_erspan(
      @id(1) port_id_t port,
      @id(2) @format(IPV4_ADDRESS) ipv4_addr_t src_ip,
      @id(3) @format(IPV4_ADDRESS) ipv4_addr_t dst_ip,
      @id(4) @format(MAC_ADDRESS) ethernet_addr_t src_mac,
      @id(5) @format(MAC_ADDRESS) ethernet_addr_t dst_mac,
      @id(6) bit<8> ttl,
      @id(7) bit<8> tos) {
    mirror_port = port;
    local_metadata.mirroring_src_ip = src_ip;
    local_metadata.mirroring_dst_ip = dst_ip;
    local_metadata.mirroring_src_mac = src_mac;
    local_metadata.mirroring_dst_mac = dst_mac;
    local_metadata.mirroring_ttl = ttl;
    local_metadata.mirroring_tos = tos;
  }

  @p4runtime_role(P4RUNTIME_ROLE_MIRRORING)
  @id(MIRROR_SESSION_TABLE_ID)
  table mirror_session_table {
    key = {
      local_metadata.mirror_session_id_value : exact @id(1)
                                                     @name("mirror_session_id");
    }
    actions = {
      @proto_id(1) mirror_as_ipv4_erspan;
      @defaultonly NoAction;
    }
    const default_action = NoAction;
    size = MIRROR_SESSION_TABLE_MINIMUM_GUARANTEED_SIZE;
  }

  @id(MIRRORING_SET_PRE_SESSION_ACTION_ID)
  action set_pre_session(bit<32> id) {
    pre_session = id;
  }

  @p4runtime_role(P4RUNTIME_ROLE_PACKET_REPLICATION_ENGINE)
  @id(MIRROR_PORT_TO_PRE_SESSION_TABLE_ID)
  table mirror_port_to_pre_session_table {
    key = {
      mirror_port : exact @id(1);
    }
    actions = {
      @proto_id(1) set_pre_session;
      @defaultonly NoAction;
    }
    const default_action = NoAction;
  }

  apply {
    if (local_metadata.mirror_session_id_valid) {
      // Map mirror session id to mirroring data.
      if (mirror_session_table.apply().hit) {
        // Map mirror port to Packet Replication Engine session.
        if (mirror_port_to_pre_session_table.apply().hit) {
          clone_preserving_field_list(
            CloneType.I2E, pre_session,
            (bit<8>)PreservedFieldList.MIRROR_AND_PACKET_IN_COPY);
        }
      }
    }
  }
}  // control mirroring_clone

#endif  // SAI_MIRRORING_CLONE_P4_
