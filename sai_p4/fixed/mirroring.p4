#ifndef SAI_MIRRORING_P4_
#define SAI_MIRRORING_P4_

#include <v1model.p4>
#include "headers.p4"
#include "metadata.p4"
#include "ids.h"
#include "minimum_guaranteed_sizes.h"
#include "bmv2_intrinsics.h"

control mirror_session_lookup(inout headers_t headers,
                              inout local_metadata_t local_metadata,
                              inout standard_metadata_t standard_metadata) {

  // Sets
  // * SAI_MIRROR_SESSION_ATTR_TYPE to SAI_MIRROR_SESSION_TYPE_IPFIX
  // * SAI_MIRROR_SESSION_ATTR_IPFIX_ENCAPSULATION_TYPE to
  //   SAI_IPFIX_ENCAPSULATION_TYPE_EXTENDED
  // * SAI_MIRROR_SESSION_ATTR_MONITOR_PORT to `monitor_port`
  // * SAI_MIRROR_SESSION_ATTR_SRC_MAC_ADDRESS
  // * SAI_MIRROR_SESSION_ATTR_DST_MAC_ADDRESS
  // * SAI_MIRROR_SESSION_ATTR_VLAN_TPID
  // * SAI_MIRROR_SESSION_ATTR_VLAN_ID
  // * SAI_MIRROR_SESSION_ATTR_SRC_IP_ADDRESS
  // * SAI_MIRROR_SESSION_ATTR_DST_IP_ADDRESS
  // * SAI_MIRROR_SESSION_ATTR_UDP_SRC_PORT
  // * SAI_MIRROR_SESSION_ATTR_UDP_DST_PORT
  //
  // `monitor_failover_port` is used by OrchAgent to update
  // SAI_MIRROR_SESSION_ATTR_MONITOR_PORT when `monitor_port` goes down.
  // monitor_failover_port is not associated with any SAI ATTR But OrchAgent
  // will switch to using it when `monitor_port` goes down.
  // This is similar to how OrchAgent handles watch ports.
  @id(CLONING_MIRROR_WITH_VLAN_TAG_AND_IPFIX_ENCAPSULATION_ACTION_ID)
  action mirror_with_vlan_tag_and_ipfix_encapsulation(
      @id(1) port_id_t monitor_port,
      @id(2) port_id_t monitor_failover_port,
      @id(3) @format(MAC_ADDRESS) ethernet_addr_t mirror_encap_src_mac,
      @id(4) @format(MAC_ADDRESS) ethernet_addr_t mirror_encap_dst_mac,
      @id(6) vlan_id_t mirror_encap_vlan_id,
      @id(7) @format(IPV6_ADDRESS) ipv6_addr_t mirror_encap_src_ip,
      @id(8) @format(IPV6_ADDRESS) ipv6_addr_t mirror_encap_dst_ip,
      @id(9) bit<16> mirror_encap_udp_src_port,
      @id(10) bit<16> mirror_encap_udp_dst_port) {
    local_metadata.mirror_egress_port = monitor_port;
    // monitor_failover_port's effect is not modeled.
    local_metadata.mirror_encap_src_mac = mirror_encap_src_mac;
    local_metadata.mirror_encap_dst_mac = mirror_encap_dst_mac;
    local_metadata.mirror_encap_vlan_id = mirror_encap_vlan_id;
    local_metadata.mirror_encap_src_ip = mirror_encap_src_ip;
    local_metadata.mirror_encap_dst_ip = mirror_encap_dst_ip;
    local_metadata.mirror_encap_udp_src_port = mirror_encap_udp_src_port;
    local_metadata.mirror_encap_udp_dst_port = mirror_encap_udp_dst_port;
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
      @proto_id(1) mirror_with_vlan_tag_and_ipfix_encapsulation;
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
    // All mirrored packets are encapped with
    // ==================================================================
    // | Ethernet + vlan | IPv6 | UDP | IPFIX + PSAMP extended| payload |
    // ==================================================================
    // headers. Fields for headers mostly come from mirror-related
    // local_metadata.
    if (IS_MIRROR_COPY(standard_metadata)) {
      headers.mirror_encap_ethernet.setValid();
      headers.mirror_encap_ethernet.src_addr =
       local_metadata.mirror_encap_src_mac;
      headers.mirror_encap_ethernet.dst_addr =
       local_metadata.mirror_encap_dst_mac;
      headers.mirror_encap_ethernet.ether_type = ETHERTYPE_8021Q;  // VLAN

      headers.mirror_encap_vlan.setValid();
      headers.mirror_encap_vlan.ether_type = ETHERTYPE_IPV6;
      headers.mirror_encap_vlan.vlan_id = local_metadata.mirror_encap_vlan_id;

      headers.mirror_encap_ipv6.setValid();
      headers.mirror_encap_ipv6.version = 4w6;
      // Mirrored packets' traffic class is 0.
      headers.mirror_encap_ipv6.dscp = 0;
      headers.mirror_encap_ipv6.ecn = 0;
      // Mirrored packets' hop_limit is 16.
      headers.mirror_encap_ipv6.hop_limit = 16;
      headers.mirror_encap_ipv6.flow_label = 0;
      // payload_lentgh for ipv6 packets is the byte length of headers after
      // ipv6 + payload. in our case, that's the UDP, IPFIX and PSAMP headers.
      // The mirror replicated packet becomes the new payload during mirror
      // encap, so standard_metadata.packet_length becomes the payload length.
      // contains the length of payload + all headers.
      headers.mirror_encap_ipv6.payload_length =
        (bit<16>)standard_metadata.packet_length
        + UDP_HEADER_BYTES
        + IPFIX_HEADER_BYTES
        + PSAMP_EXTENDED_BYTES;
      headers.mirror_encap_ipv6.next_header = IP_PROTOCOL_UDP;
      headers.mirror_encap_ipv6.src_addr = local_metadata.mirror_encap_src_ip;
      headers.mirror_encap_ipv6.dst_addr = local_metadata.mirror_encap_dst_ip;

      headers.mirror_encap_udp.setValid();
      headers.mirror_encap_udp.src_port =
        local_metadata.mirror_encap_udp_src_port;
      headers.mirror_encap_udp.dst_port =
        local_metadata.mirror_encap_udp_dst_port;
      headers.mirror_encap_udp.hdr_length =
        headers.mirror_encap_ipv6.payload_length;
      // Mirrored packets' UDP checksum is 0.
      headers.mirror_encap_udp.checksum = 0;

      // IPFIX and PSAMP fields are opaque to P4 so we only set their headers
      // as valid.
      headers.mirror_encap_ipfix.setValid();
      headers.mirror_encap_psamp_extended.setValid();
    }
  }
}  // control mirroring_encap

#endif  // SAI_MIRRORING_P4_
