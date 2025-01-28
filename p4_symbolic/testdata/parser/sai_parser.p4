#define PLATFORM_P4SYMBOLIC
#include <v1model.p4>
#include "../common/headers.p4"

struct headers_t {
// TODO: Clean up once we have better solution to handle packet-in
// across platforms.
#if defined(PLATFORM_BMV2) || defined(PLATFORM_P4SYMBOLIC)
  // Never extracted during parsing, but serialized during deparsing for packets
  // punted to the controller.
  packet_in_header_t packet_in_header;
#endif

  // PacketOut header; extracted only for packets received from the controller.
  packet_out_header_t packet_out_header;

  // ERSPAN headers, not extracted during parsing.
  ethernet_t erspan_ethernet;
  ipv4_t erspan_ipv4;
  gre_t erspan_gre;

  ethernet_t ethernet;
  vlan_t vlan;

  // Not extracted during parsing.
  ipv6_t tunnel_encap_ipv6;
  gre_t tunnel_encap_gre;

  ipv4_t ipv4;
  ipv6_t ipv6;
  icmp_t icmp;
  tcp_t tcp;
  udp_t udp;
  arp_t arp;
}

// Header fields rewritten by the ingress pipeline. Rewrites are computed and
// stored in this struct, but actual rewriting is dealyed until the egress
// pipeline so that the original values aren't overridden and get be matched on.
struct packet_rewrites_t {
  ethernet_addr_t src_mac;
  ethernet_addr_t dst_mac;
}

// Local metadata for each packet being processed.
struct local_metadata_t {
  vlan_id_t vlan_id;
  // True iff `vlan_id` is valid.
  bool vlan_id_valid;
  bool admit_to_l3;
  vrf_id_t vrf_id;
  packet_rewrites_t packet_rewrites;
  bit<16> l4_src_port;
  bit<16> l4_dst_port;
  bit<WCMP_SELECTOR_INPUT_BITWIDTH> wcmp_selector_input;
  // GRE tunnel encap related fields.
  bool apply_tunnel_encap_at_egress;
  ipv6_addr_t tunnel_encap_src_ipv6;
  ipv6_addr_t tunnel_encap_dst_ipv6;
  // mirroring data, we can't group them into a struct, because BMv2 doesn't
  // support passing structs in clone3.
  bool mirror_session_id_valid;
  mirror_session_id_t mirror_session_id_value;
  @field_list(PreservedFieldList.MIRROR_AND_PACKET_IN_COPY)
  ipv4_addr_t mirroring_src_ip;
  @field_list(PreservedFieldList.MIRROR_AND_PACKET_IN_COPY)
  ipv4_addr_t mirroring_dst_ip;
  @field_list(PreservedFieldList.MIRROR_AND_PACKET_IN_COPY)
  ethernet_addr_t mirroring_src_mac;
  @field_list(PreservedFieldList.MIRROR_AND_PACKET_IN_COPY)
  ethernet_addr_t mirroring_dst_mac;
  @field_list(PreservedFieldList.MIRROR_AND_PACKET_IN_COPY)
  bit<8> mirroring_ttl;
  @field_list(PreservedFieldList.MIRROR_AND_PACKET_IN_COPY)
  bit<8> mirroring_tos;

  // Packet-in related fields, which we can't group into a struct, because BMv2
  // doesn't support passing structs in clone3.

  // The value to be copied into the `ingress_port` field of packet_in_header on
  // punted packets.
  @field_list(PreservedFieldList.MIRROR_AND_PACKET_IN_COPY)
  bit<PORT_BITWIDTH> packet_in_ingress_port;
  // The value to be copied into the `target_egress_port` field of
  // packet_in_header on punted packets.
  @field_list(PreservedFieldList.MIRROR_AND_PACKET_IN_COPY)
  bit<PORT_BITWIDTH> packet_in_target_egress_port;

  MeterColor_t color;
  // We consistently use local_metadata.ingress_port instead of
  // standard_metadata.ingress_port in the P4 tables to ensure that the P4Info
  // has port_id_t as the type for all fields that match on ports. This allows
  // tools to treat ports specially (e.g. a fuzzer).
  bit<9> ingress_port;
  // The following field corresponds to SAI_ROUTE_ENTRY_ATTR_META_DATA/
  // SAI_ACL_TABLE_ATTR_FIELD_ROUTE_DST_USER_META.
  route_metadata_t route_metadata;
  // ACL metadata can be set with SAI_ACL_ACTION_TYPE_SET_ACL_META_DATA, and
  // read from SAI_ACL_TABLE_ATTR_FIELD_ACL_USER_META.
  acl_metadata_t acl_metadata;
  // When controller sends a packet-out packet, the packet will be submitted to
  // the ingress pipleine by default. But sometimes we want to skip the ingress
  // pipeline for packet-out, and we cannot skip using the 'exit' statement as
  // it is not supported in p4-symbolic yet: b/184062335. So we use this field
  // as a workaround.
  // TODO: Clean up this workaround after 'exit' is supported in
  // p4-symbolic.
  bool bypass_ingress;
}

parser packet_parser(packet_in packet, out headers_t headers,
                     inout local_metadata_t local_metadata,
                     inout standard_metadata_t standard_metadata) {
  state start {
    // Initialize local metadata fields.
    local_metadata.vlan_id_valid = false;
    local_metadata.vlan_id = 0;
    local_metadata.admit_to_l3 = false;
    local_metadata.vrf_id = kDefaultVrf;
    local_metadata.packet_rewrites.src_mac = 0;
    local_metadata.packet_rewrites.dst_mac = 0;
    local_metadata.l4_src_port = 0;
    local_metadata.l4_dst_port = 0;
    local_metadata.wcmp_selector_input = 0;
    local_metadata.mirror_session_id_valid = false;
    local_metadata.color = MeterColor_t.GREEN;
    local_metadata.ingress_port = standard_metadata.ingress_port;
    local_metadata.route_metadata = 0;
    local_metadata.bypass_ingress = false;

    transition select(standard_metadata.ingress_port) {
      SAI_P4_CPU_PORT: parse_packet_out_header;
      _              : parse_ethernet;
    }
  }

  state parse_packet_out_header {
    packet.extract(headers.packet_out_header);
    transition parse_ethernet;
  }

  state parse_ethernet {
    packet.extract(headers.ethernet);
    transition select(headers.ethernet.ether_type) {
      ETHERTYPE_IPV4: parse_ipv4;
      ETHERTYPE_IPV6: parse_ipv6;
      ETHERTYPE_ARP:  parse_arp;
      ETHERTYPE_8021Q: parse_8021q_vlan;
      // VLAN double-tagging (ether_type 0x88a8) is not modeled as we do not
      // have a use case for it.
      _:              accept;
    }
  }

 state parse_8021q_vlan {
    packet.extract(headers.vlan);
    transition select(headers.vlan.ether_type) {
      ETHERTYPE_IPV4: parse_ipv4;
      ETHERTYPE_IPV6: parse_ipv6;
      ETHERTYPE_ARP:  parse_arp;
      _:              accept;
    }
  }

  state parse_ipv4 {
    packet.extract(headers.ipv4);
    transition select(headers.ipv4.protocol) {
      IP_PROTOCOL_ICMP: parse_icmp;
      IP_PROTOCOL_TCP:  parse_tcp;
      IP_PROTOCOL_UDP:  parse_udp;
      _:                accept;
    }
  }

  state parse_ipv6 {
    packet.extract(headers.ipv6);
    transition select(headers.ipv6.next_header) {
      IP_PROTOCOL_ICMPV6: parse_icmp;
      IP_PROTOCOL_TCP:    parse_tcp;
      IP_PROTOCOL_UDP:    parse_udp;
      _:                  accept;
    }
  }

  state parse_tcp {
    packet.extract(headers.tcp);
    // Normalize TCP port metadata to common port metadata.
    local_metadata.l4_src_port = headers.tcp.src_port;
    local_metadata.l4_dst_port = headers.tcp.dst_port;
    transition accept;
  }

  state parse_udp {
    packet.extract(headers.udp);
    // Normalize UDP port metadata to common port metadata.
    local_metadata.l4_src_port = headers.udp.src_port;
    local_metadata.l4_dst_port = headers.udp.dst_port;
    transition accept;
  }

  state parse_icmp {
    packet.extract(headers.icmp);
    transition accept;
  }

  state parse_arp {
    packet.extract(headers.arp);
    transition accept;
  }
}  // parser packet_parser

control verify_ipv4_checksum(inout headers_t headers,
                             inout local_metadata_t local_metadata) {
  apply {
    verify_checksum(headers.ipv4.isValid(), {
      headers.ipv4.version,
      headers.ipv4.ihl,
      headers.ipv4.dscp,
      headers.ipv4.ecn,
      headers.ipv4.total_len,
      headers.ipv4.identification,
      headers.ipv4.reserved,
      headers.ipv4.do_not_fragment,
      headers.ipv4.more_fragments,
      headers.ipv4.frag_offset,
      headers.ipv4.ttl,
      headers.ipv4.protocol,
      headers.ipv4.src_addr,
      headers.ipv4.dst_addr
    }, headers.ipv4.header_checksum, HashAlgorithm.csum16);
  }
}  // control verify_ipv4_checksum

control ingress(inout headers_t headers,
                inout local_metadata_t local_metadata,
                inout standard_metadata_t standard_metadata) {
  apply {}
}  // control ingress

control egress(inout headers_t headers,
               inout local_metadata_t local_metadata,
               inout standard_metadata_t standard_metadata) {
  apply {}
}  // control egress

control compute_ipv4_checksum(inout headers_t headers,
                              inout local_metadata_t local_metadata) {
  apply {
    update_checksum(headers.erspan_ipv4.isValid(), {
        headers.erspan_ipv4.version,
        headers.erspan_ipv4.ihl,
        headers.erspan_ipv4.dscp,
        headers.erspan_ipv4.ecn,
        headers.erspan_ipv4.total_len,
        headers.erspan_ipv4.identification,
        headers.erspan_ipv4.reserved,
        headers.erspan_ipv4.do_not_fragment,
        headers.erspan_ipv4.more_fragments,
        headers.erspan_ipv4.frag_offset,
        headers.erspan_ipv4.ttl,
        headers.erspan_ipv4.protocol,
        headers.erspan_ipv4.src_addr,
        headers.erspan_ipv4.dst_addr
      }, headers.erspan_ipv4.header_checksum, HashAlgorithm.csum16);

    update_checksum(headers.ipv4.isValid(), {
        headers.ipv4.version,
        headers.ipv4.ihl,
        headers.ipv4.dscp,
        headers.ipv4.ecn,
        headers.ipv4.total_len,
        headers.ipv4.identification,
        headers.ipv4.reserved,
        headers.ipv4.do_not_fragment,
        headers.ipv4.more_fragments,
        headers.ipv4.frag_offset,
        headers.ipv4.ttl,
        headers.ipv4.protocol,
        headers.ipv4.src_addr,
        headers.ipv4.dst_addr
      }, headers.ipv4.header_checksum, HashAlgorithm.csum16);
  }
}  // control compute_ipv4_checksum

control packet_deparser(packet_out packet, in headers_t headers) {
  apply {
    // We always expect the packet_out_header to be invalid at the end of the
    // pipeline, so this line has no effect on the output packet.
    packet.emit(headers.packet_out_header);
// TODO: Clean up once we have better solution to handle packet-in
// across platforms.
#if defined(PLATFORM_BMV2) || defined(PLATFORM_P4SYMBOLIC)
    packet.emit(headers.packet_in_header);
#endif
    packet.emit(headers.erspan_ethernet);
    packet.emit(headers.erspan_ipv4);
    packet.emit(headers.erspan_gre);
    packet.emit(headers.ethernet);
    packet.emit(headers.vlan);
    packet.emit(headers.tunnel_encap_ipv6);
    packet.emit(headers.tunnel_encap_gre);
    packet.emit(headers.ipv4);
    packet.emit(headers.ipv6);
    packet.emit(headers.arp);
    packet.emit(headers.icmp);
    packet.emit(headers.tcp);
    packet.emit(headers.udp);
  }
}  // control packet_deparser

V1Switch(
  packet_parser(),
  verify_ipv4_checksum(),
  ingress(),
  egress(),
  compute_ipv4_checksum(),
  packet_deparser()
) main;
