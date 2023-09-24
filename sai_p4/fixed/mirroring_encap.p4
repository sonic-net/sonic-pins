#ifndef SAI_MIRRORING_ENCAP_P4_
#define SAI_MIRRORING_ENCAP_P4_

#include <v1model.p4>
#include "headers.p4"
#include "metadata.p4"
#include "ids.h"
#include "minimum_guaranteed_sizes.p4"
#include "bmv2_intrinsics.h"

control mirroring_encap(inout headers_t headers,
                        inout local_metadata_t local_metadata,
                        inout standard_metadata_t standard_metadata) {
  apply {
    if (IS_MIRROR_COPY(standard_metadata)) {

      // Reference for ERSPAN Type II header construction
      // https://tools.ietf.org/html/draft-foschiano-erspan-00
      headers.erspan_ethernet.setValid();
      headers.erspan_ethernet.src_addr = local_metadata.mirroring_src_mac;
      headers.erspan_ethernet.dst_addr = local_metadata.mirroring_dst_mac;
      headers.erspan_ethernet.ether_type = ETHERTYPE_IPV4;

      headers.erspan_ipv4.setValid();
      headers.erspan_ipv4.src_addr = local_metadata.mirroring_src_ip;
      headers.erspan_ipv4.dst_addr = local_metadata.mirroring_dst_ip;
      headers.erspan_ipv4.version = 4w4;
      headers.erspan_ipv4.ihl = 4w5;
      headers.erspan_ipv4.protocol = IP_PROTOCOLS_GRE;
      headers.erspan_ipv4.ttl = local_metadata.mirroring_ttl;
      headers.erspan_ipv4.dscp = local_metadata.mirroring_tos[7:2];
      headers.erspan_ipv4.ecn = local_metadata.mirroring_tos[1:0];
      headers.erspan_ipv4.total_len = IPV4_HEADER_BYTES + GRE_HEADER_BYTES +
                                      (bit<16>)standard_metadata.packet_length;
      headers.erspan_ipv4.identification = 0;
      headers.erspan_ipv4.reserved = 0;
      headers.erspan_ipv4.do_not_fragment = 1;
      headers.erspan_ipv4.more_fragments = 0;
      headers.erspan_ipv4.frag_offset = 0;
      headers.erspan_ipv4.header_checksum = 0;

      headers.erspan_gre.setValid();
      headers.erspan_gre.checksum_present = 0;
      headers.erspan_gre.routing_present = 0;
      headers.erspan_gre.key_present = 0;
      headers.erspan_gre.sequence_present = 0;
      headers.erspan_gre.strict_source_route = 0;
      headers.erspan_gre.recursion_control = 0;
      headers.erspan_gre.acknowledgement_present = 0;
      headers.erspan_gre.flags = 0;
      headers.erspan_gre.version = 0;
      headers.erspan_gre.protocol = GRE_PROTOCOL_ERSPAN;
    }
  }
}  // control mirroring_encap

#endif  // SAI_MIRRORING_ENCAP_P4_
