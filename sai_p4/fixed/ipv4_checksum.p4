#ifndef SAI_IPV4_CHECKSUM_H_
#define SAI_IPV4_CHECKSUM_H_

#include "headers.p4"
#include "metadata.p4"

// IPv6 does not have a checksum, so this code is only for IPv4.

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

#endif  // SAI_IPV4_CHECKSUM_H_
