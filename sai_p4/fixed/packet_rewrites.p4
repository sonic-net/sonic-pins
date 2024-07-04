#ifndef SAI_PACKET_REWRITES_P4_
#define SAI_PACKET_REWRITES_P4_

#include <v1model.p4>
#include "headers.p4"
#include "metadata.p4"
#include "minimum_guaranteed_sizes.p4"

// This control block applies the rewrites computed during the the ingress
// stage to the actual packet.
control packet_rewrites(inout headers_t headers,
                        in local_metadata_t local_metadata,
                        inout standard_metadata_t standard_metadata) {
  apply {
    if (local_metadata.admit_to_l3) {
      headers.ethernet.src_addr = local_metadata.packet_rewrites.src_mac;
      headers.ethernet.dst_addr = local_metadata.packet_rewrites.dst_mac;

    if (headers.ipv4.isValid()) {
      if (headers.ipv4.ttl <= 1) {
        mark_to_drop(standard_metadata);
      } else {
        headers.ipv4.ttl = headers.ipv4.ttl - 1;
      }
    }

    if (headers.ipv6.isValid()) {
      if (headers.ipv6.hop_limit <= 1) {
        mark_to_drop(standard_metadata);
      } else {
        headers.ipv6.hop_limit = headers.ipv6.hop_limit - 1;
      }
    }
    }
  }
}  // control packet_rewrites

#endif  // SAI_PACKET_REWRITES_P4_
