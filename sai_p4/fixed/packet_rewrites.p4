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
    }
  }
}  // control packet_rewrites

#endif  // SAI_PACKET_REWRITES_P4_
