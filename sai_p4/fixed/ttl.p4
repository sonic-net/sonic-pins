#ifndef SAI_TTL_P4_
#define SAI_TTL_P4_

#include <v1model.p4>
#include "headers.p4"
#include "metadata.p4"

control ttl(inout headers_t headers,
                  inout local_metadata_t local_metadata,
                  inout standard_metadata_t standard_metadata) {
  apply {
    if (local_metadata.admit_to_l3) {
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
}  // control ttl

#endif  // SAI_TTL_P4_
