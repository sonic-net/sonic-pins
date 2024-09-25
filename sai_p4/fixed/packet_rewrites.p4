#ifndef SAI_PACKET_REWRITES_P4_
#define SAI_PACKET_REWRITES_P4_

#include <v1model.p4>
#include "headers.p4"
#include "metadata.p4"
#include "minimum_guaranteed_sizes.p4"

// This control block applies the rewrites computed during the the ingress
// stage to the actual packet.
control packet_rewrites(inout headers_t headers,
                        inout local_metadata_t local_metadata,
                        inout standard_metadata_t standard_metadata) {
  apply {
    // TODO: Use a more robust check to determine whether to rewrite
    // packets.
    if (local_metadata.admit_to_l3){
      // VLAN id is kept in local_metadata until the end of egress pipeline
      // where depending on the value of VLAN id and VLAN configuration the
      // packet might potentially get VLAN tagged with that VLAN id.
      // TODO: For now rewriting unconditionaly since disabling
      // VLAN rewrite is not modeled yet. When modeled, this rewrite should
      // become conditional too.
//      local_metadata.vlan_id = local_metadata.packet_rewrites.vlan_id;
      if (local_metadata.enable_src_mac_rewrite) {
        headers.ethernet.src_addr = local_metadata.packet_rewrites.src_mac;
      }
      if (local_metadata.enable_dst_mac_rewrite) {
        headers.ethernet.dst_addr = local_metadata.packet_rewrites.dst_mac;
      }
      if (local_metadata.enable_vlan_rewrite) {
        // VLAN id is kept in local_metadata until the end of egress pipeline
        // where depending on the value of VLAN id and VLAN configuration the
        // packet might potentially get VLAN tagged with that VLAN id.
        local_metadata.vlan_id = local_metadata.packet_rewrites.vlan_id;
      }
      if (headers.ipv4.isValid()) {
        if (headers.ipv4.ttl > 0 && local_metadata.enable_decrement_ttl) {
          headers.ipv4.ttl = headers.ipv4.ttl - 1;
        }
        // TODO: Verify this is accurate when TTL rewrite is
        // disabled and update this code if not.
        if (headers.ipv4.ttl == 0) {
          mark_to_drop(standard_metadata);
        }
      }
      if (headers.ipv6.isValid()) {
        if (headers.ipv6.hop_limit > 0 && local_metadata.enable_decrement_ttl) {
          headers.ipv6.hop_limit = headers.ipv6.hop_limit - 1;
        }
        // TODO: Verify this is accurate when TTL rewrite is
        // disabled and update this code if not.
        if (headers.ipv6.hop_limit == 0) {
          mark_to_drop(standard_metadata);
        }
      }
    }
  }
}  // control packet_rewrites

#endif  // SAI_PACKET_REWRITES_P4_
