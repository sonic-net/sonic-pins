// A preliminary, incomplete model of IEEE 802.1Q VLAN.

#ifndef SAI_VLAN_P4_
#define SAI_VLAN_P4_

#include <v1model.p4>
#include "headers.p4"
#include "metadata.p4"


control vlan_untag(inout headers_t headers,
                   inout local_metadata_t local_metadata,
                   inout standard_metadata_t standard_metadata) {
  apply {
     if (headers.vlan.isValid()) {
        headers.ethernet.ether_type = headers.vlan.ether_type;
        local_metadata.vlan_id_valid = true;
        local_metadata.vlan_id = headers.vlan.vlan_id;
        headers.vlan.setInvalid();
    }
  }
}  // control vlan_ingress

control vlan_tag(inout headers_t headers,
                 inout local_metadata_t local_metadata,
                 inout standard_metadata_t standard_metadata) {
  apply {
    // Currently no VLAN tagged packet gets forwarded, thus tagging is not
    // modeled yet. When modeling vlan tagging, note that ethernet.ether_type
    // must be copied into vlan.ether_type due to the way it is currently
    // modeled (see headers.p4).
  }
}  // control vlan_egress

#endif  // SAI_VLAN_P4_
