// A preliminary, incomplete model of IEEE 802.1Q VLAN.

#ifndef SAI_VLAN_P4_
#define SAI_VLAN_P4_

#include <v1model.p4>
#include "headers.p4"
#include "metadata.p4"


control vlan_untag(inout headers_t headers,
                   inout local_metadata_t local_metadata,
                   inout standard_metadata_t standard_metadata) {

  @id(DISABLE_VLAN_CHECKS_ACTION_ID)
  action disable_vlan_checks() {
    local_metadata.enable_vlan_checks = false;
  }

  // Models SAI_DISABLE_VLAN_CHECKS.
  // If VLAN checks are enabled (i.e. if the table is empty), an ingress/egress
  // packet with a VLAN tag containing a VID beside the reserved ones (0, 4095)
  // gets dropped in ingress/egress pipelines, respectively (given the
  // current switch configuration). With VLAN checks disabled, such drops do
  // not happen.
  // TODO: Remove @unsupported when the switch supports this table.
  @unsupported
  @p4runtime_role(P4RUNTIME_ROLE_SDN_CONTROLLER)
  @id(DISABLE_VLAN_CHECKS_TABLE_ID)
  @entry_restriction("
    // Force the dummy_match to be wildcard.
    dummy_match::mask == 0;
  ")
  table disable_vlan_checks_table {
    key = {
      // Note: In the P4_16 specification, a table with no match keys cannot have
      // entries (only the default action can be programmed which does not fit
      // well in our SDN ecosystem). To alleviate this, we add a dummy match but
      // force it to always be wildcard.
      1w1 : ternary @id(1) @name("dummy_match");
    }
    actions = {
      @proto_id(1) disable_vlan_checks;
    }
    size = 1;
  }

  apply {
     // Determine the vlan_id metadata.
     if (headers.vlan.isValid()) {
        // If input packet has a VLAN tag, use the VID from the tag.
        local_metadata.vlan_id = headers.vlan.vlan_id;
        // Invalidate the VLAN header. In doing so we move the ethertype placed
        // after the VLAN tag (which we model as part of the VLAN tag due to P4
        // language's limitations) to ethernet.ether_type.
        headers.ethernet.ether_type = headers.vlan.ether_type;
        headers.vlan.setInvalid();
     } else {
        // Otherwise, use native VID (4095 for all ports given the current
        // configuration).
        local_metadata.vlan_id = INTERNAL_VLAN_ID;
     }

     // VLAN checks are enabled by default.
     local_metadata.enable_vlan_checks = true;
     // Check if VLAN checks need to be disabled.
     disable_vlan_checks_table.apply();
  }
}  // control vlan_untag

control vlan_tag(inout headers_t headers,
                 inout local_metadata_t local_metadata,
                 inout standard_metadata_t standard_metadata) {
  apply {
      if (IS_RESERVED_VLAN_ID(local_metadata.vlan_id)) {
        // No VLAN tag.
      } else if (local_metadata.enable_vlan_checks) {
        // With VLAN checks enabled, an egress packet with VIDs besides the
        // reserved ones (0, 4095) gets dropped.
        mark_to_drop(standard_metadata);
      } else {
        // Add a VLAN tag.
        headers.vlan.setValid();
        headers.vlan.priority_code_point = 0;
        headers.vlan.drop_eligible_indicator = 0;
        headers.vlan.vlan_id = local_metadata.vlan_id;
        // Move ethernet.ether_type to vlan.ether_type so that it can be
        // placed after the VLAN tag during deparsing.
        headers.vlan.ether_type = headers.ethernet.ether_type;
        headers.ethernet.ether_type = ETHERTYPE_8021Q;
      }
  }
}  // control vlan_tag

#endif  // SAI_VLAN_P4_
