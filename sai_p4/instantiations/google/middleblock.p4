#define SAI_INSTANTIATION_MIDDLEBLOCK

#define ACL_REDIRECT_TO_NEXTHOP_CAPABLE
#define ACL_REDIRECT_TO_PORT_CAPABLE
#define DSCP_REWRITE_CAPABLE
#define IP_MULTICAST_CAPABLE
#define L3_ADMIT_SUPPORTS_IN_PORT
#define NEXTHOP_DISABLE_REWRITES_CAPABLE
#define MIRROR_CAPABLE
#define RIF_PROGRAMMING_MY_MAC_SUPPORTED
#define TIMESTAMP_CAPABLE
#define TUNNEL_ENCAP_CAPABLE

#include <v1model.p4>

// These headers have to come first, to override their fixed counterparts.
#include "roles.h"
#include "bitwidths.p4"
#include "minimum_guaranteed_sizes.h"
#include "../../fixed/headers.p4"
#include "../../fixed/metadata.p4"
#include "../../fixed/parser.p4"
#include "../../fixed/packet_io.p4"
#include "../../fixed/routing.p4"
#include "../../fixed/ipv4_checksum.p4"
#include "../../fixed/ingress_cloning.p4"
#include "../../fixed/mirroring.p4"
#include "../../fixed/l3_admit.p4"
#include "../../fixed/vlan.p4"
#include "../../fixed/drop_martians.p4"
#include "../../fixed/packet_rewrites.p4"
#include "../../fixed/tunnel_termination.p4"
#include "acl_egress.p4"
#include "acl_ingress.p4"
#include "acl_pre_ingress.p4"
#include "admit_google_system_mac.p4"
#include "ids.h"
#include "versions.h"

control ingress(inout headers_t headers,
                inout local_metadata_t local_metadata,
                inout standard_metadata_t standard_metadata) {
  apply {
    packet_out_decap.apply(headers, local_metadata, standard_metadata);
    if (!local_metadata.bypass_ingress) {
      vlan_untag.apply(headers, local_metadata, standard_metadata);
      acl_pre_ingress.apply(headers, local_metadata, standard_metadata);
      ingress_vlan_checks.apply(headers, local_metadata, standard_metadata);
      admit_google_system_mac.apply(headers, local_metadata);
      l3_admit.apply(headers, local_metadata, standard_metadata);
      tunnel_termination.apply(headers, local_metadata);
      routing_lookup.apply(headers, local_metadata, standard_metadata);
      acl_ingress.apply(headers, local_metadata, standard_metadata);
      routing_resolution.apply(headers, local_metadata, standard_metadata);
      mirror_session_lookup.apply(headers, local_metadata, standard_metadata);
      ingress_cloning.apply(headers, local_metadata, standard_metadata);
      drop_martians.apply(headers, local_metadata, standard_metadata);
    }
  }
}  // control ingress

control egress(inout headers_t headers,
               inout local_metadata_t local_metadata,
               inout standard_metadata_t standard_metadata) {
  apply {
    packet_in_encap.apply(headers, local_metadata, standard_metadata);
    // TODO: Remove if statement once exit is supported in
    // p4-symbolic.
    if (!local_metadata.bypass_egress) {
      packet_rewrites.apply(headers, local_metadata, standard_metadata);
      mirror_encap.apply(headers, local_metadata, standard_metadata);
      egress_vlan_checks.apply(headers, local_metadata, standard_metadata);
      vlan_tag.apply(headers, local_metadata, standard_metadata);
      acl_egress.apply(headers, local_metadata, standard_metadata);
    }
  }
}  // control egress

#ifndef PKG_INFO_NAME
#define PKG_INFO_NAME "middleblock.p4"
#endif
@pkginfo(
  name = PKG_INFO_NAME,
  organization = "Google",
  version = SAI_P4_PKGINFO_VERSION_LATEST
)
@platform_property(
  multicast_group_table_size = MULTICAST_GROUP_TABLE_SIZE,
  multicast_group_table_total_replicas = MULTICAST_GROUP_TABLE_TOTAL_REPLICAS,
  multicast_group_table_max_replicas_per_entry = MULTICAST_GROUP_TABLE_MAX_REPLICAS_PER_ENTRY
)
V1Switch(packet_parser(), verify_ipv4_checksum(), ingress(), egress(),
         compute_ipv4_checksum(), packet_deparser()) main;
