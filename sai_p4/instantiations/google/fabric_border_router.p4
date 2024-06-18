#define SAI_INSTANTIATION_FABRIC_BORDER_ROUTER

#include <v1model.p4>

// These headers have to come first, to override their fixed counterparts.
#include "roles.h"
#include "versions.h"
#include "bitwidths.p4"
#include "minimum_guaranteed_sizes.p4"

#include "../../fixed/headers.p4"
#include "../../fixed/metadata.p4"
#include "../../fixed/parser.p4"
#include "../../fixed/packet_io.p4"
#include "../../fixed/routing.p4"
#include "../../fixed/ipv4_checksum.p4"
#include "../../fixed/mirroring_encap.p4"
#include "../../fixed/mirroring_clone.p4"
#include "../../fixed/l3_admit.p4"
#include "../../fixed/ttl.p4"
#include "../../fixed/packet_rewrites.p4"
#include "acl_egress.p4"
#include "acl_ingress.p4"
#include "acl_pre_ingress.p4"
#include "admit_google_system_mac.p4"

control ingress(inout headers_t headers,
                inout local_metadata_t local_metadata,
                inout standard_metadata_t standard_metadata) {
  apply {
    acl_pre_ingress.apply(headers, local_metadata, standard_metadata);
    admit_google_system_mac.apply(headers, local_metadata);
    l3_admit.apply(headers, local_metadata, standard_metadata);
    routing.apply(headers, local_metadata, standard_metadata);
    acl_ingress.apply(headers, local_metadata, standard_metadata);
    ttl.apply(headers, local_metadata, standard_metadata);
    mirroring_clone.apply(headers, local_metadata, standard_metadata);
  }
}  // control ingress

control egress(inout headers_t headers,
               inout local_metadata_t local_metadata,
               inout standard_metadata_t standard_metadata) {
  apply {
    packet_rewrites.apply(headers, local_metadata, standard_metadata);
    mirroring_encap.apply(headers, local_metadata, standard_metadata);
    packet_in_encap.apply(headers, local_metadata, standard_metadata);
    acl_egress.apply(headers, local_metadata, standard_metadata);
  }
}  // control egress

#ifndef PKG_INFO_NAME
#define PKG_INFO_NAME "fabric_border_router.p4"
#endif
@pkginfo(
  name = PKG_INFO_NAME,
  organization = "Google",
  version = SAI_P4_PKGINFO_VERSION_LATEST
)
V1Switch(packet_parser(), verify_ipv4_checksum(), ingress(), egress(),
         compute_ipv4_checksum(), packet_deparser()) main;
