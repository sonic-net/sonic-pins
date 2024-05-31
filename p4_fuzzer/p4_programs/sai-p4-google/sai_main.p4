#include "v1model.p4"
#include "headers.p4"
#include "metadata.p4"
#include "parser.p4"
#include "routing.p4"
#include "ipv4_checksum.p4"
#include "ttl.p4"
#include "acl_punt.p4"
#include "acl_set_vrf.p4"

control ingress(inout headers_t headers,
                inout local_metadata_t local_metadata,
                inout standard_metadata_t standard_metadata) {
  apply {
    acl_set_vrf.apply(headers, local_metadata, standard_metadata);
    routing.apply(headers, local_metadata, standard_metadata);
    acl_punt.apply(headers, local_metadata, standard_metadata);
    ttl.apply(headers, standard_metadata);
  }
}  // control ingress

control egress(inout headers_t headers,
               inout local_metadata_t local_metadata,
               inout standard_metadata_t standard_metadata) {
  apply {}
}  // control egress

V1Switch(packet_parser(), verify_ipv4_checksum(), ingress(), egress(),
         compute_ipv4_checksum(), packet_deparser()) main;
