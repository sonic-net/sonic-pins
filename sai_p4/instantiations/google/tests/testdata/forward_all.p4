// This is a test program that forwards all packets unchanged to the port they
// ingressed from. However, it uses the SAI P4 parser, deparser, and checksum
// verification and thus can be used to test the correctness of those
// components. For example, it is used to test that the SAI P4 parser and
// deparser roundtrip.

#include <v1model.p4>

// This header has to come first, to override its fixed counterpart.
#include "bitwidths.p4"
#include "../../fixed/parser.p4"
#include "../../fixed/ipv4_checksum.p4"

control MinimalIngress(inout headers_t headers,
                       inout local_metadata_t local_metadata,
                       inout standard_metadata_t standard_metadata) {
  apply {
    standard_metadata.egress_spec = (bit<PORT_BITWIDTH>)local_metadata.ingress_port;
  }
}

control MinimalEgress(inout headers_t headers,
                      inout local_metadata_t local_metadata,
                      inout standard_metadata_t standard_metadata) {
  apply {}
}

V1Switch(packet_parser(), verify_ipv4_checksum(), MinimalIngress(),
         MinimalEgress(), compute_ipv4_checksum(), packet_deparser()) main;
