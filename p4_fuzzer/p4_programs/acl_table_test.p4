/* -*- P4_16 -*- */
#include <core.p4>
#include <v1model.p4>
#include "sai-p4-google/acl_set_vrf.p4"

// -- Headers.
header hdr_fuzz_t {
    bit<8> fuzz_field_1;
}

struct metadata {
}


// -- Parsers.
parser MyParser(packet_in packet,
                out headers_t hdr,
                inout local_metadata_t meta,
                inout standard_metadata_t standard_metadata) {

    state start {
        transition accept;
    }
}


// -- Checksum verification.
control MyVerifyChecksum(inout headers_t hdr, inout local_metadata_t meta) {
    apply {  }
}


// -- Ingress processing.
control MyIngress(inout headers_t hdr,
                  inout local_metadata_t meta,
                  inout standard_metadata_t standard_metadata) {
  apply {
    acl_set_vrf.apply(hdr, meta, standard_metadata);
 }
}

// -- Egress processing.
control MyEgress(inout headers_t hdr,
                 inout local_metadata_t meta,
                 inout standard_metadata_t standard_metadata) {
    apply {  }
}

// -- Checksum computation.
control MyComputeChecksum(inout headers_t hdr, inout local_metadata_t meta) {
     apply {

    }
}


// -- Deparser.
control MyDeparser(packet_out packet, in headers_t hdr) {
    apply {
    }
}

// -- Switch.
// Switch architecture.
V1Switch(
MyParser(),
MyVerifyChecksum(),
MyIngress(),
MyEgress(),
MyComputeChecksum(),
MyDeparser()
) main;
