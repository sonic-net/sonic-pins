/* -*- P4_16 -*- */
#include <core.p4>
#include <v1model.p4>

// -- Headers.
header hdr_fuzz_t {
    bit<8> fuzz_field_1;
    bit<8> fuzz_field_2;
}

struct metadata {
}

struct headers {
    hdr_fuzz_t hdr_fuzz;
}


// -- Parsers.
parser MyParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {

    state start {
        packet.extract(hdr.hdr_fuzz);
        transition accept;
    }
}


// -- Checksum verification.
control MyVerifyChecksum(inout headers hdr, inout metadata meta) {
    apply {  }
}


// -- Ingress processing.
control MyIngress(inout headers hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {

    action act_fuzz() {
        /* nop */
    }

    @entry_restriction("
      hdr.hdr_fuzz.fuzz_field_1 == 42
    ")
    table tbl_fuzz {
        key = {
            hdr.hdr_fuzz.fuzz_field_1 : exact;
	    hdr.hdr_fuzz.fuzz_field_2 : exact;
        }

        actions = {
            act_fuzz;
        }
    }

    apply {

        tbl_fuzz.apply();

    }
}

// -- Egress processing.
control MyEgress(inout headers hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {
    apply {  }
}

// -- Checksum computation.
control MyComputeChecksum(inout headers hdr, inout metadata meta) {
     apply {

    }
}


// -- Deparser.
control MyDeparser(packet_out packet, in headers hdr) {
    apply {
        packet.emit(hdr.hdr_fuzz);
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
