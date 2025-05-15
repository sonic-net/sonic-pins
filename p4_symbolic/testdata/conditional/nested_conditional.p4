// Copyright 2025 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// This unit test is added to test the effect of multiple nested conditionals
// on the symbolic expressions representing header fields' value at the
// end of pipeline. The goal is to demonstrate the effect of guard-factorization
// on the size of the expressions (go/p4-symbolic-guard-factorization).

/* -*- P4_16 -*- */
#include <core.p4>
#include <v1model.p4>

typedef bit<9>  egress_spec_t;

header header_t {
    bit<8> fr;
    bit<8> fw;
    bit<8> f1;
    bit<8> f2;
    bit<8> f3;
    bit<8> f4;
    bit<8> f5;
    bit<8> f6;
    bit<8> f7;
    bit<8> f8;
}

struct metadata {
    /* empty */
}

struct headers {
    header_t   h1;
}

parser MyParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {

    state start {
        transition parse_h1;
    }

    state parse_h1 {
        packet.extract(hdr.h1);
        transition accept;
    }
}


control MyIngress(inout headers hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {
    action a1(egress_spec_t port) {
       hdr.h1.fw = 1;
       standard_metadata.egress_port = port;
    }
    action a2(egress_spec_t port) {
       hdr.h1.fw = 2;
       standard_metadata.egress_port = port;
    }
    action a3(egress_spec_t port) {
       hdr.h1.fw = 3;
       standard_metadata.egress_port = port;
    }
    action a4(egress_spec_t port) {
       standard_metadata.egress_port = port;
    }

    table i1 {key = {hdr.h1.fr: exact;} actions = {@proto_id(1) a1;}}
    table i2 {key = {hdr.h1.fr: exact;} actions = {@proto_id(1) a2;}}
    table e1 {key = {hdr.h1.fr: exact;} actions = {@proto_id(1) a3;}}
    table e2 {key = {hdr.h1.fr: exact;} actions = {@proto_id(1) a4;}}

    apply {
        if (hdr.h1.f1 == 0) {
            if (hdr.h1.f2 == 0) {
                if (hdr.h1.f3 == 0) {
                    if (hdr.h1.f4 == 0) {
                        i1.apply();
                    } else {
                        i2.apply();
                    }
                }
                else {
                    if (hdr.h1.f4 == 0) {
                        i2.apply();
                    } else {
                        i1.apply();
                    }
                }
            } else {
                if (hdr.h1.f3 == 0) {
                    if (hdr.h1.f4 == 0) {
                        i1.apply();
                    } else {
                        i2.apply();
                    }
                }
                else {
                    if (hdr.h1.f4 == 0) {
                        i2.apply();
                    } else {
                        i1.apply();
                    }
                }
            }
        } else {
            if (hdr.h1.f2 == 0) {
                if (hdr.h1.f3 == 0) {
                    if (hdr.h1.f4 == 0) {
                        e1.apply();
                    } else {
                        e2.apply();
                    }
                }
                else {
                    if (hdr.h1.f4 == 0) {
                        e2.apply();
                    } else {
                        e1.apply();
                    }
                }
            } else {
                if (hdr.h1.f3 == 0) {
                    if (hdr.h1.f4 == 0) {
                        e1.apply();
                    } else {
                        e2.apply();
                    }
                }
                else {
                    if (hdr.h1.f4 == 0) {
                        e2.apply();
                    } else {
                        e1.apply();
                    }
                }
            }
        }
    }
}
control MyEgress(inout headers hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {
    apply {  }
}



control MyDeparser(packet_out packet, in headers hdr) {
    apply {
        packet.emit(hdr.h1);
    }
}

control MyComputeChecksum(inout headers  hdr, inout metadata meta) {
    apply { }
}

control MyVerifyChecksum(inout headers hdr, inout metadata meta) {
    apply {  }
}

V1Switch(
MyParser(),
MyVerifyChecksum(),
MyIngress(),
MyEgress(),
MyComputeChecksum(),
MyDeparser()
) main;
