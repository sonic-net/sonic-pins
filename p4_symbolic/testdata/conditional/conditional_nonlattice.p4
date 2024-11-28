// Copyright 2024 Google LLC
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

/* -*- P4_16 -*- */
#include <core.p4>
#include <v1model.p4>

typedef bit<9>  egress_spec_t;
typedef bit<48> mac_addr_t;

header ethernet_t {
    mac_addr_t dst_addr;
    mac_addr_t src_addr;
    bit<16>   ether_type;
}

struct metadata {
    /* empty */
}

struct headers {
    ethernet_t   ethernet;
}

parser MyParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {

    state start {
        transition parse_ethernet;
    }

    state parse_ethernet {
        packet.extract(hdr.ethernet);
        transition accept;
    }
}


control MyIngress(inout headers hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {
    action drop() {
        mark_to_drop(standard_metadata);
    }

    action forward(mac_addr_t dst_addr, egress_spec_t port) {
        standard_metadata.egress_spec = port;
        hdr.ethernet.dst_addr = dst_addr;
    }

    table t_1 {
        key = {
            hdr.ethernet.ether_type: exact;
        }
        actions = {
            @proto_id(1) drop;
            @proto_id(2) forward;
        }
        size = 1024;
        default_action = drop();
    }
    table t_2 {
        key = {
            hdr.ethernet.src_addr: exact;
        }
        actions = {
            @proto_id(1) drop;
            @proto_id(2) forward;
        }
        size = 1024;
        default_action = drop();
    }
    table t_3 {
        key = {
            hdr.ethernet.dst_addr: exact;
        }
        actions = {
            @proto_id(1) drop;
            @proto_id(2) forward;
        }
        size = 1024;
        default_action = drop();
    }

    apply {
        if (standard_metadata.ingress_port > 10) {
            if (standard_metadata.ingress_port > 15) {
                t_1.apply();
            } else {
                t_2.apply();
            }
        } else {
            if (standard_metadata.ingress_port > 5) {
                t_1.apply();
            } else {
                t_2.apply();
            }
        }
        t_3.apply();
    }
}

control MyEgress(inout headers hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {
    apply {  }
}



control MyDeparser(packet_out packet, in headers hdr) {
    apply {
        packet.emit(hdr.ethernet);
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
