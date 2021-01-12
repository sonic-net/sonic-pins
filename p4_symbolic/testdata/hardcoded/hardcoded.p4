// Copyright 2020 Google LLC
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

struct metadata {}
struct headers {}

parser UselessParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {
    state start {
        transition accept;
    }
}

control UselessChecksum(inout headers hdr, inout metadata meta) {   
    apply {  }
}

control UselessEgress(inout headers hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {
    apply { }
}

control UselessComputeChecksum(inout headers  hdr, inout metadata meta) {
    apply { }
}

control UselessDeparser(packet_out packet, in headers hdr) {
    apply { }
}

// Forwarding Code
control MyIngress(inout headers hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {    
    apply {
        if (standard_metadata.ingress_port == 0) {
            standard_metadata.egress_spec = 1;
        } else {
            standard_metadata.egress_spec = 0;
        }
    }
}

// Switch
V1Switch(
    UselessParser(),
    UselessChecksum(),
    MyIngress(),
    UselessEgress(),
    UselessComputeChecksum(),
    UselessDeparser()
) main;
