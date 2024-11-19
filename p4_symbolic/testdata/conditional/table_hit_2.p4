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

header header_t {
    bit<8> f1;
    bit<8> f2;
    bit<8> f3;
    bit<8> f4;
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
    action forward(egress_spec_t port) {
       standard_metadata.egress_spec = port;
    }
    action nothing() {}

    table t1 {
      key = {hdr.h1.f1: exact;}
      actions = {@proto_id(1) forward; @proto_id(2) nothing;}
      default_action = nothing();
    }
    table t2 {
      key = {hdr.h1.f2: exact;}
      actions = {@proto_id(1) forward; @proto_id(2) nothing;}
      default_action = nothing();
    }
    table t3 {
      key = {hdr.h1.f3: exact;}
      actions = {@proto_id(1) forward; @proto_id(2) nothing;}
      default_action = nothing();
    }
    table t4 {
      key = {hdr.h1.f4: exact;}
      actions = {@proto_id(1) forward; @proto_id(2) nothing;}
      default_action = nothing();
    }


    apply {
        standard_metadata.egress_spec = 0;
        if (t1.apply().hit) {
          t2.apply();
        } else {
          t3.apply();
        }
        t4.apply();
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
