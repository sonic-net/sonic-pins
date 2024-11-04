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


header header_t {
    bit<8> f1;
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
    action a1() {
       hdr.h1.f1 = 1;
    }

    table n1 {key = {hdr.h1.f1: exact;} actions = {@proto_id(1) a1;}}
    table n2 {key = {hdr.h1.f1: exact;} actions = {@proto_id(1) a1;}}
    table n3 {key = {hdr.h1.f1: exact;} actions = {@proto_id(1) a1;}}
    table n4 {key = {hdr.h1.f1: exact;} actions = {@proto_id(1) a1;}}
    table n5 {key = {hdr.h1.f1: exact;} actions = {@proto_id(1) a1;}}
    table n6 {key = {hdr.h1.f1: exact;} actions = {@proto_id(1) a1;}}
    table n7 {key = {hdr.h1.f1: exact;} actions = {@proto_id(1) a1;}}
    table n8 {key = {hdr.h1.f1: exact;} actions = {@proto_id(1) a1;}}
    table n9 {key = {hdr.h1.f1: exact;} actions = {@proto_id(1) a1;}}
    table n10 {key = {hdr.h1.f1: exact;} actions = {@proto_id(1) a1;}}
    table n11 {key = {hdr.h1.f1: exact;} actions = {@proto_id(1) a1;}}
    table n12 {key = {hdr.h1.f1: exact;} actions = {@proto_id(1) a1;}}
    table n13 {key = {hdr.h1.f1: exact;} actions = {@proto_id(1) a1;}}
    table n14 {key = {hdr.h1.f1: exact;} actions = {@proto_id(1) a1;}}
    table n15 {key = {hdr.h1.f1: exact;} actions = {@proto_id(1) a1;}}
    table n16 {key = {hdr.h1.f1: exact;} actions = {@proto_id(1) a1;}}
    table n17 {key = {hdr.h1.f1: exact;} actions = {@proto_id(1) a1;}}
    table n18 {key = {hdr.h1.f1: exact;} actions = {@proto_id(1) a1;}}
    table n19 {key = {hdr.h1.f1: exact;} actions = {@proto_id(1) a1;}}
    table n20 {key = {hdr.h1.f1: exact;} actions = {@proto_id(1) a1;}}
    table n21 {key = {hdr.h1.f1: exact;} actions = {@proto_id(1) a1;}}
    table n22 {key = {hdr.h1.f1: exact;} actions = {@proto_id(1) a1;}}

    apply {
        // n1
        if (hdr.h1.f1 != 0) {
          n2.apply();
        } else {
          n2.apply();
        }
        n3.apply();
        // n4
        if (hdr.h1.f1 != 1) {
          n6.apply();
        } else {
          n7.apply();
          n8.apply();
        }
        if (n9.apply().hit) {
          // n10
          if (hdr.h1.f1 != 3) {
            n11.apply();
          } else {
            n12.apply();
          }
          n13.apply();
        } else {
          n14.apply();
        }
        // n15
        if (hdr.h1.f1 != 4) {
          // n16
          if (hdr.h1.f1 != 5) {
            n19.apply();
          } else {
            n20.apply();
          }
        } else {
          n17.apply();
          n18.apply();
        }
        n21.apply();
        n22.apply();
    }
}

control MyEgress(inout headers hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {
    action a1() {
      hdr.h1.f1 = 1;
    }

    table n23 {key = {hdr.h1.f1: exact;} actions = {@proto_id(1) a1;}}
    table n24 {key = {hdr.h1.f1: exact;} actions = {@proto_id(1) a1;}}
    table n25 {key = {hdr.h1.f1: exact;} actions = {@proto_id(1) a1;}}

    apply {
      n23.apply();
      if (hdr.h1.f1 != 6) {
        if (hdr.h1.f1 != 7) {
          n24.apply();
        }
      }
      n25.apply();
    }
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
