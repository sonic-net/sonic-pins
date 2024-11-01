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

    table i1 {key = {hdr.h1.fr: exact;} actions = {@proto_id(1) a1;}}
    table i2 {key = {hdr.h1.fr: exact;} actions = {@proto_id(1) a1;}}
    table i3 {key = {hdr.h1.fr: exact;} actions = {@proto_id(1) a1;}}
    table i4 {key = {hdr.h1.fr: exact;} actions = {@proto_id(1) a1;}}
    table i5 {key = {hdr.h1.fr: exact;} actions = {@proto_id(1) a1;}}
    table i6 {key = {hdr.h1.fr: exact;} actions = {@proto_id(1) a1;}}
    table i7 {key = {hdr.h1.fr: exact;} actions = {@proto_id(1) a1;}}
    table i8 {key = {hdr.h1.fr: exact;} actions = {@proto_id(1) a1;}}
    table e1 {key = {hdr.h1.fr: exact;} actions = {@proto_id(1) a1;}}
    table e2 {key = {hdr.h1.fr: exact;} actions = {@proto_id(1) a1;}}
    table e3 {key = {hdr.h1.fr: exact;} actions = {@proto_id(1) a1;}}
    table e4 {key = {hdr.h1.fr: exact;} actions = {@proto_id(1) a1;}}
    table e5 {key = {hdr.h1.fr: exact;} actions = {@proto_id(1) a1;}}
    table e6 {key = {hdr.h1.fr: exact;} actions = {@proto_id(1) a1;}}
    table e7 {key = {hdr.h1.fr: exact;} actions = {@proto_id(1) a1;}}
    table e8 {key = {hdr.h1.fr: exact;} actions = {@proto_id(1) a1;}}
    table t {key = {hdr.h1.fr: exact;} actions = {@proto_id(1) a1;}}

    apply {
        if (hdr.h1.f1 == 0) {i1.apply();} else {e1.apply();}
        if (hdr.h1.f2 == 0) {i2.apply();} else {e2.apply();}
        if (hdr.h1.f3 == 0) {i3.apply();} else {e3.apply();}
        if (hdr.h1.f4 == 0) {i4.apply();} else {e4.apply();}
        if (hdr.h1.f5 == 0) {i5.apply();} else {e5.apply();}
        if (hdr.h1.f6 == 0) {i6.apply();} else {e6.apply();}
        if (hdr.h1.f7 == 0) {i7.apply();} else {e7.apply();}
        if (hdr.h1.f8 == 0) {i8.apply();} else {e8.apply();}
        t.apply();
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
