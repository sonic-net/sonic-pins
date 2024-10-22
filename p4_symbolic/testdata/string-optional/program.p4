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

@p4runtime_translation("", string)
type bit<9> string_field_t;

struct metadata {
  string_field_t string_field;
}
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

    action set_egress_spec(bit<9> port) {
        standard_metadata.egress_spec = port;
    }

    action set_field(string_field_t f) {
      meta.string_field = f;
    }

    table set_field_table {
      key = {
        standard_metadata.ingress_port : exact;
      }
      actions = {
        @proto_id(1) set_field;
        @proto_id(2) NoAction;
      }
      size = 1024;
      default_action = NoAction;
    }

    table optional_match {
        key = {
            meta.string_field: optional;
        }
        actions = {
            @proto_id(1) set_egress_spec;
            @proto_id(2) NoAction;
        }
        size = 1024;
        default_action = NoAction;
    }

    apply {
        meta.string_field = (string_field_t)0;
        set_field_table.apply();
        optional_match.apply();
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
