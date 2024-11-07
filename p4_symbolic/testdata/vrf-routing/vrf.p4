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

const bit<16> TYPE_IPV4 = 0x800;

typedef bit<9> egress_spec_t;
typedef bit<48> mac_addr_t;
typedef bit<32> ipv4_addr_t;

@p4runtime_translation("", string)
type bit<10> vrf_t;

header ethernet_t {
  mac_addr_t dstAddr;
  mac_addr_t srcAddr;
  bit<16> eth_type;
}
header ipv4_t {
  bit<4> version;
  bit<4> ihl;
  bit<8> diffserv;
  bit<16> totalLen;
  bit<16> identification;
  bit<3> flags;
  bit<13> fragOffset;
  bit<8> ttl;
  bit<8> protocol;
  bit<16> hdrChecksum;
  ipv4_addr_t srcAddr;
  ipv4_addr_t dstAddr;
}
struct headers {
  ethernet_t ethernet;
  ipv4_t ipv4;
}
struct local_metadata_t {
  vrf_t vrf;
  bool vrf_is_valid;
}

parser packet_parser(packet_in packet, out headers hdr,
                     inout local_metadata_t local_metadata,
                     inout standard_metadata_t standard_metadata) {
  state start {
    transition parse_ethernet;
  }

  state parse_ethernet {
    packet.extract(hdr.ethernet);
    transition select(hdr.ethernet.eth_type) {
      TYPE_IPV4: parse_ipv4;
      default: accept;
    }
  }

  state parse_ipv4 {
    packet.extract(hdr.ipv4);
    transition accept;
  }
}

// Ingress processing:
// First set vrf by matching on ipv4.srcAddr,
// then match on vrf and ipv4.dstAddr to route.
control packet_ingress(inout headers hdr,
                       inout local_metadata_t local_metadata,
                       inout standard_metadata_t standard_metadata) {
  // NoAction: 21257015

  // 26764252
  action drop() {
    mark_to_drop(standard_metadata);
  }

  // 26074559
  action set_vrf(vrf_t vrf) {
    local_metadata.vrf = vrf;
    local_metadata.vrf_is_valid = true;
  }

  // 27807574
  action ipv4_forward(mac_addr_t dstAddr, egress_spec_t port) {
    standard_metadata.egress_spec = port;
    hdr.ethernet.srcAddr = hdr.ethernet.dstAddr;
    hdr.ethernet.dstAddr = dstAddr;
    hdr.ipv4.ttl = hdr.ipv4.ttl - 1;
  }

  // 37541331
  table set_vrf_table {
    key = {
      hdr.ipv4.srcAddr: ternary @format(IPV4_ADDRESS);
    }
    actions = {
      @proto_id(1) set_vrf;
      @proto_id(2) NoAction;
    }
    size = 1024;
    default_action = NoAction;
  }

  // 44809600
  table ipv4_lpm_table {
    key = {
      hdr.ipv4.dstAddr: lpm @format(IPV4_ADDRESS);
      local_metadata.vrf: exact;
    }
    actions = {
      @proto_id(1) ipv4_forward;
      @proto_id(2) drop;
    }
    size = 1024;
    default_action = drop();
  }

  apply {
    // vrf is not valid by default.
    local_metadata.vrf_is_valid = false;
    local_metadata.vrf = 0;

    // Check that the packet is an ipv4 packet.
    if (hdr.ipv4.isValid()) {
      // Set a vrf.
      set_vrf_table.apply();
      if (local_metadata.vrf_is_valid) {
        // If vrf was set, do lpm matching on dst to route.
        ipv4_lpm_table.apply();
      }
    }
  }
}

control empty_deparser(packet_out packet, in headers hdr) {
  apply {
    packet.emit(hdr.ethernet);
    packet.emit(hdr.ipv4);
  }
}

control empty_egress(inout headers hdr, inout local_metadata_t local_metadata,
                     inout standard_metadata_t standard_metadata) {
  apply {}
}


control empty_compute_checksum(inout headers hdr,
                               inout local_metadata_t local_metadata) {
  apply {}
}

control empty_verify_checksum(inout headers hdr,
                              inout local_metadata_t local_metadata) {
  apply {}
}

V1Switch(
packet_parser(),
empty_verify_checksum(),
packet_ingress(),
empty_egress(),
empty_compute_checksum(),
empty_deparser()
) main;
