// Copyright 2023 Google LLC
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

#include <v1model.p4>

#define ETHERTYPE_IPV4 0x0800
#define IP_PROTOCOL_ICMP 0x01

header ethernet_t {
  bit<48> dst_addr;
  bit<48> src_addr;
  bit<16> ether_type;
}

header ipv4_t {
  bit<4> version;
  bit<4> ihl;
  bit<6> dscp;  // The 6 most significant bits of the diff_serv field.
  bit<2> ecn;   // The 2 least significant bits of the diff_serv field.
  bit<16> total_len;
  bit<16> identification;
  bit<1> reserved;
  bit<1> do_not_fragment;
  bit<1> more_fragments;
  bit<13> frag_offset;
  bit<8> ttl;
  bit<8> protocol;
  bit<16> header_checksum;
  bit<32> src_addr;
  bit<32> dst_addr;
}

header icmp_t {
  bit<8> type;
  bit<8> code;
  bit<16> checksum;
  // bit<32> rest_of_header;
}

struct headers_t {
  ethernet_t ethernet;
  ipv4_t ipv4;
  icmp_t icmp;
}

struct local_metadata_t {}

parser packet_parser(packet_in packet, out headers_t headers,
                     inout local_metadata_t local_metadata,
                     inout standard_metadata_t standard_metadata) {
  state start {
    transition parse_ethernet;
  }

  state parse_ethernet {
    packet.extract(headers.ethernet);
    transition select(headers.ethernet.ether_type) {
      ETHERTYPE_IPV4: parse_ipv4;
      _:              accept;
    }
  }

  state parse_ipv4 {
    packet.extract(headers.ipv4);
    transition select(headers.ipv4.protocol) {
      IP_PROTOCOL_ICMP: parse_icmp;
      _:                accept;
    }
  }

  state parse_icmp {
    packet.extract(headers.icmp);
    transition accept;
  }
}  // parser packet_parser

control my_verify_checksum(inout headers_t headers,
                           inout local_metadata_t local_metadata) {
  apply {}
}  // control my_verify_checksum

control ingress(inout headers_t headers,
                inout local_metadata_t local_metadata,
                inout standard_metadata_t standard_metadata) {
  apply {}
}  // control ingress

control egress(inout headers_t headers,
               inout local_metadata_t local_metadata,
               inout standard_metadata_t standard_metadata) {
  apply {}
}  // control egress

control my_compute_checksum(inout headers_t headers,
                            inout local_metadata_t local_metadata) {
  apply {}
}  // control my_compute_checksum

control packet_deparser(packet_out packet, in headers_t headers) {
  apply {
    packet.emit(headers.ethernet);
    packet.emit(headers.ipv4);
    packet.emit(headers.icmp);
  }
}  // control packet_deparser

V1Switch(
  packet_parser(),
  my_verify_checksum(),
  ingress(),
  egress(),
  my_compute_checksum(),
  packet_deparser()
) main;
