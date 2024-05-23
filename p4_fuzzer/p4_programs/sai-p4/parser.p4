#ifndef SAI_PARSER_P4_
#define SAI_PARSER_P4_

#include "v1model.p4"
#include "headers.p4"
#include "metadata.p4"

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
      ETHERTYPE_IPV6: parse_ipv6;
      ETHERTYPE_ARP:  parse_arp;
      _:              accept;
    }
  }

  state parse_ipv4 {
    packet.extract(headers.ipv4);
    transition select(headers.ipv4.protocol) {
      IP_PROTOCOL_ICMP: parse_icmp;
      IP_PROTOCOL_TCP:  parse_tcp;
      IP_PROTOCOL_UDP:  parse_udp;
      _:                accept;
    }
  }

  state parse_ipv6 {
    packet.extract(headers.ipv6);
    transition select(headers.ipv6.next_header) {
      IP_PROTOCOL_ICMPV6: parse_icmp;
      IP_PROTOCOL_TCP:    parse_tcp;
      IP_PROTOCOL_UDP:    parse_udp;
      _:                  accept;
    }
  }

  state parse_tcp {
    packet.extract(headers.tcp);
    // Normalize TCP port metadata to common port metadata.
    local_metadata.l4_src_port = headers.tcp.src_port;
    local_metadata.l4_dst_port = headers.tcp.dst_port;
    transition accept;
  }

  state parse_udp {
    packet.extract(headers.udp);
    // Normalize UDP port metadata to common port metadata.
    local_metadata.l4_src_port = headers.udp.src_port;
    local_metadata.l4_dst_port = headers.udp.dst_port;
    transition accept;
  }

  state parse_icmp {
    packet.extract(headers.icmp);
    transition accept;
  }

  state parse_arp {
    packet.extract(headers.arp);
    transition accept;
  }
}  // parser packet_parser

control packet_deparser(packet_out packet, in headers_t headers) {
  apply {
    packet.emit(headers.ethernet);
    packet.emit(headers.ipv4);
    packet.emit(headers.ipv6);
    packet.emit(headers.arp);
    packet.emit(headers.icmp);
    packet.emit(headers.tcp);
    packet.emit(headers.udp);
  }
}  // control packet_deparser

#endif  // SAI_PARSER_P4_
