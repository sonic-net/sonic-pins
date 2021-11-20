#ifndef SAI_HEADERS_P4_
#define SAI_HEADERS_P4_

#define ETHERTYPE_IPV4  0x0800
#define ETHERTYPE_IPV6  0x86dd
#define ETHERTYPE_ARP   0x0806
#define ETHERTYPE_LLDP  0x88cc

#define IP_PROTOCOL_TCP    0x06
#define IP_PROTOCOL_UDP    0x11
#define IP_PROTOCOL_ICMP   0x01
#define IP_PROTOCOL_ICMPV6 0x3a
#define IP_PROTOCOLS_GRE   0x2f

#define GRE_PROTOCOL_ERSPAN 0x88be

#define ERSPAN_VERSION_TYPE_II 1

typedef bit<48> ethernet_addr_t;
typedef bit<32> ipv4_addr_t;
typedef bit<128> ipv6_addr_t;

// -- Protocol headers ---------------------------------------------------------

#define ETHERNET_HEADER_BYTES 14

header ethernet_t {
  ethernet_addr_t dst_addr;
  ethernet_addr_t src_addr;
  bit<16> ether_type;
}

#define IPV4_HEADER_BYTES 20

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
  ipv4_addr_t src_addr;
  ipv4_addr_t dst_addr;
}

#define IPV6_HEADER_BYTES 40

header ipv6_t {
  bit<4> version;
  bit<6> dscp;  // The 6 most significant bits of the traffic_class field.
  bit<2> ecn;   // The 2 least significant bits of the traffic_class field.
  bit<20> flow_label;
  bit<16> payload_length;
  bit<8> next_header;
  bit<8> hop_limit;
  ipv6_addr_t src_addr;
  ipv6_addr_t dst_addr;
}

header udp_t {
  bit<16> src_port;
  bit<16> dst_port;
  bit<16> hdr_length;
  bit<16> checksum;
}

header tcp_t {
  bit<16> src_port;
  bit<16> dst_port;
  bit<32> seq_no;
  bit<32> ack_no;
  bit<4> data_offset;
  bit<4> res;
  bit<8> flags;
  bit<16> window;
  bit<16> checksum;
  bit<16> urgent_ptr;
}

header icmp_t {
  bit<8> type;
  bit<8> code;
  bit<16> checksum;
}

header arp_t {
  bit<16> hw_type;
  bit<16> proto_type;
  bit<8> hw_addr_len;
  bit<8> proto_addr_len;
  bit<16> opcode;
  bit<48> sender_hw_addr;
  bit<32> sender_proto_addr;
  bit<48> target_hw_addr;
  bit<32> target_proto_addr;
}

#define GRE_HEADER_BYTES 4

header gre_t {
  bit<1> checksum_present;
  bit<1> routing_present;
  bit<1> key_present;
  bit<1> sequence_present;
  bit<1> strict_source_route;
  bit<3> recursion_control;
  bit<1> acknowledgement_present;
  bit<4> flags;
  bit<3> version;
  bit<16> protocol;
}

#endif  // SAI_HEADERS_P4_
