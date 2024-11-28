#include <v1model.p4>
#include "../common/headers.p4"

struct local_metadata_t {
  ethernet_addr_t dst_mac;
  ethernet_addr_t src_mac;
  ether_type_t ether_type;
  int<16> signed_integer1;
  int<16> signed_integer2;
}

struct headers_t {
  ethernet_t ethernet;
  ipv4_t ipv4;
}

parser packet_parser(packet_in packet, out headers_t headers,
                     inout local_metadata_t local_metadata,
                     inout standard_metadata_t standard_metadata) {
  state start {
    transition parse_ethernet;
  }

  state parse_ethernet {
    local_metadata.ether_type = packet.lookahead<ether_type_t>();
    local_metadata.signed_integer1 = -0x01;
    local_metadata.signed_integer2 = 0x02;
    packet.extract(headers.ethernet);
    local_metadata.dst_mac = headers.ethernet.dst_addr;
    local_metadata.src_mac = ((headers.ethernet.src_addr & 48w0xFFFFFFFFFF00));
    transition select(local_metadata.ether_type) {
      ETHERTYPE_IPV4: parse_ipv4;
      default: accept;
    }
  }

  state parse_ipv4 {
    packet.extract(headers.ipv4);
    transition accept;
  }
}

control empty_verify_checksum(inout headers_t headers,
                        inout local_metadata_t local_metadata) {
  apply {}
}  // control empty_verify_checksum

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

control empty_compute_checksum(inout headers_t headers,
                         inout local_metadata_t local_metadata) {
  apply {}
}  // control empty_compute_checksum

control packet_deparser(packet_out packet, in headers_t headers) {
  apply {
    packet.emit(headers.ethernet);
  }
}  // control packet_deparser

V1Switch(
  packet_parser(),
  empty_verify_checksum(),
  ingress(),
  egress(),
  empty_compute_checksum(),
  packet_deparser()
) main;
