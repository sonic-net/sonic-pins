#include <v1model.p4>
#include "../common/headers.p4"

struct local_metadata_t {
  /* empty */
}

struct headers_t {
  ethernet_t ethernet;
  ipv4_t     ipv4;
}

parser packet_parser(packet_in packet, out headers_t headers,
                     inout local_metadata_t local_metadata,
                     inout standard_metadata_t standard_metadata) {
  state start {
    transition parse_ethernet;
  }

  state parse_ethernet {
    packet.extract(headers.ethernet);
    transition select(headers.ethernet.ether_type) {
      0 &&& 0xfe00: accept;
      ETHERTYPE_IPV4:    parse_ipv4;
      default:      accept;
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

