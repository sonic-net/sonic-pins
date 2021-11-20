#ifndef SAI_METADATA_P4_
#define SAI_METADATA_P4_

#include "ids.h"
#include "headers.p4"
#include "bitwidths.p4"

// -- Translated Types ---------------------------------------------------------

// BMv2 does not support @p4runtime_translation.

#ifndef PLATFORM_BMV2
@p4runtime_translation("", string)
#endif
type bit<NEXTHOP_ID_BITWIDTH> nexthop_id_t;

#ifndef PLATFORM_BMV2
@p4runtime_translation("", string)
#endif
type bit<WCMP_GROUP_ID_BITWIDTH> wcmp_group_id_t;


#ifndef PLATFORM_BMV2
@p4runtime_translation("", string)
#endif
type bit<VRF_BITWIDTH> vrf_id_t;

#ifndef PLATFORM_BMV2
@p4runtime_translation("", string)
#endif
type bit<ROUTER_INTERFACE_ID_BITWIDTH> router_interface_id_t;

#ifndef PLATFORM_BMV2
@p4runtime_translation("", string)
#endif
type bit<NEIGHBOR_ID_BITWIDTH> neighbor_id_t;

#ifndef PLATFORM_BMV2
@p4runtime_translation("", string)
#endif
type bit<PORT_BITWIDTH> port_id_t;

#ifndef PLATFORM_BMV2
@p4runtime_translation("", string)
#endif
type bit<MIRROR_SESSION_ID_BITWIDTH> mirror_session_id_t;

#ifndef PLATFORM_BMV2
@p4runtime_translation("", string)
#endif
type bit<QOS_QUEUE_BITWIDTH> qos_queue_t;

// -- Meters -------------------------------------------------------------------

enum MeterColor_t { GREEN, YELLOW, RED };

// -- Per Packet State ---------------------------------------------------------

struct headers_t {
  // ERSPAN headers, not extracted during parsing.
  ethernet_t erspan_ethernet;
  ipv4_t erspan_ipv4;
  gre_t erspan_gre;

  ethernet_t ethernet;
  ipv4_t ipv4;
  ipv6_t ipv6;
  icmp_t icmp;
  tcp_t tcp;
  udp_t udp;
  arp_t arp;
}

// Header fields rewritten by the ingress pipeline. Rewrites are computed and
// stored in this struct, but actual rewriting is dealyed until the egress
// pipeline so that the original values aren't overridden and get be matched on.
struct packet_rewrites_t {
  ethernet_addr_t src_mac;
  ethernet_addr_t dst_mac;
}

// Local metadata for each packet being processed.
struct local_metadata_t {
  bool admit_to_l3;
  vrf_id_t vrf_id;
  packet_rewrites_t packet_rewrites;
  bit<16> l4_src_port;
  bit<16> l4_dst_port;
  bit<WCMP_SELECTOR_INPUT_BITWIDTH> wcmp_selector_input;
  // mirroring data, we can't group the into a struct, because BMv2 doesn't
  // support passing structs in clone3.
  bool mirror_session_id_valid;
  mirror_session_id_t mirror_session_id_value;
  ipv4_addr_t mirroring_src_ip;
  ipv4_addr_t mirroring_dst_ip;
  ethernet_addr_t mirroring_src_mac;
  ethernet_addr_t mirroring_dst_mac;
  bit<8> mirroring_ttl;
  bit<8> mirroring_tos;
  // TODO: consider modeling metering beyond control plane API.
  MeterColor_t color;
  // We consistently use local_metadata.ingress_port instead of
  // standard_metadata.ingress_port in the P4 tables to ensure that the P4Info
  // has port_id_t as the type for all fields that match on ports. This allows
  // tools to treat ports specially (e.g. a fuzzer).
  port_id_t ingress_port;
}

// -- Packet IO headers --------------------------------------------------------

// TODO: extend the P4 program to actually define the semantics of these.

@controller_header("packet_in")
header packet_in_header_t {
  // The port the packet ingressed on.
  @id(PACKET_IN_INGRESS_PORT_ID)
  port_id_t ingress_port;
  // The initial intended egress port decided for the packet by the pipeline.
  @id(PACKET_IN_TARGET_EGRESS_PORT_ID)
  port_id_t target_egress_port;
}

@controller_header("packet_out")
header packet_out_header_t {
  // The port this packet should egress out of when `submit_to_ingress == 0`.
  // Meaningless when `submit_to_ingress == 1`.
  @id(PACKET_OUT_EGRESS_PORT_ID)
  port_id_t egress_port;
  // Should the packet be submitted to the ingress pipeline instead of being
  // sent directly?
  @id(PACKET_OUT_SUBMIT_TO_INGRESS_ID)
  bit<1> submit_to_ingress;
  // BMV2 backend requires headers to be multiple of 8-bits.
  @id(3)
  bit<7> unused_pad;
}

#endif  // SAI_METADATA_P4_
