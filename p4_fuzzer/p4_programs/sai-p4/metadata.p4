#ifndef SAI_METADATA_P4_
#define SAI_METADATA_P4_

#include "headers.p4"
#include "resource_limits.p4"

@p4runtime_translation("", 32)
type bit<MAX_NEXTHOPS_LOG2> nexthop_id_t;

@p4runtime_translation("", 32)
type bit<MAX_WCMP_GROUPS_LOG2> wcmp_group_id_t;

@p4runtime_translation("", 32)
type bit<MAX_VRFS_LOG2> vrf_id_t;

@p4runtime_translation("", 32)
type bit<MAX_ROUTER_INTERFACES_LOG2> router_interface_id_t;

@p4runtime_translation("", 32)
type bit<MAX_NEIGHBORS_LOG2> neighbor_id_t;

@p4runtime_translation("", 32)
type bit<MAX_PORTS_LOG2> port_id_t;

struct headers_t {
  ethernet_t ethernet;
  ipv4_t ipv4;
  ipv6_t ipv6;
  icmp_t icmp;
  tcp_t tcp;
  udp_t udp;
  arp_t arp;
}

// Local metadata for each packet being processed.
struct local_metadata_t {
  vrf_id_t vrf_id;
  bit<16> l4_src_port;
  bit<16> l4_dst_port;
}

#endif  // SAI_METADATA_P4_
