#ifndef GOOGLE_SAI_RESOURCE_GUARANTEES_P4_
#define GOOGLE_SAI_RESOURCE_GUARANTEES_P4_

// This file documents the resource guarantees that each table provides.
// These guarantees are not based on the hardware limits of particular targets,
// but instead model the requirements that we believe we need for our
// operations. Specifically, we try to give a a conservative upper bound of our
// current requirements to support current usage and be better prepared for
// future changes.
//
// For some targets and some tables, these numbers are read by the switch and
// used to allocate tables accordingly. For other targets/tables these numbers
// are ignored by the switch. In either case, we can use p4-fuzzer to ensure
// that the given guarantees are actually upheld by the switch.
//
// See go/gpins-resource-guarantees for details on how a variety of these
// numbers arose and to what extent they are truly guarantees.

// -- Fixed Table sizes --------------------------------------------------------

#define NEXTHOP_TABLE_MINIMUM_GUARANTEED_SIZE 1024

#define NEIGHBOR_TABLE_MINIMUM_GUARANTEED_SIZE 1024

#define ROUTER_INTERFACE_TABLE_MINIMUM_GUARANTEED_SIZE 256

#define MIRROR_SESSION_TABLE_MINIMUM_GUARANTEED_SIZE 2

#define ROUTING_VRF_TABLE_MINIMUM_GUARANTEED_SIZE 64

#define ROUTING_IPV4_TABLE_MINIMUM_GUARANTEED_SIZE 32768

#define ROUTING_IPV6_TABLE_MINIMUM_GUARANTEED_SIZE 4096

#define ROUTING_TUNNEL_TABLE_MINIMUM_GUARANTEED_SIZE 512

#define L3_ADMIT_TABLE_MINIMUM_GUARANTEED_SIZE 128

// The maximum number of wcmp groups.
#define WCMP_GROUP_TABLE_MINIMUM_GUARANTEED_SIZE 3968

// The maximum sum of weights across all wcmp groups.
#define WCMP_GROUP_SELECTOR_MAX_SUM_OF_WEIGHTS_ACROSS_ALL_GROUPS 65536

// The maximum sum of weights for each wcmp group.
#define WCMP_GROUP_SELECTOR_MAX_SUM_OF_WEIGHTS_PER_GROUP 256

// -- ACL Table sizes ----------------------------------------------------------

#define ACL_INGRESS_TABLE_MINIMUM_GUARANTEED_SIZE 128

// Some switches allocate table sizes in powers of 2. Since GPINs (Orchagent)
// allocates 1 extra table entry for the loopback IP, we pick the size as
// 2^8 - 1 to avoid allocation of 2^9 entries on such switches.
#define ACL_PRE_INGRESS_TABLE_MINIMUM_GUARANTEED_SIZE 255

#define ACL_EGRESS_TABLE_MINIMUM_GUARANTEED_SIZE 128

// 1 entry for LLDP, 1 entry for ND, and 6 entries for traceroute: TTL 0,1,2 for
// IPv4 and IPv6
#define ACL_WBB_INGRESS_TABLE_MINIMUM_GUARANTEED_SIZE 8

#endif  // GOOGLE_SAI_RESOURCE_GUARANTEES_P4_
