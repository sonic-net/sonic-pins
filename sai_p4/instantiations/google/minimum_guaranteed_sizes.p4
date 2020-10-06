#ifndef GOOGLE_SAI_RESOURCE_LIMITS_P4_
#define GOOGLE_SAI_RESOURCE_LIMITS_P4_

// -- Fixed Table sizes --------------------------------------------------------

#define NEXTHOP_TABLE_MINIMUM_GUARANTEED_SIZE 1024

#define NEIGHBOR_TABLE_MINIMUM_GUARANTEED_SIZE 1024

#define ROUTER_INTERFACE_TABLE_MINIMUM_GUARANTEED_SIZE 1024

#define MIRROR_SESSION_TABLE_MINIMUM_GUARANTEED_SIZE 2

// We choose a small number of guranteed VRF table entries here because VRFs
// consume default route enties in the IPv4 and IPv6 tables, and this isn't
// currently modelled in P4. We could support more VRFs in principle, but
// restrict ourselves to a small number so VRFs won't interfere with our
// gurantees for the IPv4 and IPv6 tables too much.
// TODO: Find a better way to model such interdepencies.
#define ROUTING_VRF_TABLE_MINIMUM_GUARANTEED_SIZE 32

# copybara:strip_begin(comment only applies internally)
// The IPv4 and IPv6 minimums appear to hold in practice, but Broadcom's
// Algorithmic LPM implementation is subtle, and we do not understand it well
// enough to guarantee these limits. If you are planning to develop a feature
// that relies on these minimums, please talk to us first.
//
// These limits are taken from Sandcastle:
// http://google3/platforms/networking/sandblaze/stack/hal/target/config/tomahawk3_l3_lpm_profiles.txt
# copybara:strip_end
#define ROUTING_IPV4_TABLE_MINIMUM_GUARANTEED_SIZE 32768

#define ROUTING_IPV6_TABLE_MINIMUM_GUARANTEED_SIZE 4096

#define L3_ADMIT_TABLE_MINIMUM_GUARANTEED_SIZE 512

// The maximum number of wcmp groups.
# copybara:strip_begin(comment only applies internally)
// Tomahawk3 supports 4096 entries, but 128 of them are reserved for DLB, so we
// only allow 3968.
//
// Taken from:
// http://google3/platforms/networking/sandblaze/stack/hal/target/config/tomahawk3_ecmp_profiles.txt

// If the switch is unable to support 512 max weight per group for so many
// groups, this could likely be decreased since this link seems to suggest that
// nothing needs more than 1024 groups:
// https://docs.google.com/spreadsheets/d/1Po1E-TXa8Naj4ug0uptZbwuOVK_oWVRrwZjQEgukJNk/edit#gid=1887042389
# copybara:strip_end
#define WCMP_GROUP_TABLE_MINIMUM_GUARANTEED_SIZE 3968

// The maximum sum of weights across all wcmp groups.
#define WCMP_GROUP_SELECTOR_MAX_SUM_OF_WEIGHTS_ACROSS_ALL_GROUPS 65536

// The maximum sum of weights for each wcmp group.
#define WCMP_GROUP_SELECTOR_MAX_SUM_OF_WEIGHTS_PER_GROUP 256

// -- ACL Table sizes ----------------------------------------------------------

#define ACL_INGRESS_TABLE_MINIMUM_GUARANTEED_SIZE 128
#define ACL_PRE_INGRESS_TABLE_MINIMUM_GUARANTEED_SIZE 256
#define ACL_EGRESS_TABLE_MINIMUM_GUARANTEED_SIZE 128

// 1 entry for LLDP, 1 entry for ND, and 6 entries for traceroute: TTL 0,1,2 for
// IPv4 and IPv6
#define ACL_WBB_INGRESS_TABLE_MINIMUM_GUARANTEED_SIZE 8

#endif  // GOOGLE_SAI_RESOURCE_LIMITS_P4_
