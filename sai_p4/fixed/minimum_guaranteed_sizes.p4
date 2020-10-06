#ifndef SAI_MINIMUM_GUARANTEED_SIZES_P4_
#define SAI_MINIMUM_GUARANTEED_SIZES_P4_

// A table's size specifies the minimum number of entries that must be supported
// by the given table.
//
// Consider for example a hash table with 1024 buckets, where each bucket can
// store two values. The table's size would be 2, because after installing
// two entries that land in the same bucket B, the third entry will be rejected
// if it also lands in B. Note that such collisions are unlikely, so the switch
// will very likely accept a much larger number of table entries than 2.
//
// Instantiations of SAI P4 can override these sizes by defining the following
// macros.

#ifndef NEXTHOP_TABLE_MINIMUM_GUARANTEED_SIZE
#define NEXTHOP_TABLE_MINIMUM_GUARANTEED_SIZE 0
#endif

#ifndef NEIGHBOR_TABLE_MINIMUM_GUARANTEED_SIZE
#define NEIGHBOR_TABLE_MINIMUM_GUARANTEED_SIZE 0
#endif

#ifndef ROUTER_INTERFACE_TABLE_MINIMUM_GUARANTEED_SIZE
#define ROUTER_INTERFACE_TABLE_MINIMUM_GUARANTEED_SIZE 0
#endif

#ifndef MIRROR_SESSION_TABLE_MINIMUM_GUARANTEED_SIZE
#define MIRROR_SESSION_TABLE_MINIMUM_GUARANTEED_SIZE 0
#endif

#ifndef ROUTING_VRF_TABLE_MINIMUM_GUARANTEED_SIZE
#define ROUTING_VRF_TABLE_MINIMUM_GUARANTEED_SIZE 0
#endif

#ifndef ROUTING_IPV4_TABLE_MINIMUM_GUARANTEED_SIZE
#define ROUTING_IPV4_TABLE_MINIMUM_GUARANTEED_SIZE 0
#endif

#ifndef ROUTING_IPV6_TABLE_MINIMUM_GUARANTEED_SIZE
#define ROUTING_IPV6_TABLE_MINIMUM_GUARANTEED_SIZE 0
#endif

#ifndef L3_ADMIT_TABLE_MINIMUM_GUARANTEED_SIZE
#define L3_ADMIT_TABLE_MINIMUM_GUARANTEED_SIZE 0
#endif

#ifndef WCMP_GROUP_TABLE_MINIMUM_GUARANTEED_SIZE
#define WCMP_GROUP_TABLE_MINIMUM_GUARANTEED_SIZE 0
#endif

// The maximum sum of weights across all wcmp groups.
#ifndef WCMP_GROUP_SELECTOR_MAX_SUM_OF_WEIGHTS_ACROSS_ALL_GROUPS
#define WCMP_GROUP_SELECTOR_MAX_SUM_OF_WEIGHTS_ACROSS_ALL_GROUPS 0
#endif

// The maximum sum of weights for each wcmp group.
#ifndef WCMP_GROUP_SELECTOR_MAX_SUM_OF_WEIGHTS_PER_GROUP
#define WCMP_GROUP_SELECTOR_MAX_SUM_OF_WEIGHTS_PER_GROUP 0
#endif

#endif  // SAI_MINIMUM_GUARANTEED_SIZES_P4_
