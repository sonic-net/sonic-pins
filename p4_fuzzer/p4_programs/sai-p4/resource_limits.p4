#ifndef SAI_RESOURCE_LIMITS_P4_
#define SAI_RESOURCE_LIMITS_P4_

#define MAX_PORTS_LOG2 9

#define MAX_VRFS_LOG2 10

#define MAX_NEXTHOPS 1024
#define MAX_NEXTHOPS_LOG2 10

#define MAX_NEIGHBORS 1024
#define MAX_NEIGHBORS_LOG2 10

#define MAX_ROUTER_INTERFACES 1024
#define MAX_ROUTER_INTERFACES_LOG2 10

// The maximum number of wcmp groups.
#define MAX_WCMP_GROUPS 4096
#define MAX_WCMP_GROUPS_LOG2 12

// The maximum sum of weights across all wcmp groups.
#define MAX_WCMP_GROUPS_SUM_OF_WEIGHTS 65536

// The maximum sum of weights for each wcmp group.
#define MAX_WCMP_GROUP_SUM_OF_WEIGHTS_LOG2 7

#define PUNT_TABLE_SIZE 128
#define SET_VRF_TABLE_SIZE 256

#endif  // SAI_RESOURCE_LIMITS_P4_
