// Rename this for the open source version.
#ifndef P4_SAI_IDS_H_
#define P4_SAI_IDS_H_

// All declarations (tables, actions, action profiles, meters, counters) have a
// stable ID. This list will evolve as new declarations are added. IDs cannot be
// reused. If a declaration is removed, its ID macro is kept and marked reserved
// to avoid the ID being reused.
//
// The IDs are classified using the 8 most significant bits to be compatible
// with "6.3. ID Allocation for P4Info Objects" in the P4Runtime specification.

// IDs of fixed SAI tables (8 most significant bits = 0x02).
#define ROUTING_NEIGHBOR_TABLE_ID 0x02000040          // 33554496
#define ROUTING_ROUTER_INTERFACE_TABLE_ID 0x02000041  // 33554497
#define ROUTING_NEXTHOP_TABLE_ID 0x02000042           // 33554498
#define ROUTING_WCMP_GROUP_TABLE_ID 0x02000043        // 33554499
#define ROUTING_IPV4_TABLE_ID 0x02000044              // 33554500
#define ROUTING_IPV6_TABLE_ID 0x02000045              // 33554501

// IDs of ACL tables (8 most significant bits = 0x02).
// Since these IDs are user defined, they need to be separate from the fixed SAI
// table ID space. We achieve this by starting the IDs at 0x100.
#define ACL_PUNT_TABLE_ID 0x02000100     // 33554688
#define ACL_SET_VRF_TABLE_ID 0x02000101  // 33554689

// IDs of fixed SAI actions (8 most significant bits = 0x01).
#define ROUTING_SET_DST_MAC_ACTION_ID 0x01000001           // 16777217
#define ROUTING_SET_PORT_AND_SRC_MAC_ACTION_ID 0x01000002  // 16777218
#define ROUTING_SET_NEXTHOP_ACTION_ID 0x01000003           // 16777219
#define ROUTING_SET_WCMP_GROUP_ID_ACTION_ID 0x01000004     // 16777220
#define ROUTING_SET_NEXTHOP_ID_ACTION_ID 0x01000005        // 16777221
#define ROUTING_DROP_ACTION_ID 0x01000006                  // 16777222
#define ACL_COPY_ACTION_ID 0x01000007                      // 16777223
#define ACL_TRAP_ACTION_ID 0x01000008                      // 16777224

// IDs of ACL actions (8 most significant bits = 0x01).
// Since these IDs are user defined, they need to be separate from the fixed SAI
// actions ID space. We achieve this by starting the IDs at 0x100.
#define ACL_SET_VRF_SET_VRF_ACTION_ID 0x01000100  // 16777472

// The COPY_TO_CPU_SESSION_ID must be programmed in the target using P4Runtime:
//
// type: INSERT
// entity {
//   packet_replication_engine_entry {
//     clone_session_entry {
//       session_id: COPY_TO_CPU_SESSION_ID
//       replicas { egress_port: 0xfffffffd } # to CPU
//     }
//   }
// }
//
#define COPY_TO_CPU_SESSION_ID 1024

#endif  // P4_SAI_IDS_H_
