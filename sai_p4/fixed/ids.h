#ifndef SAI_IDS_H_
#define SAI_IDS_H_

// All declarations (tables, actions, action profiles, meters, counters) have a
// stable ID. This list will evolve as new declarations are added. IDs cannot be
// reused. If a declaration is removed, its ID macro is kept and marked reserved
// to avoid the ID being reused.
//
// The IDs are classified using the 8 most significant bits to be compatible
// with "6.3. ID Allocation for P4Info Objects" in the P4Runtime specification.

// --- Tables ------------------------------------------------------------------

// IDs of fixed SAI tables (8 most significant bits = 0x02).
#define ROUTING_NEIGHBOR_TABLE_ID 0x02000040            // 33554496
#define ROUTING_ROUTER_INTERFACE_TABLE_ID 0x02000041    // 33554497
#define ROUTING_NEXTHOP_TABLE_ID 0x02000042             // 33554498
#define ROUTING_WCMP_GROUP_TABLE_ID 0x02000043          // 33554499
#define ROUTING_IPV4_TABLE_ID 0x02000044                // 33554500
#define ROUTING_IPV6_TABLE_ID 0x02000045                // 33554501
#define ROUTING_VRF_TABLE_ID 0x0200004A                 // 33554506
#define MIRROR_SESSION_TABLE_ID 0x02000046              // 33554502
#define L3_ADMIT_TABLE_ID 0x02000047                    // 33554503
#define MIRROR_PORT_TO_PRE_SESSION_TABLE_ID 0x02000048  // 33554504
#define ECMP_HASHING_TABLE_ID 0x02000049                // 33554505
#define ROUTING_TUNNEL_TABLE_ID 0x02000050              // 33554512
#define IPV6_TUNNEL_TERMINATION_TABLE_ID 0x0200004B     // 33554507
// Next available table id: 0x0200004C (33554508)

// --- Actions -----------------------------------------------------------------

// IDs of fixed SAI actions (8 most significant bits = 0x01).
#define ROUTING_SET_DST_MAC_ACTION_ID 0x01000001                     // 16777217
#define ROUTING_SET_PORT_AND_SRC_MAC_ACTION_ID 0x01000002            // 16777218
#define ROUTING_SET_NEXTHOP_ACTION_ID 0x01000003                     // 16777219
#define ROUTING_SET_IP_NEXTHOP_ACTION_ID 0x01000014                  // 16777236
#define ROUTING_SET_WCMP_GROUP_ID_ACTION_ID 0x01000004               // 16777220
#define ROUTING_SET_WCMP_GROUP_ID_AND_METADATA_ACTION_ID 0x01000011  // 16777233
#define ROUTING_SET_NEXTHOP_ID_ACTION_ID 0x01000005                  // 16777221
#define ROUTING_SET_NEXTHOP_ID_AND_METADATA_ACTION_ID 0x01000010     // 16777232
#define ROUTING_DROP_ACTION_ID 0x01000006                            // 16777222
#define ROUTING_SET_P2P_TUNNEL_ENCAP_NEXTHOP_ACTION_ID 0x01000012    // 16777234
#define ROUTING_MARK_FOR_P2P_TUNNEL_ENCAP_ACTION_ID 0x01000013       // 16777235
#define MIRRORING_MIRROR_AS_IPV4_ERSPAN_ACTION_ID 0x01000007         // 16777223
#define L3_ADMIT_ACTION_ID 0x01000008                                // 16777224
#define MIRRORING_SET_PRE_SESSION_ACTION_ID 0x01000009               // 16777225
#define SELECT_ECMP_HASH_ALGORITHM_ACTION_ID 0x010000A               // 16777226
#define COMPUTE_ECMP_HASH_IPV4_ACTION_ID 0x0100000B                  // 16777227
#define COMPUTE_ECMP_HASH_IPV6_ACTION_ID 0x0100000C                  // 16777228
#define COMPUTE_LAG_HASH_IPV4_ACTION_ID 0x0100000D                   // 16777229
#define COMPUTE_LAG_HASH_IPV6_ACTION_ID 0x0100000E                   // 16777230
#define TRAP_ACTION_ID 0x0100000F                                    // 16777231
#define ROUTING_SET_METADATA_AND_DROP_ACTION_ID 0x01000015           // 16777237
#define MARK_FOR_TUNNEL_DECAP_AND_SET_VRF_ACTION_ID 0x01000016       // 16777238
// Next available action id: 0x01000017 (16777239)

// --- Action Profiles and Selectors (8 most significant bits = 0x11) ----------
// This value should ideally be 0x11000001, but we currently have this value for
// legacy reasons.
#define ROUTING_WCMP_GROUP_SELECTOR_ACTION_PROFILE_ID 0x11DC4EC8  // 299650760

// --- Intrinsic ports ---------------------------------------------------------

// Port used for PacketIO. Packets sent to this port go to the CPU.
// Packets received on this port come from the CPU.
// TODO For simplicity, we went with 510/511 as CPU/drop port to
// begin with, which are the values used by BMv2 by default, and the values
// hard-coded in p4-symbolic. We should revisit these arbitrary values.
#define SAI_P4_CPU_PORT 510

// The port used by `mark_to_drop` from v1model.p4. For details, see the
// documentation of `mark_to_drop`.
#define SAI_P4_DROP_PORT 511

// --- Copy to CPU session -----------------------------------------------------

// The COPY_TO_CPU_SESSION_ID must be programmed in the target using P4Runtime:
//
// type: INSERT
// entity {
//   packet_replication_engine_entry {
//     clone_session_entry {
//       session_id: COPY_TO_CPU_SESSION_ID
//       replicas {
//        egress_port: SAI_P4_CPU_PORT
//        instance: CLONE_REPLICA_INSTANCE_PACKET_IN
//       }
//     }
//   }
// }
//
#define COPY_TO_CPU_SESSION_ID 255

// --- Packet-IO ---------------------------------------------------------------

#define PACKET_IN_INGRESS_PORT_ID 1
#define PACKET_IN_TARGET_EGRESS_PORT_ID 2
#define PACKET_IN_UNUSED_PAD_ID 3

#define PACKET_OUT_EGRESS_PORT_ID 1
#define PACKET_OUT_SUBMIT_TO_INGRESS_ID 2
#define PACKET_OUT_UNUSED_PAD_ID 3

//--- Packet Replication Engine Instances --------------------------------------

// Egress instance type definitions.
// The egress instance is a 32-bit standard metadata set by the packet
// replication engine (PRE) in the V1Model architecture. However, the values are
// not defined by the P4 specification. Here we define our own values; these may
// be changed when we adopt another architecture.
#define CLONE_REPLICA_INSTANCE_PACKET_IN 1
#define CLONE_REPLICA_INSTANCE_MIRRORING 2

#endif  // SAI_IDS_H_
