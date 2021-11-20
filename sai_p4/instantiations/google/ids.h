#ifndef GOOGLE_SAI_IDS_H_
#define GOOGLE_SAI_IDS_H_

#include "../../fixed/ids.h"

// All declarations (tables, actions, action profiles, meters, counters) have a
// stable ID. This list will evolve as new declarations are added. IDs cannot be
// reused. If a declaration is removed, its ID macro is kept and marked reserved
// to avoid the ID being reused.
//
// The IDs are classified using the 8 most significant bits to be compatible
// with "6.3. ID Allocation for P4Info Objects" in the P4Runtime specification.

// --- Tables ------------------------------------------------------------------

// IDs of ACL tables (8 most significant bits = 0x02).
// Since these IDs are user defined, they need to be separate from the fixed SAI
// table ID space. We achieve this by starting the IDs at 0x100.
#define ACL_INGRESS_TABLE_ID 0x02000100      // 33554688
#define ACL_PRE_INGRESS_TABLE_ID 0x02000101  // 33554689
#define ACL_WBB_INGRESS_TABLE_ID 0x02000103  // 33554691
#define ACL_EGRESS_TABLE_ID 0x02000104       // 33554692

// --- Actions -----------------------------------------------------------------

// IDs of ACL actions (8 most significant bits = 0x01).
// Since these IDs are user defined, they need to be separate from the fixed SAI
// actions ID space. We achieve this by starting the IDs at 0x100.
#define ACL_PRE_INGRESS_SET_VRF_ACTION_ID 0x01000100  // 16777472
#define ACL_INGRESS_COPY_ACTION_ID 0x01000101         // 16777473
#define ACL_INGRESS_TRAP_ACTION_ID 0x01000102         // 16777474
#define ACL_INGRESS_FORWARD_ACTION_ID 0x01000103      // 16777475
#define ACL_INGRESS_MIRROR_ACTION_ID 0x01000104       // 16777476
#define ACL_WBB_INGRESS_COPY_ACTION_ID 0x01000107     // 16777479
#define ACL_WBB_INGRESS_TRAP_ACTION_ID 0x01000108     // 16777480
#define ACL_DROP_ACTION_ID 0x01000109                 // 16777481

// --- Meters ------------------------------------------------------------------
#define ACL_INGRESS_METER_ID 0x15000100      // 352321792
#define ACL_WBB_INGRESS_METER_ID 0x15000101  // 352321793

// --- Counters ----------------------------------------------------------------
#define ACL_PRE_INGRESS_COUNTER_ID 0x13000101  // 318767361
#define ACL_INGRESS_COUNTER_ID 0x13000102      // 318767362
#define ACL_WBB_INGRESS_COUNTER_ID 0x13000103  // 318767363

#endif  // GOOGLE_SAI_IDS_H_
