#ifndef SAI_ACL_ACTIONS_P4_
#define SAI_ACL_ACTIONS_P4_

#include "v1model.p4"

// User defined ACL tables can use the actions from this file.

// Copy the packet to the CPU. The original packet proceeds unmodified.
@id(ACL_COPY_ACTION_ID)
@sai_action(SAI_PACKET_ACTION_COPY)
action copy(inout standard_metadata_t standard_metadata) {
  clone(CloneType.I2E, COPY_TO_CPU_SESSION_ID);
}

// Copy the packet to the CPU. The original packet is dropped.
@id(ACL_TRAP_ACTION_ID)
@sai_action(SAI_PACKET_ACTION_TRAP)
action trap(inout standard_metadata_t standard_metadata) {
  copy(standard_metadata);
  mark_to_drop(standard_metadata);
}

#endif  // SAI_ACL_ACTIONS_P4_
