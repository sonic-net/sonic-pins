#ifndef SAI_ACL_COMMON_ACTIONS_P4_
#define SAI_ACL_COMMON_ACTIONS_P4_

#include <v1model.p4>
#include "ids.h"

// This file lists ACL actions that may be used in multiple control blocks.

// Drop the packet at the end of the current pipeline (ingress or egress). See
// "mark_to_drop" in google3/third_party/p4lang_p4c/p4include/v1model.p4 for
// more information.
@id(ACL_DROP_ACTION_ID)
@sai_action(SAI_PACKET_ACTION_DROP)
action acl_drop(inout standard_metadata_t standard_metadata) {
  mark_to_drop(standard_metadata);
}

#endif  // SAI_ACL_COMMON_ACTIONS_P4_
