// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
#ifndef SAI_P4_GOOGLE_ACL_PRE_INGRESS_VLAN_P4_
#define SAI_P4_GOOGLE_ACL_PRE_INGRESS_VLAN_P4_

#include <v1model.p4>
#include "../../fixed/headers.p4"
#include "../../fixed/metadata.p4"
#include "ids.h"
#include "minimum_guaranteed_sizes.p4"
#include "roles.h"

control acl_pre_ingress_vlan(in headers_t headers,
                             inout local_metadata_t local_metadata,
                             in standard_metadata_t standard_metadata) {
  @id(ACL_PRE_INGRESS_VLAN_COUNTER_ID)
  direct_counter(CounterType.packets_and_bytes) acl_pre_ingress_vlan_counter;

  @id(ACL_PRE_INGRESS_SET_OUTER_VLAN_ACTION_ID)
  @sai_action(SAI_PACKET_ACTION_FORWARD)
  action set_outer_vlan_id(
      @id(1) @sai_action_param(SAI_ACL_ENTRY_ATTR_ACTION_SET_OUTER_VLAN_ID)
        vlan_id_t vlan_id) {
    local_metadata.vlan_id_valid = true;
    local_metadata.vlan_id = headers.vlan.vlan_id;
    acl_pre_ingress_vlan_counter.count();
  }

  @id(ACL_PRE_INGRESS_VLAN_TABLE_ID)
  @sai_acl(PRE_INGRESS)
  @p4runtime_role(P4RUNTIME_ROLE_SDN_CONTROLLER)
  table acl_pre_ingress_vlan_table {
    key = {
      headers.ethernet.ether_type : ternary
         @id(1) @name("ether_type")
         @sai_field(SAI_ACL_TABLE_ATTR_FIELD_ETHER_TYPE);
    }
    actions = {
      @proto_id(1) set_outer_vlan_id;
      @defaultonly NoAction;
    }
    const default_action = NoAction;
    counters = acl_pre_ingress_vlan_counter;
    size = ACL_PRE_INGRESS_TABLE_MINIMUM_GUARANTEED_SIZE;
  }

  apply {
    acl_pre_ingress_vlan_table.apply();
  }
}  // control acl_pre_ingress_vlan

#endif  // SAI_P4_GOOGLE_ACL_PRE_INGRESS_VLAN_P4_
