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
#ifndef SAI_P4_GOOGLE_ACL_PRE_INGRESS_METADATA_P4_
#define SAI_P4_GOOGLE_ACL_PRE_INGRESS_METADATA_P4_

#include <v1model.p4>
#include "../../fixed/headers.p4"
#include "../../fixed/metadata.p4"
#include "ids.h"
#include "minimum_guaranteed_sizes.p4"
#include "roles.h"

control acl_pre_ingress_metadata(
    in headers_t headers, inout local_metadata_t local_metadata,
    in standard_metadata_t standard_metadata) {
  // IPv4 IP protocol or IPv6 next_header (or 0, for non-IP packets)
  bit<8> ip_protocol = 0;

  @id(ACL_PRE_INGRESS_METADATA_COUNTER_ID)
  direct_counter(CounterType.packets_and_bytes) acl_pre_ingress_metadata_counter;

  @id(ACL_PRE_INGRESS_SET_ACL_METADATA_ACTION_ID)
  @sai_action(SAI_PACKET_ACTION_FORWARD)
  // TODO: OA does not support SAI_ACL_ENTRY_ATTR_ACTION_SET_ACL_META_DATA
  // action set_acl_metadata(
  //      @id(1) @sai_action_param(SAI_ACL_ENTRY_ATTR_ACTION_SET_ACL_META_DATA)
  //        acl_metadata_t acl_metadata) {
  //   local_metadata.acl_metadata = acl_metadata;
  //   acl_pre_ingress_metadata_counter.count();
  // }
  action set_acl_metadata() {
    acl_pre_ingress_metadata_counter.count();
  }

  @id(ACL_PRE_INGRESS_METADATA_TABLE_ID)
  @sai_acl(PRE_INGRESS)
  @p4runtime_role(P4RUNTIME_ROLE_SDN_CONTROLLER)
  @entry_restriction("
    // Forbid illegal combinations of IP_TYPE fields.
    is_ip::mask != 0 -> (is_ipv4::mask == 0 && is_ipv6::mask == 0);
    is_ipv4::mask != 0 -> (is_ip::mask == 0 && is_ipv6::mask == 0);
    is_ipv6::mask != 0 -> (is_ip::mask == 0 && is_ipv4::mask == 0);
    // Forbid unsupported combinations of IP_TYPE fields.
    is_ipv4::mask != 0 -> (is_ipv4 == 1);
    is_ipv6::mask != 0 -> (is_ipv6 == 1);
  ")
  table acl_pre_ingress_metadata_table {
    key = {
      headers.ipv4.isValid() || headers.ipv6.isValid() : optional
          @id(1) @name("is_ip")
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_ACL_IP_TYPE/IP);
      headers.ipv4.isValid() : optional
          @id(2) @name("is_ipv4")
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_ACL_IP_TYPE/IPV4ANY);
      headers.ipv6.isValid() : optional
          @id(3) @name("is_ipv6")
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_ACL_IP_TYPE/IPV6ANY);
      headers.ethernet.ether_type : ternary
          @id(4) @name("ether_type")
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_ETHER_TYPE);
      ip_protocol : ternary
          @id(5) @name("ip_protocol")
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_IP_PROTOCOL);
      local_metadata.l4_src_port : ternary
          @id(6) @name("l4_src_port")
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_L4_SRC_PORT);
    }
    actions = {
      @proto_id(1) set_acl_metadata;
      @defaultonly NoAction;
    }
    const default_action = NoAction;
    counters = acl_pre_ingress_metadata_counter;
    size = ACL_PRE_INGRESS_TABLE_MINIMUM_GUARANTEED_SIZE;
  }

  apply {
    if (headers.ipv4.isValid()) {
      ip_protocol = headers.ipv4.protocol;
    } else if (headers.ipv6.isValid()) {
      ip_protocol = headers.ipv6.next_header;
    }

    acl_pre_ingress_metadata_table.apply();
  }
}  // control acl_pre_ingress_metadata

#endif  // SAI_P4_GOOGLE_ACL_PRE_INGRESS_METADATA_P4_
