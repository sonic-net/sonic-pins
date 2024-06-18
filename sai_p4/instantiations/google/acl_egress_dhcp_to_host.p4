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
#ifndef SAI_P4_GOOGLE_ACL_EGRESS_DHCP_TO_HOST_P4_
#define SAI_P4_GOOGLE_ACL_EGRESS_DHCP_TO_HOST_P4_

#include <v1model.p4>
#include "../../fixed/headers.p4"
#include "../../fixed/metadata.p4"
#include "acl_common_actions.p4"
#include "ids.h"
#include "minimum_guaranteed_sizes.p4"
#include "roles.h"

control acl_egress_dhcp_to_host(in headers_t headers,
                                inout local_metadata_t local_metadata,
                                inout standard_metadata_t standard_metadata) {
  // The IPv4 and IPv6 headers are both L3 protocols and share a lot of the same
  // packet data. To save on harware resources we can use a single match field
  // that extracts the packet value based on the header type.
  bit<8> ip_protocol = 0; // IPv4=ip_protocol, IPv6=next_header, non-IP=0

  @id(ACL_EGRESS_DHCP_TO_HOST_COUNTER_ID)
  direct_counter(CounterType.packets_and_bytes) acl_egress_dhcp_to_host_counter;

  @id(ACL_EGRESS_DHCP_TO_HOST_TABLE_ID)
  @sai_acl(EGRESS)
  @p4runtime_role(P4RUNTIME_ROLE_SDN_CONTROLLER)
  @entry_restriction("
    // Forbid using ether_type for IP packets (by convention, use is_ip* instead).
    ether_type != 0x0800 && ether_type != 0x86dd;
    // Only allow IP field matches for IP packets.
    ip_protocol::mask != 0 -> (is_ip == 1 || is_ipv4 == 1 || is_ipv6 == 1);
    // Only allow l4_dst_port matches for TCP/UDP packets.
    l4_dst_port::mask != 0 -> (ip_protocol == 6 || ip_protocol == 17);
    // Forbid illegal combinations of IP_TYPE fields.
    is_ip::mask != 0 -> (is_ipv4::mask == 0 && is_ipv6::mask == 0);
    is_ipv4::mask != 0 -> (is_ip::mask == 0 && is_ipv6::mask == 0);
    is_ipv6::mask != 0 -> (is_ip::mask == 0 && is_ipv4::mask == 0);
    // Forbid unsupported combinations of IP_TYPE fields.
    is_ipv4::mask != 0 -> (is_ipv4 == 1);
    is_ipv6::mask != 0 -> (is_ipv6 == 1);
  ")
  table acl_egress_dhcp_to_host_table {
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
      local_metadata.l4_dst_port : ternary
          @id(6) @name("l4_dst_port")
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_L4_DST_PORT);
      (port_id_t)standard_metadata.egress_port: optional
          @id(7) @name("out_port")
          @sai_field(SAI_ACL_TABLE_ATTR_FIELD_OUT_PORT);
    }
    actions = {
      @proto_id(1) acl_drop(standard_metadata);
      @defaultonly NoAction;
    }
    const default_action = NoAction;
    counters = acl_egress_dhcp_to_host_counter;
    size = ACL_EGRESS_TABLE_MINIMUM_GUARANTEED_SIZE;
  }

 apply {
    if (headers.ipv4.isValid()) {
      ip_protocol = headers.ipv4.protocol;
    } else if (headers.ipv6.isValid()) {
      ip_protocol = headers.ipv6.next_header;
    }

    acl_egress_dhcp_to_host_table.apply();
 }
} // control acl_egress_dhcp_to_host

#endif  // SAI_P4_GOOGLE_ACL_EGRESS_DHCP_TO_HOST_P4_
