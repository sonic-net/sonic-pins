#ifndef SAI_ROUTING_P4_
#define SAI_ROUTING_P4_

#include "v1model.p4"
#include "headers.p4"
#include "metadata.p4"
#include "ids.h"
#include "resource_limits.p4"

// This control block models the L3 routing pipeline.
//
// +-------+   +-------+ wcmp  +---------+       +-----------+
// |  lpm  |-->| group |------>| nexthop |----+->| router    |--> egress_port
// |       |   |       |------>|         |-+  |  | interface |--> src_mac
// +-------+   +-------+       +---------+ |  |  +-----------+
//   |   |                         ^       |  |  +-----------+
//   |   |                         |       |  +->| neighbor  |
//   V   +-------------------------+       +---->|           |--> dst_mac
//  drop                                         +-----------+
//
// The pipeline first performs a longest prefix match on the packet's
// destination IP address. The action associated with the match then either
// drops the packet, points to a nexthop, or points to a wcmp group which uses a
// hash of the packet to choose from a set of nexthops. The nexthop points to a
// router interface, which determines the packet's src_mac and the egress_port
// to forward the packet to. The nexthop also points to a neighbor which,
// together with the router_interface, determines the packet's dst_mac.
control routing(inout headers_t headers,
                inout local_metadata_t local_metadata,
                inout standard_metadata_t standard_metadata) {
  // Wcmp group id, only valid if `wcmp_group_id_valid` is true.
  bool wcmp_group_id_valid = false;
  wcmp_group_id_t wcmp_group_id_value;

  // Nexthop id, only valid if `nexthop_id_valid` is true.
  bool nexthop_id_valid = false;
  nexthop_id_t nexthop_id_value;

  // Router interface id, only valid if `router_interface_id_valid` is true.
  bool router_interface_id_valid = false;
  router_interface_id_t router_interface_id_value;

  // Neighbor id, only valid if `neighbor_id_valid` is true.
  bool neighbor_id_valid = false;
  neighbor_id_t neighbor_id_value;

  const bit<1> HASH_BASE_CRC16 = 1w0;
  const bit<14> HASH_MAX_CRC16 = 14w1024;
  bit<MAX_WCMP_GROUP_SUM_OF_WEIGHTS_LOG2> wcmp_selector_input = 0;

  // Sets SAI_NEIGHBOR_ENTRY_ATTR_DST_MAC_ADDRESS.
  @id(ROUTING_SET_DST_MAC_ACTION_ID)
  action set_dst_mac(@id(1) @format(MAC_ADDRESS) ethernet_addr_t dst_mac) {
    headers.ethernet.dst_addr = dst_mac;
  }

  @proto_package("sai")
  @id(ROUTING_NEIGHBOR_TABLE_ID)
  table neighbor_table {
    key = {
      // Sets rif_id in sai_neighbor_entry_t.
      router_interface_id_value : exact @id(1)
                                        @name("router_interface_id");
      // Sets ip_address in sai_neighbor_entry_t.
      neighbor_id_value : exact @id(2) @name("neighbor_id");
    }
    actions = {
      @proto_id(1) set_dst_mac;
      @defaultonly NoAction;
    }
    const default_action = NoAction;
  }

  // Sets SAI_ROUTER_INTERFACE_ATTR_TYPE to SAI_ROUTER_INTERFACE_TYPE_PORT, and
  // SAI_ROUTER_INTERFACE_ATTR_PORT_ID, and
  // SAI_ROUTER_INTERFACE_ATTR_SRC_MAC_ADDRESS.
  @id(ROUTING_SET_PORT_AND_SRC_MAC_ACTION_ID)
  action set_port_and_src_mac(@id(1) port_id_t port_id,
                              @id(2) @format(MAC_ADDRESS)
                              ethernet_addr_t src_mac) {
    // Cast is necessary, because v1model does not define port using `type`.
    standard_metadata.egress_spec = (bit<MAX_PORTS_LOG2>)port_id;
    headers.ethernet.src_addr = src_mac;
  }

  @proto_package("sai")
  @id(ROUTING_ROUTER_INTERFACE_TABLE_ID)
  table router_interface_table {
    key = {
      router_interface_id_value : exact @id(1)
                                        @name("router_interface_id");
    }
    actions = {
      @proto_id(1) set_port_and_src_mac;
      @defaultonly NoAction;
    }
    const default_action = NoAction;
  }

  // Sets SAI_NEXT_HOP_ATTR_TYPE to SAI_NEXT_HOP_TYPE_IP, and
  // SAI_NEXT_HOP_ATTR_ROUTER_INTERFACE_ID, and SAI_NEXT_HOP_ATTR_IP.
  //
  // This action can only refer to `router_interface_id`s and `neighbor_id`s
  // that are programmed in the `router_interface_table` and `neighbor_table`.
  @id(ROUTING_SET_NEXTHOP_ACTION_ID)
  action set_nexthop(@id(1) router_interface_id_t router_interface_id,
                     @id(2) neighbor_id_t neighbor_id) {
    router_interface_id_valid = true;
    router_interface_id_value = router_interface_id;
    neighbor_id_valid = true;
    neighbor_id_value = neighbor_id;
  }

  @proto_package("sai")
  @id(ROUTING_NEXTHOP_TABLE_ID)
  table nexthop_table {
    key = {
      nexthop_id_value : exact @id(1) @name("nexthop_id");
    }
    actions = {
      @proto_id(1) set_nexthop;
      @defaultonly NoAction;
    }
    const default_action = NoAction;
  }

  // When called from a route, sets SAI_ROUTE_ENTRY_ATTR_PACKET_ACTION to
  // SAI_PACKET_ACTION_FORWARD, and SAI_ROUTE_ENTRY_ATTR_NEXT_HOP_ID to a
  // SAI_OBJECT_TYPE_NEXT_HOP.
  //
  // When called from a group, sets SAI_NEXT_HOP_GROUP_MEMBER_ATTR_NEXT_HOP_ID.
  //
  // This action can only refer to `nexthop_id`s that are programmed in the
  // `nexthop_table`.
  @id(ROUTING_SET_NEXTHOP_ID_ACTION_ID)
  action set_nexthop_id(@id(1) nexthop_id_t nexthop_id) {
    nexthop_id_valid = true;
    nexthop_id_value = nexthop_id;
  }

  action_selector(HashAlgorithm.identity,
                  MAX_WCMP_GROUPS_SUM_OF_WEIGHTS,
                  MAX_WCMP_GROUP_SUM_OF_WEIGHTS_LOG2) wcmp_group_selector;

  @proto_package("sai")
  @id(ROUTING_WCMP_GROUP_TABLE_ID)
  @weight_proto_id(1)
  @oneshot()
  @weight_proto_tag(2)  // Sets SAI_NEXT_HOP_GROUP_MEMBER_ATTR_WEIGHT.
  table wcmp_group_table {
    key = {
      wcmp_group_id_value : exact @id(1) @name("wcmp_group_id");
      wcmp_selector_input : selector;
    }
    actions = {
      @proto_id(1) set_nexthop_id;
      @defaultonly NoAction;
    }
    const default_action = NoAction;
    implementation = wcmp_group_selector;
  }

  // Sets SAI_ROUTE_ENTRY_ATTR_PACKET_ACTION to SAI_PACKET_ACTION_DROP.
  @id(ROUTING_DROP_ACTION_ID)
  action drop() {
    mark_to_drop(standard_metadata);
  }

  // Sets SAI_ROUTE_ENTRY_ATTR_PACKET_ACTION to SAI_PACKET_ACTION_FORWARD, and
  // SAI_ROUTE_ENTRY_ATTR_NEXT_HOP_ID to a SAI_OBJECT_TYPE_NEXT_HOP_GROUP.
  //
  // This action can only refer to `wcmp_group_id`s that are programmed in the
  // `wcmp_group_table`.
  @id(ROUTING_SET_WCMP_GROUP_ID_ACTION_ID)
  action set_wcmp_group_id(@id(1) wcmp_group_id_t wcmp_group_id) {
    wcmp_group_id_valid = true;
    wcmp_group_id_value = wcmp_group_id;
  }

  @proto_package("sai")
  @id(ROUTING_IPV4_TABLE_ID)
  table ipv4_table {
    key = {
      // Sets vr_id in sai_route_entry_t.
      local_metadata.vrf_id : exact @id(1) @name("vrf_id");
      // Sets destination in sai_route_entry_t to an IPv4 prefix.
      headers.ipv4.dst_addr : lpm @format(IPV4_ADDRESS) @id(2)
                                  @name("ipv4_dst");
    }
    actions = {
      @proto_id(1) drop;
      @proto_id(2) set_nexthop_id;
      @proto_id(3) set_wcmp_group_id;
    }
    const default_action = drop;
  }

  @proto_package("sai")
  @id(ROUTING_IPV6_TABLE_ID)
  table ipv6_table {
    key = {
      // Sets vr_id in sai_route_entry_t.
      local_metadata.vrf_id : exact @id(1) @name("vrf_id");
      // Sets destination in sai_route_entry_t to an IPv6 prefix.
      headers.ipv6.dst_addr : lpm @format(IPV6_ADDRESS) @id(2)
                                  @name("ipv6_dst");
    }
    actions = {
      @proto_id(1) drop;
      @proto_id(2) set_nexthop_id;
      @proto_id(3) set_wcmp_group_id;
    }
    const default_action = drop;
  }

  apply {
    if (headers.ipv4.isValid()) {
      hash(wcmp_selector_input, HashAlgorithm.crc16, HASH_BASE_CRC16, {
           headers.ipv4.dst_addr, headers.ipv4.src_addr,
           local_metadata.l4_src_port, local_metadata.l4_dst_port},
           HASH_MAX_CRC16);
      ipv4_table.apply();
    } else if (headers.ipv6.isValid()) {
      hash(wcmp_selector_input, HashAlgorithm.crc16, HASH_BASE_CRC16, {
           headers.ipv6.dst_addr, headers.ipv6.src_addr,
           headers.ipv6.flow_label[15:0], local_metadata.l4_src_port,
           local_metadata.l4_dst_port}, HASH_MAX_CRC16);
      ipv6_table.apply();
    }

    // The lpm tables may not set a valid `wcmp_group_id`, e.g. they may drop.
    if (wcmp_group_id_valid) {
      wcmp_group_table.apply();
    }

    // The lpm tables may not set a valid `nexthop_id`, e.g. they may drop.
    // The `wcmp_group_table` should always set a valid `nexthop_id`.
    if (nexthop_id_valid) {
      nexthop_table.apply();

      // The `nexthop_table` should always set a valid
      // `router_interface_id` and `neighbor_id`.
      if (router_interface_id_valid && neighbor_id_valid) {
        router_interface_table.apply();
        neighbor_table.apply();
      }
    }
  }
}  // control l3_fwd

#endif  // SAI_L3_FWD_P4_
