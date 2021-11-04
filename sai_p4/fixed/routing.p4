#ifndef SAI_ROUTING_P4_
#define SAI_ROUTING_P4_

#include <v1model.p4>
#include "headers.p4"
#include "metadata.p4"
#include "ids.h"
#include "roles.h"
#include "minimum_guaranteed_sizes.p4"

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
//
// Note that this block does not rewrite any header fields directly, but only
// records rewrites in `local_metadata.packet_rewrites`, from where they will be
// read and applied in the egress stage.
control routing(in headers_t headers,
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

  // Sets SAI_NEIGHBOR_ENTRY_ATTR_DST_MAC_ADDRESS.
  @id(ROUTING_SET_DST_MAC_ACTION_ID)
  action set_dst_mac(@id(1) @format(MAC_ADDRESS) ethernet_addr_t dst_mac) {
    local_metadata.packet_rewrites.dst_mac = dst_mac;
  }

  @p4runtime_role(P4RUNTIME_ROLE_ROUTING)
  @id(ROUTING_NEIGHBOR_TABLE_ID)
  table neighbor_table {
    key = {
      // Sets rif_id in sai_neighbor_entry_t. Can only refer to values that are
      // already programmed in the `router_interface_table`.
      router_interface_id_value : exact @id(1) @name("router_interface_id")
          @refers_to(router_interface_table, router_interface_id);
      // Sets ip_address in sai_neighbor_entry_t.
      neighbor_id_value : exact @id(2) @name("neighbor_id");
    }
    actions = {
      @proto_id(1) set_dst_mac;
      @defaultonly NoAction;
    }
    const default_action = NoAction;
    size = NEIGHBOR_TABLE_MINIMUM_GUARANTEED_SIZE;
  }

  // Sets SAI_ROUTER_INTERFACE_ATTR_TYPE to SAI_ROUTER_INTERFACE_TYPE_PORT, and
  // SAI_ROUTER_INTERFACE_ATTR_PORT_ID, and
  // SAI_ROUTER_INTERFACE_ATTR_SRC_MAC_ADDRESS.
  @id(ROUTING_SET_PORT_AND_SRC_MAC_ACTION_ID)
  action set_port_and_src_mac(@id(1) port_id_t port,
                              @id(2) @format(MAC_ADDRESS)
                              ethernet_addr_t src_mac) {
    // Cast is necessary, because v1model does not define port using `type`.
    standard_metadata.egress_spec = (bit<PORT_BITWIDTH>)port;
    local_metadata.packet_rewrites.src_mac = src_mac;
  }

  @p4runtime_role(P4RUNTIME_ROLE_ROUTING)
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
    size = ROUTER_INTERFACE_TABLE_MINIMUM_GUARANTEED_SIZE;
  }

  // Sets SAI_NEXT_HOP_ATTR_TYPE to SAI_NEXT_HOP_TYPE_IP, and
  // SAI_NEXT_HOP_ATTR_ROUTER_INTERFACE_ID, and SAI_NEXT_HOP_ATTR_IP.
  //
  // This action can only refer to `router_interface_id`s and `neighbor_id`s,
  // if `router_interface_id` is a key in the `router_interface_table`, and
  // the `(router_interface_id, neighbor_id)` pair is a key in the
  // `neighbor_table`.
  //
  // Note that the @refers_to annotation could be more precise if it allowed
  // specifying that the pair (router_interface_id, neighbor_id) refers to the
  // two match fields in neighbor_table. This is still correct, but less
  // precise.
  @id(ROUTING_SET_NEXTHOP_ACTION_ID)
  action set_nexthop(@id(1)
                     @refers_to(router_interface_table, router_interface_id)
                     @refers_to(neighbor_table, router_interface_id)
                     router_interface_id_t router_interface_id,
                     @id(2) @refers_to(neighbor_table, neighbor_id)
                     neighbor_id_t neighbor_id) {
    router_interface_id_valid = true;
    router_interface_id_value = router_interface_id;
    neighbor_id_valid = true;
    neighbor_id_value = neighbor_id;
  }

  @p4runtime_role(P4RUNTIME_ROLE_ROUTING)
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
    size = NEXTHOP_TABLE_MINIMUM_GUARANTEED_SIZE;
  }

  // When called from a route, sets SAI_ROUTE_ENTRY_ATTR_PACKET_ACTION to
  // SAI_PACKET_ACTION_FORWARD, and SAI_ROUTE_ENTRY_ATTR_NEXT_HOP_ID to a
  // SAI_OBJECT_TYPE_NEXT_HOP.
  //
  // When called from a group, sets SAI_NEXT_HOP_GROUP_MEMBER_ATTR_NEXT_HOP_ID.
  // When called from a group, sets SAI_NEXT_HOP_GROUP_MEMBER_ATTR_WEIGHT.
  //
  // This action can only refer to `nexthop_id`s that are programmed in the
  // `nexthop_table`.
  @id(ROUTING_SET_NEXTHOP_ID_ACTION_ID)
  action set_nexthop_id(@id(1) @refers_to(nexthop_table, nexthop_id)
                        nexthop_id_t nexthop_id) {
    nexthop_id_valid = true;
    nexthop_id_value = nexthop_id;
  }

  @max_group_size(WCMP_GROUP_SELECTOR_MAX_SUM_OF_WEIGHTS_PER_GROUP)
  action_selector(HashAlgorithm.identity,
                  WCMP_GROUP_SELECTOR_MAX_SUM_OF_WEIGHTS_ACROSS_ALL_GROUPS,
                  WCMP_SELECTOR_INPUT_BITWIDTH)
      wcmp_group_selector;

  @p4runtime_role(P4RUNTIME_ROLE_ROUTING)
  @id(ROUTING_WCMP_GROUP_TABLE_ID)
  @oneshot()
  table wcmp_group_table {
    key = {
      wcmp_group_id_value : exact @id(1) @name("wcmp_group_id");
      local_metadata.wcmp_selector_input : selector;
    }
    actions = {
      @proto_id(1) set_nexthop_id;
      @defaultonly NoAction;
    }
    const default_action = NoAction;
    @id(ROUTING_WCMP_GROUP_SELECTOR_ACTION_PROFILE_ID)
        implementation = wcmp_group_selector;
    size = WCMP_GROUP_TABLE_MINIMUM_GUARANTEED_SIZE;
  }

  // Action that does nothing. Like `NoAction` in `core.p4`, but following
  // Google's naming conventions.
  // TODO: Add support for CamlCase actions to the PD generator,
  // so we can use `NoAction` throughout.
  action no_action() {}

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
  action set_wcmp_group_id(@id(1) @refers_to(wcmp_group_table, wcmp_group_id)
                           wcmp_group_id_t wcmp_group_id) {
    wcmp_group_id_valid = true;
    wcmp_group_id_value = wcmp_group_id;
  }

  @p4runtime_role(P4RUNTIME_ROLE_ROUTING)
  @id(ROUTING_IPV4_TABLE_ID)
  table ipv4_table {
    key = {
      // Sets vrf_id in sai_route_entry_t.
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
    size = ROUTING_IPV4_TABLE_MINIMUM_GUARANTEED_SIZE;
  }

  @p4runtime_role(P4RUNTIME_ROLE_ROUTING)
  @id(ROUTING_IPV6_TABLE_ID)
  table ipv6_table {
    key = {
      // Sets vrf_id in sai_route_entry_t.
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
    size = ROUTING_IPV6_TABLE_MINIMUM_GUARANTEED_SIZE;
  }

  apply {
    // Drop packets by default, then override in the router_interface_table.
    // TODO: This should just be the default behavior of v1model:
    // https://github.com/p4lang/behavioral-model/issues/992
    mark_to_drop(standard_metadata);

    if (local_metadata.admit_to_l3) {

      if (headers.ipv4.isValid()) {
        ipv4_table.apply();
      } else if (headers.ipv6.isValid()) {
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
  }
}  // control routing

#endif  // SAI_ROUTING_P4_
