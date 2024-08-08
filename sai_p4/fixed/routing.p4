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
  ipv6_addr_t neighbor_id_value;

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
      neighbor_id_value : exact @id(2) @format(IPV6_ADDRESS)
          @name("neighbor_id");
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
  @id(ROUTING_SET_IP_NEXTHOP_ACTION_ID)
  action set_ip_nexthop(@id(1)
                        @refers_to(router_interface_table, router_interface_id)
                        @refers_to(neighbor_table, router_interface_id)
                        router_interface_id_t router_interface_id,
                        @id(2) @format(IPV6_ADDRESS)
                        @refers_to(neighbor_table, neighbor_id)
                        ipv6_addr_t neighbor_id) {
    router_interface_id_valid = true;
    router_interface_id_value = router_interface_id;
    neighbor_id_valid = true;
    neighbor_id_value = neighbor_id;
  }

  @id(ROUTING_SET_NEXTHOP_ACTION_ID)
  @deprecated("Use set_ip_nexthop instead.")
  // TODO: Remove this action once migration to `set_ip_nexthop`
  // is complete & rolled out.
  action set_nexthop(@id(1)
                     @refers_to(router_interface_table, router_interface_id)
                     @refers_to(neighbor_table, router_interface_id)
                     router_interface_id_t router_interface_id,
                     @id(2)  @format(IPV6_ADDRESS)
                     @refers_to(neighbor_table, neighbor_id)
                     ipv6_addr_t neighbor_id) {
    set_ip_nexthop(router_interface_id, neighbor_id);
  }

  @p4runtime_role(P4RUNTIME_ROLE_ROUTING)
  @id(ROUTING_NEXTHOP_TABLE_ID)
  table nexthop_table {
    key = {
      nexthop_id_value : exact @id(1) @name("nexthop_id");
    }
    actions = {
      @proto_id(1) set_nexthop;
      @proto_id(3) set_ip_nexthop;
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

  // When called from a route, sets SAI_ROUTE_ENTRY_ATTR_PACKET_ACTION to
  // SAI_PACKET_ACTION_FORWARD, and SAI_ROUTE_ENTRY_ATTR_NEXT_HOP_ID to a
  // SAI_OBJECT_TYPE_NEXT_HOP.
  //
  // When called from a group, sets SAI_NEXT_HOP_GROUP_MEMBER_ATTR_NEXT_HOP_ID.
  // When called from a group, sets SAI_NEXT_HOP_GROUP_MEMBER_ATTR_WEIGHT.
  //
  // This action can only refer to `nexthop_id`s that are programmed in the
  // `nexthop_table`.
  //
  // Also sets the route metadata available for Ingress ACL lookup.
  @id(ROUTING_SET_NEXTHOP_ID_AND_METADATA_ACTION_ID)
  action set_nexthop_id_and_metadata(@id(1)
                                     @refers_to(nexthop_table, nexthop_id)
                                     nexthop_id_t nexthop_id,
                                     route_metadata_t route_metadata) {
    nexthop_id_valid = true;
    nexthop_id_value = nexthop_id;
    local_metadata.route_metadata = route_metadata;
  }

  // TODO: When the P4RT compiler supports the size selector
  // annotation, this should be used to specify the semantics.
  // @selector_size_semantics(WCMP_GROUP_SELECTOR_SIZE_SEMANTICS)
  // TODO: Uncomment when supported by the P4RT compiler.
  // @max_member_weight(WCMP_GROUP_SELECTOR_MAX_MEMBER_WEIGHT)
  @max_group_size(WCMP_GROUP_SELECTOR_MAX_GROUP_SIZE)
  action_selector(HashAlgorithm.identity,
		  WCMP_GROUP_SELECTOR_SIZE,
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

  // Action that does nothing. Like `NoAction` in `core.p4`.
  // TODO: Add support for CamlCase actions to the PD generator,
  // so we can use `NoAction` throughout.
  action no_action() {}

  // Programming this table does not affect packet forwarding directly -- the
  // table performs no actions -- but results in the creation/deletion of VRFs.
  // This is a prerequisite to using these VRFs, e.g. in the `ipv4_table` and
  // `ipv6_table` below, as is indicated by the `@refers_to(vrf_table, vrf_id)`
  // annotations.
  // TODO: Currently we don't expose any `sai_virtual_router_attr_t`
  // attributes here, but we may explore that in the future.
  @entry_restriction("
    // The VRF ID 0 (or '' in P4Runtime) encodes the default VRF, which cannot
    // be read or written via this table, but is always present implicitly.
    // TODO: This constraint should read `vrf_id != ''` (since
    // constraints are a control plane (P4Runtime) concept), but
    // p4-constraints does not currently support strings.
    vrf_id != 0;
  ")
  @p4runtime_role(P4RUNTIME_ROLE_ROUTING)
  @id(ROUTING_VRF_TABLE_ID)
  table vrf_table {
    key = {
      local_metadata.vrf_id : exact @id(1) @name("vrf_id");
    }
    actions = {
      // TODO: Add support for CamlCase actions to the PD generator
      // so we can use `NoAction` instead of `no_action`.
      @proto_id(1) no_action;
    }
    const default_action = no_action;
    size = ROUTING_VRF_TABLE_MINIMUM_GUARANTEED_SIZE;
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
  action set_wcmp_group_id(@id(1) @refers_to(wcmp_group_table, wcmp_group_id)
                           wcmp_group_id_t wcmp_group_id) {
    wcmp_group_id_valid = true;
    wcmp_group_id_value = wcmp_group_id;
  }

  // Sets SAI_ROUTE_ENTRY_ATTR_PACKET_ACTION to SAI_PACKET_ACTION_FORWARD, and
  // SAI_ROUTE_ENTRY_ATTR_NEXT_HOP_ID to a SAI_OBJECT_TYPE_NEXT_HOP_GROUP.
  //
  // This action can only refer to `wcmp_group_id`s that are programmed in the
  // `wcmp_group_table`.
  //
  // Also sets the route metadata available for Ingress ACL lookup.
  @id(ROUTING_SET_WCMP_GROUP_ID_AND_METADATA_ACTION_ID)
  action set_wcmp_group_id_and_metadata(@id(1)
                                        @refers_to(wcmp_group_table,
                                        wcmp_group_id)
                                        wcmp_group_id_t wcmp_group_id,
                                        route_metadata_t route_metadata) {
    set_wcmp_group_id(wcmp_group_id);
    local_metadata.route_metadata = route_metadata;
  }

  // Trap the packet and send it to CPU. Drop the packet in the dataplane.
  @id(TRAP_ACTION_ID)
  action trap() {
    clone(CloneType.I2E, COPY_TO_CPU_SESSION_ID);
    mark_to_drop(standard_metadata);
  }

#ifdef SAI_INSTANTIATION_FABRIC_BORDER_ROUTER
  // Set the metadata of the packet and mark the packet to drop at the end of
  // the ingress pipeline.
  @id(ROUTING_SET_METADATA_AND_DROP_ACTION_ID)
  action set_metadata_and_drop(@id(1) route_metadata_t route_metadata) {
    local_metadata.route_metadata = route_metadata;
    mark_to_drop(standard_metadata);
  }
#endif

   @p4runtime_role(P4RUNTIME_ROLE_ROUTING)
  @id(ROUTING_IPV4_TABLE_ID)
  table ipv4_table {
    key = {
      // Sets vrf_id in sai_route_entry_t.
      local_metadata.vrf_id : exact @id(1) @name("vrf_id")
          @refers_to(vrf_table, vrf_id);
      // Sets destination in sai_route_entry_t to an IPv4 prefix.
      headers.ipv4.dst_addr : lpm @format(IPV4_ADDRESS) @id(2)
                                  @name("ipv4_dst");
    }
    actions = {
      @proto_id(1) drop;
      @proto_id(2) set_nexthop_id;
      @proto_id(3) set_wcmp_group_id;
      @proto_id(4) trap;
      @proto_id(5) set_nexthop_id_and_metadata;
      @proto_id(6) set_wcmp_group_id_and_metadata;
#ifdef SAI_INSTANTIATION_FABRIC_BORDER_ROUTER
      @proto_id(7) set_metadata_and_drop;
#endif
    }
    const default_action = drop;
    size = ROUTING_IPV4_TABLE_MINIMUM_GUARANTEED_SIZE;
  }

  @p4runtime_role(P4RUNTIME_ROLE_ROUTING)
  @id(ROUTING_IPV6_TABLE_ID)
  table ipv6_table {
    key = {
      // Sets vrf_id in sai_route_entry_t.
      local_metadata.vrf_id : exact @id(1) @name("vrf_id")
          @refers_to(vrf_table, vrf_id);
      // Sets destination in sai_route_entry_t to an IPv6 prefix.
      headers.ipv6.dst_addr : lpm @format(IPV6_ADDRESS) @id(2)
                                  @name("ipv6_dst");
    }
    actions = {
      @proto_id(1) drop;
      @proto_id(2) set_nexthop_id;
      @proto_id(3) set_wcmp_group_id;
      @proto_id(4) trap;
      @proto_id(5) set_nexthop_id_and_metadata;
      @proto_id(6) set_wcmp_group_id_and_metadata;
#ifdef SAI_INSTANTIATION_FABRIC_BORDER_ROUTER
      @proto_id(7) set_metadata_and_drop;
#endif
    }
    const default_action = drop;
    size = ROUTING_IPV6_TABLE_MINIMUM_GUARANTEED_SIZE;
  }

  apply {
    // Drop packets by default, then override in the router_interface_table.
    // TODO: This should just be the default behavior of v1model:
    // https://github.com/p4lang/behavioral-model/issues/992
    mark_to_drop(standard_metadata);

    vrf_table.apply();

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
