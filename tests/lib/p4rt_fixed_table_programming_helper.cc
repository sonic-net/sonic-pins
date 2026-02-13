// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
#include "tests/lib/p4rt_fixed_table_programming_helper.h"

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/types/span.h"
#include "gutil/proto.h"
#include "gutil/status.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"

namespace pins {

namespace {

absl::StatusOr<p4::v1::Update> IpTableUpdate(const pdpi::IrP4Info& ir_p4_info,
                                             p4::v1::Update::Type type,
                                             pdpi::Format ip_type,
                                             const IpTableOptions& ip_options) {
  pdpi::IrUpdate ir_update;
  ir_update.set_type(type);
  pdpi::IrTableEntry* ir_table_entry =
      ir_update.mutable_entity()->mutable_table_entry();

  switch (ip_type) {
    case pdpi::Format::IPV4:
      ir_table_entry->set_table_name("ipv4_table");
      break;
    case pdpi::Format::IPV6:
      ir_table_entry->set_table_name("ipv6_table");
      break;
    default:
      return gutil::InvalidArgumentErrorBuilder()
             << "Unsupported IP type: " << ip_type;
  }

  // Always set the VRF ID.
  auto* vrf_id = ir_table_entry->add_matches();
  vrf_id->set_name("vrf_id");
  vrf_id->mutable_exact()->set_str(ip_options.vrf_id);

  // optionally set the IPv4 DST address.
  if (ip_options.dst_addr_lpm.has_value()) {
    auto* dst_addr = ir_table_entry->add_matches();

    switch (ip_type) {
      case pdpi::Format::IPV4:
        dst_addr->set_name("ipv4_dst");
        dst_addr->mutable_lpm()->mutable_value()->set_ipv4(
            ip_options.dst_addr_lpm->first);
        break;
      case pdpi::Format::IPV6:
        dst_addr->set_name("ipv6_dst");
        dst_addr->mutable_lpm()->mutable_value()->set_ipv6(
            ip_options.dst_addr_lpm->first);
        break;
      default:
        return gutil::InvalidArgumentErrorBuilder()
               << "Unsupported IP type: " << ip_type;
    }
    dst_addr->mutable_lpm()->set_prefix_length(ip_options.dst_addr_lpm->second);
  }

  std::string action_name;
  switch (ip_options.action) {
    case IpTableOptions::Action::kDrop:
      action_name =
          ip_options.metadata.has_value() ? "set_metadata_and_drop" : "drop";
      break;
    case IpTableOptions::Action::kSetNextHopId:
      action_name = ip_options.metadata.has_value()
                        ? "set_nexthop_id_and_metadata"
                        : "set_nexthop_id";
      break;
    case pins::IpTableOptions::Action::kSetWcmpGroupId:
      action_name = ip_options.metadata.has_value()
                        ? "set_wcmp_group_id_and_metadata"
                        : "set_wcmp_group_id";
      break;
  }
  auto* action = ir_table_entry->mutable_action();
  action->set_name(action_name);

  // optionally set any action parameters.
  if (ip_options.nexthop_id.has_value()) {
    auto* param = action->add_params();
    param->set_name("nexthop_id");
    param->mutable_value()->set_str(*ip_options.nexthop_id);
  }
  if (ip_options.wcmp_group_id.has_value()) {
    auto* param = action->add_params();
    param->set_name("wcmp_group_id");
    param->mutable_value()->set_str(*ip_options.wcmp_group_id);
  }
  if (ip_options.metadata.has_value()) {
    auto* param = action->add_params();
    param->set_name("route_metadata");
    param->mutable_value()->set_hex_str(
        absl::StrFormat("%#04x", *ip_options.metadata));
  }

  return pdpi::IrUpdateToPi(ir_p4_info, ir_update);
}

}  // namespace

std::string IpTableOptions::ToString() const {
  std::vector<std::string> result_lines = {
      absl::StrFormat("vrf_id: %s", vrf_id)};
  if (dst_addr_lpm.has_value()) {
    result_lines.push_back(absl::StrFormat(
        "dst_addr_lpm:  %s/%d", dst_addr_lpm->first, dst_addr_lpm->second));
  }
  std::string action_str;
  switch (action) {
    case Action::kDrop:
      result_lines.push_back("action: kDrop");
      break;
    case Action::kSetNextHopId:
      result_lines.push_back("action: kSetNextHopId");
      break;
    case Action::kSetWcmpGroupId:
      result_lines.push_back("action: kSetWcmpGroupId");
      break;
  }
  if (nexthop_id.has_value()) {
    result_lines.push_back(absl::StrFormat("nexthop_id: %s", *nexthop_id));
  }
  if (wcmp_group_id.has_value()) {
    result_lines.push_back(
        absl::StrFormat("wcmp_group_id: %s", *wcmp_group_id));
  }
  if (metadata.has_value()) {
    result_lines.push_back(absl::StrFormat("metadata: %d", *metadata));
  }

  return absl::StrJoin(result_lines, "\n");
}

absl::StatusOr<p4::v1::Update> RouterInterfaceTableUpdate(
    const pdpi::IrP4Info& ir_p4_info, p4::v1::Update::Type type,
    absl::string_view router_interface_id, absl::string_view port,
    absl::string_view src_mac) {
  pdpi::IrUpdate ir_update;
  // Use unicast_set_port_and_src_mac if set_port_and_src_mac is not supported
  // in the P4Info.
  absl::string_view action_name = "set_port_and_src_mac";
  if (!ir_p4_info.actions_by_name().contains(action_name)) {
    action_name = "unicast_set_port_and_src_mac";
  }
  RETURN_IF_ERROR(gutil::ReadProtoFromString(
      absl::Substitute(R"pb(
                         type: $0
                         entity {
                           table_entry {
                             table_name: "router_interface_table"
                             matches {
                               name: "router_interface_id"
                               exact { str: "$1" }
                             }
                             action {
                               name: "$2"
                               params {
                                 name: "port"
                                 value { str: "$3" }
                               }
                               params {
                                 name: "src_mac"
                                 value { mac: "$4" }
                               }
                             }
                           }
                         }
                       )pb",
                       type, router_interface_id, action_name, port, src_mac),
      &ir_update))
      << "invalid pdpi::IrUpdate string.";
  return pdpi::IrUpdateToPi(ir_p4_info, ir_update);
}

absl::StatusOr<p4::v1::Update> VlanTableUpdate(const pdpi::IrP4Info& ir_p4_info,
                                               p4::v1::Update::Type type,
                                               int32_t vlan) {
  pdpi::IrUpdate ir_update;
  ir_update.set_type(type);
  pdpi::IrTableEntry* ir_table_entry =
      ir_update.mutable_entity()->mutable_table_entry();
  ir_table_entry->set_table_name("vlan_table");

  auto* vlan_match = ir_table_entry->add_matches();
  vlan_match->set_name("vlan_id");
  vlan_match->mutable_exact()->set_hex_str(absl::StrFormat("0x%03x", vlan));

  auto* action = ir_table_entry->mutable_action();
  action->set_name("no_action");

  return pdpi::IrUpdateToPi(ir_p4_info, ir_update);
}

absl::StatusOr<p4::v1::Update> VlanMemberTableUpdate(
    const pdpi::IrP4Info& ir_p4_info, p4::v1::Update::Type type,
    int32_t port_id, int32_t vlan, bool tag) {
  pdpi::IrUpdate ir_update;
  ir_update.set_type(type);
  pdpi::IrTableEntry* ir_table_entry =
      ir_update.mutable_entity()->mutable_table_entry();
  ir_table_entry->set_table_name("vlan_membership_table");

  auto* vlan_match = ir_table_entry->add_matches();
  vlan_match->set_name("vlan_id");
  vlan_match->mutable_exact()->set_hex_str(absl::StrFormat("0x%03x", vlan));

  auto* port_match = ir_table_entry->add_matches();
  port_match->set_name("port");
  port_match->mutable_exact()->set_str(absl::StrCat(port_id));

  auto* action = ir_table_entry->mutable_action();
  if (tag) {
    action->set_name("make_tagged_member");
  } else {
    action->set_name("make_untagged_member");
  }

  return pdpi::IrUpdateToPi(ir_p4_info, ir_update);
}

absl::StatusOr<p4::v1::Update> MulticastRouterInterfaceTableUpdate(
    const pdpi::IrP4Info& ir_p4_info, p4::v1::Update::Type type,
    const MulticastReplica& replica) {
  pdpi::IrUpdate ir_update;
  ir_update.set_type(type);
  pdpi::IrTableEntry* ir_table_entry =
      ir_update.mutable_entity()->mutable_table_entry();
  ir_table_entry->set_table_name("multicast_router_interface_table");

  auto* port_match = ir_table_entry->add_matches();
  port_match->set_name("multicast_replica_port");
  port_match->mutable_exact()->set_str(replica.port);

  auto* instance_match = ir_table_entry->add_matches();
  instance_match->set_name("multicast_replica_instance");
  instance_match->mutable_exact()->set_hex_str(
      absl::StrFormat("0x%04x", replica.instance));

  if (replica.is_ip_mcast) {
    auto* action = ir_table_entry->mutable_action();
    action->set_name("multicast_set_src_mac_and_vlan_id");
    auto* action_param = action->add_params();
    action_param->set_name("src_mac");
    *action_param->mutable_value()->mutable_mac() = replica.src_mac;
    action_param = action->add_params();
    action_param->set_name("vlan_id");
    *action_param->mutable_value()->mutable_hex_str() =
        absl::StrFormat("0x%03x", replica.vlan);
  } else {
    auto* action = ir_table_entry->mutable_action();
    action->set_name("l2_multicast_passthrough");
  }

  return pdpi::IrUpdateToPi(ir_p4_info, ir_update);
}

absl::StatusOr<p4::v1::Update> MulticastGroupUpdate(
    const pdpi::IrP4Info& ir_p4_info, p4::v1::Update::Type type,
    uint32_t group_id, absl::Span<MulticastReplica> replicas) {
  pdpi::IrUpdate ir_update;
  ir_update.set_type(type);
  pdpi::IrPacketReplicationEngineEntry* ir_packet_replication_engine_entry =
      ir_update.mutable_entity()->mutable_packet_replication_engine_entry();

  auto* multicast_group_entry =
      ir_packet_replication_engine_entry->mutable_multicast_group_entry();
  multicast_group_entry->set_multicast_group_id(group_id);

  for (auto& replica : replicas) {
    auto* new_replica = multicast_group_entry->add_replicas();
    new_replica->set_port(replica.port);
    new_replica->set_instance(replica.instance);
  }

  return pdpi::IrUpdateToPi(ir_p4_info, ir_update);
}

absl::StatusOr<p4::v1::Update> Ipv4MulticastRouteUpdate(
    const pdpi::IrP4Info& ir_p4_info, p4::v1::Update::Type type,
    const std::string& vrf_id, const std::string& addr, int32_t group_id) {
  pdpi::IrUpdate ir_update;
  ir_update.set_type(type);
  pdpi::IrTableEntry* ir_table_entry =
      ir_update.mutable_entity()->mutable_table_entry();
  ir_table_entry->set_table_name("ipv4_multicast_table");
  auto* vrf_match = ir_table_entry->add_matches();
  vrf_match->set_name("vrf_id");
  vrf_match->mutable_exact()->set_str(vrf_id);
  auto* dst_addr = ir_table_entry->add_matches();
  dst_addr->set_name("ipv4_dst");
  dst_addr->mutable_exact()->set_ipv4(addr);
  auto* action = ir_table_entry->mutable_action();
  action->set_name("set_multicast_group_id");
  auto* param = action->add_params();
  param->set_name("multicast_group_id");
  param->mutable_value()->set_hex_str(absl::StrFormat("0x%04x", group_id));

  return pdpi::IrUpdateToPi(ir_p4_info, ir_update);
}

absl::StatusOr<p4::v1::Update> Ipv6MulticastRouteUpdate(
    const pdpi::IrP4Info& ir_p4_info, p4::v1::Update::Type type,
    const std::string& vrf_id, const std::string& addr, int32_t group_id) {
  pdpi::IrUpdate ir_update;
  ir_update.set_type(type);
  pdpi::IrTableEntry* ir_table_entry =
      ir_update.mutable_entity()->mutable_table_entry();
  ir_table_entry->set_table_name("ipv6_multicast_table");
  auto* vrf_match = ir_table_entry->add_matches();
  vrf_match->set_name("vrf_id");
  vrf_match->mutable_exact()->set_str(vrf_id);
  auto* dst_addr = ir_table_entry->add_matches();
  dst_addr->set_name("ipv6_dst");
  dst_addr->mutable_exact()->set_ipv6(addr);
  auto* action = ir_table_entry->mutable_action();
  action->set_name("set_multicast_group_id");
  auto* param = action->add_params();
  param->set_name("multicast_group_id");
  param->mutable_value()->set_hex_str(absl::StrFormat("0x%04x", group_id));

  return pdpi::IrUpdateToPi(ir_p4_info, ir_update);
}

absl::StatusOr<p4::v1::Update> NeighborTableUpdate(
    const pdpi::IrP4Info& ir_p4_info, p4::v1::Update::Type type,
    absl::string_view router_interface_id, absl::string_view neighbor_id,
    absl::string_view dst_mac) {
  pdpi::IrUpdate ir_update;
  RETURN_IF_ERROR(gutil::ReadProtoFromString(
      absl::Substitute(R"pb(
                         type: $0
                         entity {
                           table_entry {
                             table_name: "neighbor_table"
                             matches {
                               name: "router_interface_id"
                               exact { str: "$1" }
                             }
                             matches {
                               name: "neighbor_id"
                               exact { ipv6: "$2" }
                             }
                             action {
                               name: "set_dst_mac"
                               params {
                                 name: "dst_mac"
                                 value { mac: "$3" }
                               }
                             }
                           }
                         }
                       )pb",
                       type, router_interface_id, neighbor_id, dst_mac),
      &ir_update))
      << "invalid pdpi::IrUpdate string.";
  return pdpi::IrUpdateToPi(ir_p4_info, ir_update);
}

absl::StatusOr<p4::v1::Update> NexthopTableUpdate(
    const pdpi::IrP4Info& ir_p4_info, p4::v1::Update::Type type,
    absl::string_view nexthop_id, absl::string_view router_interface_id,
    absl::string_view neighbor_id) {
  pdpi::IrUpdate ir_update;
  RETURN_IF_ERROR(gutil::ReadProtoFromString(
      absl::Substitute(R"pb(
                         type: $0
                         entity {
                           table_entry {
                             table_name: "nexthop_table"
                             matches {
                               name: "nexthop_id"
                               exact { str: "$1" }
                             }
                             action {
                               name: "set_ip_nexthop"
                               params {
                                 name: "router_interface_id"
                                 value { str: "$2" }
                               }
                               params {
                                 name: "neighbor_id"
                                 value { ipv6: "$3" }
                               }
                             }
                           }
                         }
                       )pb",
                       type, nexthop_id, router_interface_id, neighbor_id),
      &ir_update))
      << "invalid pdpi::IrUpdate string.";
  return pdpi::IrUpdateToPi(ir_p4_info, ir_update);
}

absl::StatusOr<p4::v1::Update> NexthopTunnelTableUpdate(
    const pdpi::IrP4Info& ir_p4_info, p4::v1::Update::Type type,
    absl::string_view nexthop_id, absl::string_view tunnel_id) {
  pdpi::IrUpdate ir_update;
  RETURN_IF_ERROR(gutil::ReadProtoFromString(
      absl::Substitute(R"pb(
                         type: $0
                         entity {
                           table_entry {
                             table_name: "nexthop_table"
                             matches {
                               name: "nexthop_id"
                               exact { str: "$1" }
                             }
                             action {
                               name: "set_p2p_tunnel_encap_nexthop"
                               params {
                                 name: "tunnel_id"
                                 value { str: "$2" }
                               }
                             }
                           }
                         }
                       )pb",
                       type, nexthop_id, tunnel_id),
      &ir_update))
      << "invalid pdpi::IrUpdate string.";
  return pdpi::IrUpdateToPi(ir_p4_info, ir_update);
}

absl::StatusOr<p4::v1::Update> TunnelTableUpdate(
    const pdpi::IrP4Info& ir_p4_info, p4::v1::Update::Type type,
    absl::string_view tunnel_id, absl::string_view encap_dst_ip,
    absl::string_view encap_src_ip, absl::string_view router_interface_id) {
  pdpi::IrUpdate ir_update;
  RETURN_IF_ERROR(gutil::ReadProtoFromString(
      absl::Substitute(R"pb(
                         type: $0
                         entity {
                           table_entry {
                             table_name: "tunnel_table"
                             matches {
                               name: "tunnel_id"
                               exact { str: "$1" }
                             }
                             action {
                               name: "mark_for_p2p_tunnel_encap"
                               params {
                                 name: "encap_dst_ip"
                                 value { ipv6: "$2" }
                               }
                               params {
                                 name: "encap_src_ip"
                                 value { ipv6: "$3" }
                               }
                               params {
                                 name: "router_interface_id"
                                 value { str: "$4" }
                               }
                             }
                           }
                         }
                       )pb",
                       type, tunnel_id, encap_dst_ip, encap_src_ip,
                       router_interface_id),
      &ir_update))
      << "invalid pdpi::IrUpdate string.";
  return pdpi::IrUpdateToPi(ir_p4_info, ir_update);
}

absl::StatusOr<p4::v1::Update> VrfTableUpdate(const pdpi::IrP4Info& ir_p4_info,
                                              p4::v1::Update::Type type,
                                              absl::string_view vrf_id) {
  if (vrf_id.empty()) {
    return absl::InvalidArgumentError(
        "Empty vrf id is reserved for default vrf.");
  }
  pdpi::IrUpdate ir_update;
  ir_update.set_type(type);
  ASSIGN_OR_RETURN(
      pdpi::IrEntities ir_entities,
      sai::EntryBuilder().AddVrfEntry(vrf_id).GetDedupedIrEntities(ir_p4_info));
  if (ir_entities.entities_size() != 1) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Expected exactly one vrf entry, got "
           << ir_entities.entities_size();
  }
  *ir_update.mutable_entity() = std::move(ir_entities.entities(0)); 
  return pdpi::IrUpdateToPi(ir_p4_info, ir_update);
}

absl::StatusOr<p4::v1::Update> Ipv4TableUpdate(
    const pdpi::IrP4Info& ir_p4_info, p4::v1::Update::Type type,
    const IpTableOptions& ip_options) {
  return IpTableUpdate(ir_p4_info, type, pdpi::IPV4, ip_options);
}

absl::StatusOr<p4::v1::Update> Ipv6TableUpdate(
    const pdpi::IrP4Info& ir_p4_info, p4::v1::Update::Type type,
    const IpTableOptions& ip_options) {
  return IpTableUpdate(ir_p4_info, type, pdpi::IPV6, ip_options);
}

absl::StatusOr<p4::v1::Update> L3AdmitTableUpdate(
    const pdpi::IrP4Info& ir_p4_info, p4::v1::Update::Type type,
    const L3AdmitOptions& options) {
  pdpi::IrUpdate ir_update;
  ir_update.set_type(type);
  pdpi::IrTableEntry* ir_table_entry =
      ir_update.mutable_entity()->mutable_table_entry();
  ir_table_entry->set_table_name("l3_admit_table");

  // Always set the priority because the DST mac is a ternary value.
  ir_table_entry->set_priority(options.priority);

  // Always set the DST mac.
  auto* dst_mac = ir_table_entry->add_matches();
  dst_mac->set_name("dst_mac");
  dst_mac->mutable_ternary()->mutable_value()->set_mac(options.dst_mac.first);
  dst_mac->mutable_ternary()->mutable_mask()->set_mac(options.dst_mac.second);

  // Only set the port if it is passed.
  if (options.in_port.has_value()) {
    auto* in_port = ir_table_entry->add_matches();
    in_port->set_name("in_port");
    in_port->mutable_optional()->mutable_value()->set_str(*options.in_port);
  }

  // Always set the action to "admit_to_l3"
  ir_table_entry->mutable_action()->set_name("admit_to_l3");

  return pdpi::IrUpdateToPi(ir_p4_info, ir_update);
}

absl::StatusOr<p4::v1::Update> L3AdmitAllTableUpdate(
    const pdpi::IrP4Info& ir_p4_info, p4::v1::Update::Type type) {
  pdpi::IrUpdate ir_update;
  ir_update.set_type(type);
  ASSIGN_OR_RETURN(pdpi::IrEntities ir_entities,
                   sai::EntryBuilder()
                       .AddEntryAdmittingAllPacketsToL3()
                       .GetDedupedIrEntities(ir_p4_info));
  if (ir_entities.entities_size() != 1) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Expected exactly one l3_admit_all entry, got "
           << ir_entities.entities_size();
  }
  *ir_update.mutable_entity() = std::move(ir_entities.entities(0)); 
  return pdpi::IrUpdateToPi(ir_p4_info, ir_update);
}

absl::StatusOr<p4::v1::Update> WcmpGroupTableUpdate(
    const pdpi::IrP4Info& ir_p4_info, p4::v1::Update::Type type,
    absl::string_view wcmp_group_id, const std::vector<WcmpAction>& actions) {
  pdpi::IrUpdate ir_update;
  RETURN_IF_ERROR(gutil::ReadProtoFromString(
      absl::Substitute(R"pb(
                         type: $0
                         entity {
                           table_entry {
                             table_name: "wcmp_group_table"
                             matches {
                               name: "wcmp_group_id"
                               exact { str: "$1" }
                             }
                           }
                         }
                       )pb",
                       type, wcmp_group_id),
      &ir_update))
      << "invalid pdpi::IrUpdate string.";

  pdpi::IrActionSet* action_set =
      ir_update.mutable_entity()->mutable_table_entry()->mutable_action_set();
  for (const auto& action_data : actions) {
    // Every action in the set should have a weight.
    auto* action = action_set->add_actions();
    action->set_weight(action_data.weight);

    // We always assume a set_nexthop_id action.
    action->mutable_action()->set_name("set_nexthop_id");
    auto* action_param = action->mutable_action()->add_params();
    action_param->set_name("nexthop_id");
    *action_param->mutable_value()->mutable_str() = action_data.nexthop_id;

    // Only set the watch_port if it's set by the user.
    if (action_data.watch_port.has_value()) {
      action->set_watch_port(action_data.watch_port.value());
    }
  }

  return pdpi::IrUpdateToPi(ir_p4_info, ir_update);
}

}  // namespace pins
