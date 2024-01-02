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

#include "sai_p4/instantiations/google/test_tools/test_entries.h"

#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "absl/types/span.h"
#include "glog/logging.h"
#include "gutil/proto.h"
#include "gutil/proto_ordering.h"
#include "gutil/status.h"
#include "gutil/testing.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/netaddr/ipv4_address.h"
#include "p4_pdpi/netaddr/ipv6_address.h"
#include "p4_pdpi/netaddr/mac_address.h"
#include "p4_pdpi/pd.h"
#include "p4_pdpi/string_encodings/hex_string.h"
#include "p4_pdpi/translation_options.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"

namespace sai {
namespace {

bool AllRewritesEnabled(const NexthopRewriteOptions& rewrite_options) {
  return !rewrite_options.disable_decrement_ttl &&
         rewrite_options.src_mac_rewrite.has_value() &&
         rewrite_options.dst_mac_rewrite.has_value() &&
         !rewrite_options.disable_vlan_rewrite;
}

std::string BoolToHexString(bool value) { return value ? "0x1" : "0x0"; }

}  // namespace

// -- EntryBuilder --------------------------------------------------------

const EntryBuilder& EntryBuilder::LogPdEntries() const {
  LOG(INFO) << entries_.DebugString();
  return *this;
}

EntryBuilder& EntryBuilder::LogPdEntries() {
  LOG(INFO) << entries_.DebugString();
  return *this;
}

absl::StatusOr<std::vector<p4::v1::Entity>> EntryBuilder::GetDedupedPiEntities(
    const pdpi::IrP4Info& ir_p4info, bool allow_unsupported) const {
  ASSIGN_OR_RETURN(pdpi::IrEntities ir_entities,
                   GetDedupedIrEntities(ir_p4info, allow_unsupported));
  return pdpi::IrEntitiesToPi(
      ir_p4info, ir_entities,
      pdpi::TranslationOptions{.allow_unsupported = allow_unsupported});
}

absl::StatusOr<pdpi::IrEntities> EntryBuilder::GetDedupedIrEntities(
    const pdpi::IrP4Info& ir_p4info, bool allow_unsupported) const {
  ASSIGN_OR_RETURN(
      pdpi::IrEntities ir_entities,
      pdpi::PdTableEntriesToIrEntities(
          ir_p4info, entries_,
          pdpi::TranslationOptions{.allow_unsupported = allow_unsupported}));
  gutil::InefficientProtoSortAndDedup(*ir_entities.mutable_entities());
  return ir_entities;
}

EntryBuilder& EntryBuilder::AddVrfEntry(absl::string_view vrf) {
  sai::TableEntry& entry = *entries_.add_entries();
  entry = gutil::ParseProtoOrDie<sai::TableEntry>(R"pb(
    vrf_table_entry {
      match { vrf_id: "TBD" }
      action { no_action {} }
    }
  )pb");
  entry.mutable_vrf_table_entry()->mutable_match()->set_vrf_id(
      // TODO: Pass string_view directly once proto supports it.
      std::string(vrf));
  return *this;
}

EntryBuilder& EntryBuilder::AddEntryAdmittingAllPacketsToL3() {
  *entries_.add_entries() = gutil::ParseProtoOrDie<sai::TableEntry>(R"pb(
    l3_admit_table_entry {
      match {}  # Wildcard.
      action { admit_to_l3 {} }
      priority: 1
    }
  )pb");
  return *this;
}

EntryBuilder& EntryBuilder::AddEntryPuntingAllPackets(PuntAction action) {
  sai::TableEntry& entry = *entries_.add_entries();
  entry = gutil::ParseProtoOrDie<sai::TableEntry>(
      R"pb(
        acl_ingress_table_entry {
          match {}  # Wildcard match
          priority: 1
        }
      )pb");
  auto& acl_action = *entry.mutable_acl_ingress_table_entry()->mutable_action();
  switch (action) {
    case PuntAction::kTrap:
      acl_action.mutable_acl_trap()->set_qos_queue("0x7");
      return *this;
    case PuntAction::kCopy:
      acl_action.mutable_acl_copy()->set_qos_queue("0x7");
      return *this;
  }
  LOG(FATAL) << "invalid punt action: " << static_cast<int>(action);
}

EntryBuilder& EntryBuilder::AddDefaultRouteForwardingAllPacketsToGivenPort(
    absl::string_view egress_port, IpVersion ip_version, absl::string_view vrf,
    const NexthopRewriteOptions& nexthop_rewrite_options,
    std::optional<absl::string_view> vlan_hexstr) {
  const std::string kNexthopId =
      absl::StrFormat("nexthop(%s, %s)", egress_port, vrf);

  if (ip_version == IpVersion::kIpv4 || ip_version == IpVersion::kIpv4And6) {
    sai::TableEntry& entry = *entries_.add_entries();
    entry = gutil::ParseProtoOrDie<sai::TableEntry>(R"pb(
      ipv4_table_entry {
        # IP match field omitted so this entry serves as the default route.
        match { vrf_id: "TBD" }
        action { set_nexthop_id { nexthop_id: "nexthop" } }
      }
    )pb");
    entry.mutable_ipv4_table_entry()->mutable_match()->set_vrf_id(
        // TODO: Pass string_view directly once proto supports it.
        std::string(vrf));
    entry.mutable_ipv4_table_entry()
        ->mutable_action()
        ->mutable_set_nexthop_id()
        ->set_nexthop_id(kNexthopId);
  }
  if (ip_version == IpVersion::kIpv6 || ip_version == IpVersion::kIpv4And6) {
    sai::TableEntry& entry = *entries_.add_entries();
    entry = gutil::ParseProtoOrDie<sai::TableEntry>(R"pb(
      ipv6_table_entry {
        # IP match field omitted so this entry serves as the default route.
        match { vrf_id: "TBD" }
        action { set_nexthop_id { nexthop_id: "nexthop" } }
      }
    )pb");
    entry.mutable_ipv6_table_entry()->mutable_match()->set_vrf_id(
        // TODO: Pass string_view directly once proto supports it.
        std::string(vrf));
    entry.mutable_ipv6_table_entry()
        ->mutable_action()
        ->mutable_set_nexthop_id()
        ->set_nexthop_id(kNexthopId);
  }

  return AddNexthopRifNeighborEntries(kNexthopId, egress_port,
                                      nexthop_rewrite_options, vlan_hexstr);
}

EntryBuilder& EntryBuilder::AddEntriesForwardingIpPacketsToGivenPort(
    absl::string_view egress_port, IpVersion ip_version,
    NexthopRewriteOptions rewrite_options) {
  // Create router interface entry.
  sai::RouterInterfaceTableEntry& rif_entry =
      *entries_.add_entries()->mutable_router_interface_table_entry();
  const netaddr::MacAddress src_mac =
      rewrite_options.src_mac_rewrite.value_or(netaddr::MacAddress::AllZeros());
  const std::string rif_id = absl::StrCat(egress_port, "/", src_mac.ToString());
  rif_entry.mutable_match()->set_router_interface_id(rif_id);
  auto& rif_action =
      *rif_entry.mutable_action()->mutable_set_port_and_src_mac();
  // TODO: Pass string_view directly once proto supports it.
  rif_action.set_port(std::string(egress_port));
  rif_action.set_src_mac(src_mac.ToString());

  // Create neighbor table entry.
  sai::NeighborTableEntry& neighbor_entry =
      *entries_.add_entries()->mutable_neighbor_table_entry();
  const netaddr::MacAddress dst_mac =
      rewrite_options.dst_mac_rewrite.value_or(netaddr::MacAddress::AllZeros());
  const std::string neighbor_id = dst_mac.ToLinkLocalIpv6Address().ToString();
  neighbor_entry.mutable_match()->set_router_interface_id(rif_id);
  neighbor_entry.mutable_match()->set_neighbor_id(neighbor_id);
  rif_entry.mutable_match()->set_router_interface_id(rif_id);
  neighbor_entry.mutable_action()->mutable_set_dst_mac()->set_dst_mac(
      dst_mac.ToString());

  // Create Nexthop entry based on `rewrite_options`
  sai::NexthopTableEntry& nexthop_entry =
      *entries_.add_entries()->mutable_nexthop_table_entry();
  // Ideally we would use an ID that is unique for the RIF & neighbor, but
  // the ID ends up being longer than BMv2 can support.
  const std::string nexthop_id = rif_id;
  // const std::string nexthop_id = absl::StrCat(rif_id, "/", neighbor_id);
  nexthop_entry.mutable_match()->set_nexthop_id(nexthop_id);

  if (AllRewritesEnabled(rewrite_options)) {
    SetIpNexthopAction& action =
        *nexthop_entry.mutable_action()->mutable_set_ip_nexthop();
    action.set_router_interface_id(rif_id);
    action.set_neighbor_id(neighbor_id);
  } else {
    SetIpNexthopAndDisableRewritesAction& action =
        *nexthop_entry.mutable_action()
             ->mutable_set_ip_nexthop_and_disable_rewrites();
    action.set_router_interface_id(rif_id);
    action.set_neighbor_id(neighbor_id);
    action.set_disable_decrement_ttl(
        BoolToHexString(rewrite_options.disable_decrement_ttl));
    action.set_disable_src_mac_rewrite(
        BoolToHexString(!rewrite_options.src_mac_rewrite.has_value()));
    action.set_disable_dst_mac_rewrite(
        BoolToHexString(!rewrite_options.dst_mac_rewrite.has_value()));
    action.set_disable_vlan_rewrite(
        BoolToHexString(rewrite_options.disable_vlan_rewrite));
  }

  const std::string vrf_id = "vrf";

  // Add IPv4 default route.
  if (ip_version == IpVersion::kIpv4 || ip_version == IpVersion::kIpv4And6) {
    auto& ipv4_entry = *entries_.add_entries()->mutable_ipv4_table_entry();
    ipv4_entry.mutable_match()->set_vrf_id(vrf_id);
    ipv4_entry.mutable_action()->mutable_set_nexthop_id()->set_nexthop_id(
        nexthop_id);
  }

  // Add IPv6 default route.
  if (ip_version == IpVersion::kIpv6 || ip_version == IpVersion::kIpv4And6) {
    auto& ipv6_entry = *entries_.add_entries()->mutable_ipv6_table_entry();
    ipv6_entry.mutable_match()->set_vrf_id(vrf_id);
    ipv6_entry.mutable_action()->mutable_set_nexthop_id()->set_nexthop_id(
        nexthop_id);
  }

  return AddEntryAdmittingAllPacketsToL3()
      .AddVrfEntry(vrf_id)
      .AddPreIngressAclEntryAssigningVrfForGivenIpType(vrf_id, ip_version);
}

EntryBuilder& EntryBuilder::AddEntryPuntingPacketsWithTtlZeroAndOne() {
  *entries_.add_entries() = (gutil::ParseProtoOrDie<sai::TableEntry>(R"pb(
    acl_ingress_table_entry {
      match {
        is_ip { value: "0x1" }
        ttl { value: "0x00" mask: "0xfe" }
      }
      action { acl_trap { qos_queue: "queue" } }
      priority: 1
    }
  )pb"));
  return *this;
}

EntryBuilder&
EntryBuilder::AddEntriesForwardingIpPacketsToGivenMulticastGroup(
    int multicast_group_id) {
  LOG(FATAL)  // Crash ok
      << "TODO: implement once SAI P4 supports it";
  AddEntryAdmittingAllPacketsToL3();
  const std::string kVrf =
      absl::StrFormat("vrf-for-multicast-group-%d", multicast_group_id);
  AddVrfEntry(kVrf);
  AddPreIngressAclEntryAssigningVrfForGivenIpType(kVrf, IpVersion::kIpv4And6);
  // AddDefaultRouteForwardingAllPacketsToGivenMulticastGroup(
  //     multicast_group_id, IpVersion::kIpv4And6, kVrf);
  return *this;
}

EntryBuilder& EntryBuilder::AddPreIngressAclEntryAssigningVrfForGivenIpType(
    absl::string_view vrf, IpVersion ip_version) {
  sai::TableEntry& entry = *entries_.add_entries();
  entry = gutil::ParseProtoOrDie<sai::TableEntry>(R"pb(
    acl_pre_ingress_table_entry {
      match {}
      action { set_vrf { vrf_id: "TBD" } }
      priority: 1
    }
  )pb");
  entry.mutable_acl_pre_ingress_table_entry()
      ->mutable_action()
      ->mutable_set_vrf()
      // TODO: Pass string_view directly once proto supports it.
      ->set_vrf_id(std::string(vrf));
  auto& match = *entry.mutable_acl_pre_ingress_table_entry()->mutable_match();
  switch (ip_version) {
    case IpVersion::kIpv4:
      match.mutable_is_ipv4()->set_value("0x1");
      return *this;
    case IpVersion::kIpv6:
      match.mutable_is_ipv6()->set_value("0x1");
      return *this;
    case IpVersion::kIpv4And6:
      match.mutable_is_ip()->set_value("0x1");
      return *this;
  }
  LOG(FATAL)  // Crash ok: test-only library.
      << "invalid ip version: " << static_cast<int>(ip_version);
}

EntryBuilder& EntryBuilder::AddEntryDecappingAllIpInIpv6PacketsAndSettingVrf(
    absl::string_view vrf) {
  sai::TableEntry& entry = *entries_.add_entries();
  entry = gutil::ParseProtoOrDie<sai::TableEntry>(R"pb(
    ipv6_tunnel_termination_table_entry {
      match {}  # Wildcard match
      action { mark_for_tunnel_decap_and_set_vrf { vrf_id: "" } }
      priority: 1
    }
  )pb");
  entry.mutable_ipv6_tunnel_termination_table_entry()
      ->mutable_action()
      ->mutable_mark_for_tunnel_decap_and_set_vrf()
      // TODO: Pass string_view directly once proto supports it.
      ->set_vrf_id(std::string(vrf));
  return *this;
}

EntryBuilder& EntryBuilder::AddMulticastGroupEntry(
    int multicast_group_id, absl::Span<const Replica> replicas) {
  sai::MulticastGroupTableEntry& entry =
      *entries_.add_entries()->mutable_multicast_group_table_entry();
  entry.mutable_match()->set_multicast_group_id(
      pdpi::BitsetToHexString<16>(multicast_group_id));
  for (const Replica& replica : replicas) {
    sai::ReplicateAction::Replica& pd_replica =
        *entry.mutable_action()->mutable_replicate()->add_replicas();
    pd_replica.set_port(replica.egress_port);
    pd_replica.set_instance(pdpi::BitsetToHexString<16>(replica.instance));
  }
  return *this;
}

EntryBuilder& EntryBuilder::AddMulticastGroupEntry(
    int multicast_group_id, absl::Span<const std::string> egress_ports) {
  std::vector<Replica> replicas;
  absl::flat_hash_map<std::string, int> next_instance_by_port;
  for (const std::string& egress_port : egress_ports) {
    replicas.push_back(Replica{
        .egress_port = egress_port,
        .instance = next_instance_by_port[egress_port]++,
    });
  }
  return AddMulticastGroupEntry(multicast_group_id, replicas);
}

EntryBuilder& EntryBuilder::AddMulticastRouterInterfaceEntry(
    const MulticastRouterInterfaceTableEntry& entry) {
  sai::MulticastRouterInterfaceTableEntry& pd_entry =
      *entries_.add_entries()->mutable_multicast_router_interface_table_entry();
  auto& match = *pd_entry.mutable_match();
  match.set_multicast_replica_port(entry.multicast_replica_port);
  match.set_multicast_replica_instance(
      pdpi::BitsetToHexString<16>(entry.multicast_replica_instance));
  auto& action = *pd_entry.mutable_action()->mutable_set_multicast_src_mac();
  action.set_src_mac(entry.src_mac.ToString());
  return *this;
}

EntryBuilder& EntryBuilder::AddMulticastRoute(
    absl::string_view vrf, const netaddr::Ipv4Address& dst_ip,
    int multicast_group_id) {
  sai::Ipv4MulticastTableEntry& entry =
      *entries_.add_entries()->mutable_ipv4_multicast_table_entry();
  entry.mutable_match()->set_vrf_id(vrf);
  entry.mutable_match()->set_ipv4_dst(dst_ip.ToString());
  entry.mutable_action()
      ->mutable_set_multicast_group_id()
      ->set_multicast_group_id(pdpi::BitsetToHexString<16>(multicast_group_id));
  return *this;
}

EntryBuilder& EntryBuilder::AddMulticastRoute(
    absl::string_view vrf, const netaddr::Ipv6Address& dst_ip,
    int multicast_group_id) {
  sai::Ipv6MulticastTableEntry& entry =
      *entries_.add_entries()->mutable_ipv6_multicast_table_entry();
  entry.mutable_match()->set_vrf_id(vrf);
  entry.mutable_match()->set_ipv6_dst(dst_ip.ToString());
  entry.mutable_action()
      ->mutable_set_multicast_group_id()
      ->set_multicast_group_id(pdpi::BitsetToHexString<16>(multicast_group_id));
  return *this;
}

EntryBuilder& EntryBuilder::AddIngressAclDroppingAllPackets() {
  *entries_.add_entries() = gutil::ParseProtoOrDie<sai::TableEntry>(R"pb(
    acl_ingress_table_entry {
      match {}  # Wildcard match.
      action { acl_drop {} }
      priority: 1  # Maximum priority.
    }
  )pb");
  return *this;
}
EntryBuilder& EntryBuilder::AddDisableVlanChecksEntry() {
  *entries_.add_entries() = gutil::ParseProtoOrDie<sai::TableEntry>(R"pb(
    disable_vlan_checks_table_entry {
      action { disable_vlan_checks {} }
      priority: 1
    }
  )pb");
  return *this;
}

EntryBuilder& EntryBuilder::AddEntrySettingVrfBasedOnVlanId(
    absl::string_view vlan_id_hexstr, absl::string_view vrf) {
  sai::AclPreIngressTableEntry& entry =
      *entries_.add_entries()->mutable_acl_pre_ingress_table_entry();
  entry.mutable_match()->mutable_vlan_id()->set_value(vlan_id_hexstr);
  entry.mutable_match()->mutable_vlan_id()->set_mask("0xfff");
  entry.mutable_action()->mutable_set_vrf()->set_vrf_id(vrf);
  entry.set_priority(1);
  return *this;
}

EntryBuilder& EntryBuilder::AddEntrySettingVrfForAllPackets(
    absl::string_view vrf) {
  sai::AclPreIngressTableEntry& entry =
      *entries_.add_entries()->mutable_acl_pre_ingress_table_entry();
  entry.mutable_action()->mutable_set_vrf()->set_vrf_id(vrf);
  entry.set_priority(1);
  return *this;
}

EntryBuilder& EntryBuilder::AddEntrySettingVlanIdInPreIngress(
    absl::string_view set_vlan_id_hexstr,
    std::optional<absl::string_view> match_vlan_id_hexstr) {
  sai::AclPreIngressVlanTableEntry& entry =
      *entries_.add_entries()->mutable_acl_pre_ingress_vlan_table_entry();
  if (match_vlan_id_hexstr.has_value()) {
    entry.mutable_match()->mutable_vlan_id()->set_value(*match_vlan_id_hexstr);
    entry.mutable_match()->mutable_vlan_id()->set_mask("0xfff");
  }
  entry.mutable_action()->mutable_set_outer_vlan_id()->set_vlan_id(
      set_vlan_id_hexstr);
  entry.set_priority(1);

  return *this;
}

EntryBuilder& EntryBuilder::AddNexthopRifNeighborEntries(
    absl::string_view nexthop_id, absl::string_view egress_port,
    const NexthopRewriteOptions& nexthop_rewrite_options,
    std::optional<absl::string_view> vlan_hexstr) {
  const std::string kRifId = absl::StrFormat(
      "rif(port=%s, vlan=%s)", egress_port, vlan_hexstr.value_or("none"));
  {
    sai::NexthopTableEntry& nexthop_entry =
        *entries_.add_entries()->mutable_nexthop_table_entry();
    nexthop_entry.mutable_match()->set_nexthop_id(nexthop_id);
    if (AllRewritesEnabled(nexthop_rewrite_options)) {
      sai::SetIpNexthopAction& action =
          *nexthop_entry.mutable_action()->mutable_set_ip_nexthop();
      action.set_router_interface_id(kRifId);
      action.set_neighbor_id("fe80::2");
    } else {
      sai::SetIpNexthopAndDisableRewritesAction& action =
          *nexthop_entry.mutable_action()
               ->mutable_set_ip_nexthop_and_disable_rewrites();
      action.set_router_interface_id(kRifId);
      action.set_neighbor_id("fe80::2");
      action.set_disable_decrement_ttl(
          BoolToHexString(nexthop_rewrite_options.disable_decrement_ttl));
      action.set_disable_src_mac_rewrite(BoolToHexString(
          !nexthop_rewrite_options.src_mac_rewrite.has_value()));
      action.set_disable_dst_mac_rewrite(BoolToHexString(
          !nexthop_rewrite_options.dst_mac_rewrite.has_value()));
      action.set_disable_vlan_rewrite(
          BoolToHexString(nexthop_rewrite_options.disable_vlan_rewrite));
    }
  }
  {
    sai::TableEntry& entry = *entries_.add_entries();
    entry = gutil::ParseProtoOrDie<sai::TableEntry>(R"pb(
      neighbor_table_entry {
        match { router_interface_id: "rif" neighbor_id: "fe80::2" }
        action { set_dst_mac { dst_mac: "02:03:04:05:06:07" } }
      }
    )pb");
    entry.mutable_neighbor_table_entry()
        ->mutable_match()
        ->set_router_interface_id(kRifId);
  }
  {
    sai::RouterInterfaceTableEntry& entry =
        *entries_.add_entries()->mutable_router_interface_table_entry();
    entry.mutable_match()->set_router_interface_id(kRifId);
    if (vlan_hexstr.has_value()) {
      auto& action =
          *entry.mutable_action()->mutable_set_port_and_src_mac_and_vlan_id();
      action.set_vlan_id(*vlan_hexstr);
      action.set_src_mac("00:01:02:03:04:05");
      action.set_port(egress_port);
    } else {
      auto& action = *entry.mutable_action()->mutable_set_port_and_src_mac();
      action.set_src_mac("00:01:02:03:04:05");
      action.set_port(egress_port);
    }
  }

  return *this;
}

EntryBuilder& EntryBuilder::AddIngressAclEntryRedirectingToNexthop(
    absl::string_view nexthop_id,
    std::optional<absl::string_view> in_port_match) {
  sai::AclIngressMirrorAndRedirectTableEntry& entry =
      *entries_.add_entries()
           ->mutable_acl_ingress_mirror_and_redirect_table_entry();
  if (in_port_match.has_value()) {
    entry.mutable_match()->mutable_in_port()->set_value(*in_port_match);
  }
  entry.mutable_action()->mutable_redirect_to_nexthop()->set_nexthop_id(
      nexthop_id);
  entry.set_priority(1);

  return *this;
}

EntryBuilder& EntryBuilder::AddIngressAclEntryRedirectingToMulticastGroup(
    int multicast_group_id, const MirrorAndRedirectMatchFields& match_fields) {
  sai::AclIngressMirrorAndRedirectTableEntry& entry =
      *entries_.add_entries()
           ->mutable_acl_ingress_mirror_and_redirect_table_entry();
  if (match_fields.in_port.has_value()) {
    entry.mutable_match()->mutable_in_port()->set_value(*match_fields.in_port);
  }
  if (match_fields.ipmc_table_hit.has_value()) {
    entry.mutable_match()->mutable_ipmc_table_hit()->set_value(
        BoolToHexString(*match_fields.ipmc_table_hit));
  }
  entry.mutable_action()
      ->mutable_redirect_to_ipmc_group()
      ->set_multicast_group_id(pdpi::BitsetToHexString<16>(multicast_group_id));
  entry.set_priority(1);

  return *this;
}

EntryBuilder& EntryBuilder::AddMirrorSessionTableEntry(
    const MirrorSessionParams& params) {
  sai::TableEntry pd_entry;
  sai::MirrorSessionTableEntry& mirror_session_entry =
      *pd_entry.mutable_mirror_session_table_entry();
  mirror_session_entry.mutable_match()->set_mirror_session_id(
      params.mirror_session_id);
  sai::MirrorWithIpfixEncapsulationAction& action =
      *mirror_session_entry.mutable_action()
           ->mutable_mirror_with_ipfix_encapsulation();
  action.set_monitor_port(params.mirror_egress_port);
  // TODO: Fill in IPFIX params in table entry's action.
  *entries_.add_entries() = std::move(pd_entry);

  return *this;
}

EntryBuilder& EntryBuilder::AddMarkToMirrorAclEntry(
    const MarkToMirrorParams& params) {
  sai::TableEntry pd_entry;
  sai::AclIngressMirrorAndRedirectTableEntry& acl_entry =
      *pd_entry.mutable_acl_ingress_mirror_and_redirect_table_entry();
  acl_entry.mutable_match()->mutable_in_port()->set_value(params.ingress_port);
  acl_entry.mutable_action()->mutable_acl_mirror()->set_mirror_session_id(
      params.mirror_session_id);
  acl_entry.set_priority(1);
  *entries_.add_entries() = std::move(pd_entry);
  return *this;
}

EntryBuilder& EntryBuilder::AddEgressPortLoopbackEntry(
    absl::string_view out_port) {
  sai::EgressPortLoopbackTableEntry& loopback_entry =
      *entries_.add_entries()->mutable_egress_port_loopback_table_entry();
  loopback_entry.mutable_match()->set_out_port(out_port);
  loopback_entry.mutable_action()->mutable_egress_loopback();

  return *this;
}

}  // namespace sai
