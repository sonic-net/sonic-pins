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
#include <variant>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "absl/types/span.h"
#include "glog/logging.h"
#include "gutil/overload.h"
#include "gutil/proto_ordering.h"
#include "gutil/status.h"
#include "gutil/testing.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/netaddr/ipv4_address.h"
#include "p4_pdpi/netaddr/ipv6_address.h"
#include "p4_pdpi/netaddr/mac_address.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/p4_runtime_session_extras.h"
#include "p4_pdpi/pd.h"
#include "p4_pdpi/string_encodings/hex_string.h"
#include "p4_pdpi/translation_options.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
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
          // We always use the static P4Info when translating from PD to protect
          // against a mismatch between the PD proto and the argument
          // `ir_p4info`.
          sai::GetUnionedIrP4Info(), entries_,
          pdpi::TranslationOptions{.allow_unsupported = allow_unsupported}));
  gutil::InefficientProtoSortAndDedup(*ir_entities.mutable_entities());
  return ir_entities;
}

absl::Status EntryBuilder::InstallDedupedEntities(
    pdpi::P4RuntimeSession& session, bool allow_unsupported) const {
  ASSIGN_OR_RETURN(pdpi::IrP4Info ir_p4info, pdpi::GetIrP4Info(session));
  return InstallDedupedEntities(ir_p4info, session, allow_unsupported);
}

absl::Status EntryBuilder::InstallDedupedEntities(
    const pdpi::IrP4Info& ir_p4info, pdpi::P4RuntimeSession& session,
    bool allow_unsupported) const {
  ASSIGN_OR_RETURN(std::vector<p4::v1::Entity> pi_entities,
                   GetDedupedPiEntities(ir_p4info, allow_unsupported));
  return pdpi::InstallPiEntities(&session, ir_p4info, pi_entities);
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
    const NexthopRewriteOptions& rewrite_options) {
  struct IpForwardingParams ip_forwarding_params;
  if (ip_version == IpVersion::kIpv4) {
    ip_forwarding_params.ipv6_lpm = std::nullopt;
  } else if (ip_version == IpVersion::kIpv6) {
    ip_forwarding_params.ipv4_lpm = std::nullopt;
  }

  return AddL3LpmRouteForwardingUnicastPacketsToGivenPort(
      egress_port, vrf, ip_forwarding_params, rewrite_options);
}

EntryBuilder& EntryBuilder::AddL3LpmRouteForwardingUnicastPacketsToGivenPort(
    absl::string_view egress_port, absl::string_view vrf,
    const IpForwardingParams& ip_forwarding_params,
    const NexthopRewriteOptions& rewrite_options) {
  const std::string nexthop_id =
      absl::StrFormat("nexthop(%s, %s)", egress_port, vrf)
          // Ideally we would use the whole ID, but it may be longer than BMv2
          // can support.
          .substr(0, 31);

  if (ip_forwarding_params.ipv4_lpm.has_value()) {
    AddIpv4EntrySettingNexthopId(nexthop_id, vrf,
                                 ip_forwarding_params.ipv4_lpm.value());
  }
  if (ip_forwarding_params.ipv6_lpm.has_value()) {
    AddIpv6EntrySettingNexthopId(nexthop_id, vrf,
                                 ip_forwarding_params.ipv6_lpm.value());
  }
  return AddNexthopRifNeighborEntries(nexthop_id, egress_port, rewrite_options);
}

EntryBuilder& EntryBuilder::EntryBuilder::AddIpv4EntrySettingNexthopId(
    absl::string_view nexthop_id, absl::string_view vrf,
    const Ipv4Lpm& ipv4_lpm) {
  sai::Ipv4TableEntry& ipv4_entry =
      *entries_.add_entries()->mutable_ipv4_table_entry();
  ipv4_entry.mutable_match()->set_vrf_id(vrf);

  if (!ipv4_lpm.dst_ip.IsAllZeros()) {
    ipv4_entry.mutable_match()->mutable_ipv4_dst()->set_value(
        ipv4_lpm.dst_ip.ToString());
    ipv4_entry.mutable_match()->mutable_ipv4_dst()->set_prefix_length(
        ipv4_lpm.prefix_len);
  }

  ipv4_entry.mutable_action()->mutable_set_nexthop_id()->set_nexthop_id(
      nexthop_id);

  return *this;
}

EntryBuilder& EntryBuilder::AddIpv6EntrySettingNexthopId(
    absl::string_view nexthop_id, absl::string_view vrf,
    const Ipv6Lpm& ipv6_lpm) {
  sai::Ipv6TableEntry& ipv6_entry =
      *entries_.add_entries()->mutable_ipv6_table_entry();
  ipv6_entry.mutable_match()->set_vrf_id(vrf);

  if (!ipv6_lpm.dst_ip.IsAllZeros()) {
    ipv6_entry.mutable_match()->mutable_ipv6_dst()->set_value(
        ipv6_lpm.dst_ip.ToString());
    ipv6_entry.mutable_match()->mutable_ipv6_dst()->set_prefix_length(
        ipv6_lpm.prefix_len);
  }

  ipv6_entry.mutable_action()->mutable_set_nexthop_id()->set_nexthop_id(
      nexthop_id);

  return *this;
}

EntryBuilder& EntryBuilder::AddEntriesForwardingIpPacketsToGivenPort(
    absl::string_view egress_port, IpVersion ip_version,
    const NexthopRewriteOptions& rewrite_options) {
  const std::string vrf_id = "vrf";

  return AddEntryAdmittingAllPacketsToL3()
      .AddVrfEntry(vrf_id)
      .AddPreIngressAclEntryAssigningVrfForGivenIpType(vrf_id, ip_version)
      .AddDefaultRouteForwardingAllPacketsToGivenPort(egress_port, ip_version,
                                                      vrf_id, rewrite_options);
}

EntryBuilder& EntryBuilder::AddEntriesForwardingIpPacketsToGivenPort(
    absl::string_view egress_port,
    const IpForwardingParams& ip_forwarding_params,
    const NexthopRewriteOptions& rewrite_options) {
  const std::string vrf_id = "vrf";

  return AddEntryAdmittingAllPacketsToL3()
      .AddVrfEntry(vrf_id)
      .AddPreIngressAclEntryAssigningVrfForGivenIpType(vrf_id,
                                                       IpVersion::kIpv4And6)
      .AddL3LpmRouteForwardingUnicastPacketsToGivenPort(
          egress_port, vrf_id, ip_forwarding_params, rewrite_options);
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

EntryBuilder& EntryBuilder::AddEntryPuntingPacketsWithDstMac(
    absl::string_view dst_mac, PuntAction action, absl::string_view qos_queue) {
  sai::AclIngressTableEntry& entry =
      *entries_.add_entries()->mutable_acl_ingress_table_entry();
  entry.mutable_match()->mutable_dst_mac()->set_value(dst_mac);
  entry.mutable_match()->mutable_dst_mac()->set_mask(
      netaddr::MacAddress::AllOnes().ToString());
  entry.set_priority(1);
  switch (action) {
    case PuntAction::kTrap:
      entry.mutable_action()->mutable_acl_trap()->set_qos_queue(qos_queue);
      return *this;
    case PuntAction::kCopy:
      entry.mutable_action()->mutable_acl_copy()->set_qos_queue(qos_queue);
  }
  return *this;
}

EntryBuilder& EntryBuilder::AddEntriesForwardingIpPacketsToGivenMulticastGroup(
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

EntryBuilder& EntryBuilder::AddEntryTunnelTerminatingAllIpInIpv6Packets() {
  sai::TableEntry& entry = *entries_.add_entries();
  entry = gutil::ParseProtoOrDie<sai::TableEntry>(R"pb(
    ipv6_tunnel_termination_table_entry {
      match {}  # Wildcard match
      action { tunnel_decap {} }
      priority: 1
    }
  )pb");
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

EntryBuilder& EntryBuilder::AddMrifEntryRewritingSrcMac(
    absl::string_view egress_port, int replica_instance,
    const netaddr::MacAddress& src_mac) {
  sai::MulticastRouterInterfaceTableEntry& pd_entry =
      *entries_.add_entries()->mutable_multicast_router_interface_table_entry();
  auto& match = *pd_entry.mutable_match();
  match.set_multicast_replica_port(egress_port);
  match.set_multicast_replica_instance(
      pdpi::BitsetToHexString<16>(replica_instance));
  auto& action = *pd_entry.mutable_action()->mutable_multicast_set_src_mac();
  action.set_src_mac(src_mac.ToString());
  return *this;
}

EntryBuilder& EntryBuilder::AddMrifEntryRewritingSrcMacAndVlanId(
    absl::string_view egress_port, int replica_instance,
    const netaddr::MacAddress& src_mac, int vlan_id) {
  sai::MulticastRouterInterfaceTableEntry& pd_entry =
      *entries_.add_entries()->mutable_multicast_router_interface_table_entry();
  auto& match = *pd_entry.mutable_match();
  match.set_multicast_replica_port(egress_port);
  match.set_multicast_replica_instance(
      pdpi::BitsetToHexString<16>(replica_instance));
  auto& action =
      *pd_entry.mutable_action()->mutable_multicast_set_src_mac_and_vlan_id();
  action.set_src_mac(src_mac.ToString());
  action.set_vlan_id(pdpi::BitsetToHexString<12>(vlan_id));
  return *this;
}

EntryBuilder& EntryBuilder::AddMrifEntryRewritingSrcMacDstMacAndVlanId(
    absl::string_view egress_port, int replica_instance,
    const netaddr::MacAddress& src_mac, const netaddr::MacAddress& dst_mac,
    int vlan_id) {
  sai::MulticastRouterInterfaceTableEntry& pd_entry =
      *entries_.add_entries()->mutable_multicast_router_interface_table_entry();
  auto& match = *pd_entry.mutable_match();
  match.set_multicast_replica_port(egress_port);
  match.set_multicast_replica_instance(
      pdpi::BitsetToHexString<16>(replica_instance));
  auto& action = *pd_entry.mutable_action()
                      ->mutable_multicast_set_src_mac_and_dst_mac_and_vlan_id();
  action.set_src_mac(src_mac.ToString());
  action.set_dst_mac(dst_mac.ToString());
  action.set_vlan_id(pdpi::BitsetToHexString<12>(vlan_id));
  return *this;
}

EntryBuilder&
EntryBuilder::AddMrifEntryRewritingSrcMacAndPreservingIngressVlanId(
    absl::string_view egress_port, int replica_instance,
    const netaddr::MacAddress& src_mac) {
  sai::MulticastRouterInterfaceTableEntry& pd_entry =
      *entries_.add_entries()->mutable_multicast_router_interface_table_entry();
  auto& match = *pd_entry.mutable_match();
  match.set_multicast_replica_port(egress_port);
  match.set_multicast_replica_instance(
      pdpi::BitsetToHexString<16>(replica_instance));
  auto& action =
      *pd_entry.mutable_action()
           ->mutable_multicast_set_src_mac_and_preserve_ingress_vlan_id();
  action.set_src_mac(src_mac.ToString());
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
      priority: 1
    }
  )pb");
  return *this;
}

EntryBuilder& EntryBuilder::AddEgressAclDroppingIpPackets(
    IpVersion ip_version) {
  if (ip_version == IpVersion::kIpv4 || ip_version == IpVersion::kIpv4And6) {
    *entries_.add_entries() = gutil::ParseProtoOrDie<sai::TableEntry>(R"pb(
      acl_egress_table_entry {
        match { is_ipv4 { value: "0x1" } }
        action { acl_drop {} }
        priority: 1
      }
    )pb");
  }
  if (ip_version == IpVersion::kIpv6 || ip_version == IpVersion::kIpv4And6) {
    *entries_.add_entries() = gutil::ParseProtoOrDie<sai::TableEntry>(R"pb(
      acl_egress_table_entry {
        match { is_ipv6 { value: "0x1" } }
        action { acl_drop {} }
        priority: 1
      }
    )pb");
  }
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

EntryBuilder& EntryBuilder::AddDisableIngressVlanChecksEntry() {
  *entries_.add_entries() = gutil::ParseProtoOrDie<sai::TableEntry>(R"pb(
    disable_ingress_vlan_checks_table_entry {
      action { disable_ingress_vlan_checks {} }
    }
  )pb");
  return *this;
}

EntryBuilder& EntryBuilder::AddDisableEgressVlanChecksEntry() {
  *entries_.add_entries() = gutil::ParseProtoOrDie<sai::TableEntry>(R"pb(
    disable_egress_vlan_checks_table_entry {
      action { disable_egress_vlan_checks {} }
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
    absl::string_view vrf, int priority) {
  sai::AclPreIngressTableEntry& entry =
      *entries_.add_entries()->mutable_acl_pre_ingress_table_entry();
  entry.mutable_action()->mutable_set_vrf()->set_vrf_id(vrf);
  entry.set_priority(priority);
  return *this;
}

EntryBuilder& EntryBuilder::AddEntrySettingVlanIdInPreIngress(
    absl::string_view set_vlan_id_hexstr,
    std::optional<absl::string_view> match_vlan_id_hexstr, int priority) {
  sai::AclPreIngressVlanTableEntry& entry =
      *entries_.add_entries()->mutable_acl_pre_ingress_vlan_table_entry();
  if (match_vlan_id_hexstr.has_value()) {
    entry.mutable_match()->mutable_vlan_id()->set_value(*match_vlan_id_hexstr);
    entry.mutable_match()->mutable_vlan_id()->set_mask("0xfff");
  }
  entry.mutable_action()->mutable_set_outer_vlan_id()->set_vlan_id(
      set_vlan_id_hexstr);
  entry.set_priority(priority);

  return *this;
}

EntryBuilder& EntryBuilder::AddNexthopRifNeighborEntries(
    absl::string_view nexthop_id, absl::string_view egress_port,
    const NexthopRewriteOptions& rewrite_options) {
  // Create router interface entry.
  sai::RouterInterfaceTableEntry& rif_entry =
      *entries_.add_entries()->mutable_router_interface_table_entry();
  // If no SMAC is provided, SMAC rewrite will be disabled for nexthop. In that
  // case, we can use any valid value for RIF's SMAC rewrite, we choose
  // 22:22:22:22:22:22 arbitrarily. Note that value 0 won't be accepted by the switch
  const netaddr::MacAddress src_mac = rewrite_options.src_mac_rewrite.value_or(
      netaddr::MacAddress(0x22, 0x22, 0x22, 0x22, 0x22, 0x22));
  const std::string kRifId =
      absl::StrFormat("rif(%s,%s,%s)", egress_port, src_mac.ToString(),
                      rewrite_options.egress_rif_vlan.value_or("no_vlan"))
          // Ideally we would use the whole ID, but it may be longer than BMv2
          // can support.
          .substr(0, 32);
  rif_entry.mutable_match()->set_router_interface_id(kRifId);
  if (rewrite_options.egress_rif_vlan.has_value()) {
    auto& rif_action =
        *rif_entry.mutable_action()->mutable_set_port_and_src_mac_and_vlan_id();
    rif_action.set_vlan_id(*rewrite_options.egress_rif_vlan);
    // TODO: Pass string_view directly once proto supports it.
    rif_action.set_port(std::string(egress_port));
    rif_action.set_src_mac(src_mac.ToString());
  } else {
    auto& rif_action =
        *rif_entry.mutable_action()->mutable_set_port_and_src_mac();
    // TODO: Pass string_view directly once proto supports it.
    rif_action.set_port(std::string(egress_port));
    rif_action.set_src_mac(src_mac.ToString());
  }

  // Create neighbor table entry.
  sai::NeighborTableEntry& neighbor_entry =
      *entries_.add_entries()->mutable_neighbor_table_entry();
  // If no DST is provided, DMAC rewrite will be disabled for nexthop. In that
  // case, we can use any valid value for RIF's DST rewrite, we choose
  // 22:22:22:22:22:22 arbitrary.
  const netaddr::MacAddress dst_mac = rewrite_options.dst_mac_rewrite.value_or(
      netaddr::MacAddress(0x22, 0x22, 0x22, 0x22, 0x22, 0x22));
  const std::string neighbor_id = dst_mac.ToLinkLocalIpv6Address().ToString();
  neighbor_entry.mutable_match()->set_router_interface_id(kRifId);
  neighbor_entry.mutable_match()->set_neighbor_id(neighbor_id);
  rif_entry.mutable_match()->set_router_interface_id(kRifId);
  neighbor_entry.mutable_action()->mutable_set_dst_mac()->set_dst_mac(
      dst_mac.ToString());

  // Create Nexthop entry based on `rewrite_options`
  sai::NexthopTableEntry& nexthop_entry =
      *entries_.add_entries()->mutable_nexthop_table_entry();
  nexthop_entry.mutable_match()->set_nexthop_id(nexthop_id);

  if (AllRewritesEnabled(rewrite_options)) {
    SetIpNexthopAction& action =
        *nexthop_entry.mutable_action()->mutable_set_ip_nexthop();
    action.set_router_interface_id(kRifId);
    action.set_neighbor_id(neighbor_id);
  } else {
    SetIpNexthopAndDisableRewritesAction& action =
        *nexthop_entry.mutable_action()
             ->mutable_set_ip_nexthop_and_disable_rewrites();
    action.set_router_interface_id(kRifId);
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

  return *this;
}

EntryBuilder& EntryBuilder::AddIngressAclEntryRedirectingToNexthop(
    absl::string_view nexthop_id,
    const MirrorAndRedirectMatchFields& match_fields, int priority) {
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
  if (match_fields.vlan_id.has_value()) {
    entry.mutable_match()->mutable_vlan_id()->set_value(
        pdpi::BitsetToHexString<12>(*match_fields.vlan_id));
    entry.mutable_match()->mutable_vlan_id()->set_mask("0xfff");
  }
  if (match_fields.dst_ip.has_value()) {
    entry.mutable_match()->mutable_dst_ip()->set_value(
        match_fields.dst_ip->value.ToString());
    entry.mutable_match()->mutable_dst_ip()->set_mask(
        match_fields.dst_ip->mask.ToString());
  }
  if (match_fields.is_ipv4.has_value()) {
    entry.mutable_match()->mutable_is_ipv4()->set_value(
        BoolToHexString(*match_fields.is_ipv4));
  }
  if (match_fields.dst_ipv6.has_value()) {
    entry.mutable_match()->mutable_dst_ipv6()->set_value(
        match_fields.dst_ipv6->value.ToString());
    entry.mutable_match()->mutable_dst_ipv6()->set_mask(
        match_fields.dst_ipv6->mask.ToString());
  }
  if (match_fields.is_ipv6.has_value()) {
    entry.mutable_match()->mutable_is_ipv6()->set_value(
        BoolToHexString(*match_fields.is_ipv6));
  }
  entry.mutable_action()->mutable_redirect_to_nexthop()->set_nexthop_id(
      nexthop_id);
  entry.set_priority(priority);

  return *this;
}

EntryBuilder& EntryBuilder::AddIngressAclEntryRedirectingToMulticastGroup(
    int multicast_group_id, const MirrorAndRedirectMatchFields& match_fields) {
  return AddIngressAclMirrorAndRedirectEntry(
      RedirectToIpmcGroup{
          .multicast_group_id = multicast_group_id,
      },
      match_fields);
}

EntryBuilder& EntryBuilder::AddIngressAclMirrorAndRedirectEntry(
    const MirrorAndRedirectAction& action,
    const MirrorAndRedirectMatchFields& match_fields, int priority) {
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
  if (match_fields.vlan_id.has_value()) {
    entry.mutable_match()->mutable_vlan_id()->set_value(
        pdpi::BitsetToHexString<12>(*match_fields.vlan_id));
    entry.mutable_match()->mutable_vlan_id()->set_mask("0xfff");
  }
  if (match_fields.dst_ip.has_value()) {
    entry.mutable_match()->mutable_dst_ip()->set_value(
        match_fields.dst_ip->value.ToString());

    entry.mutable_match()->mutable_dst_ip()->set_mask(
        match_fields.dst_ip->mask.ToString());
  }
  if (match_fields.is_ipv4.has_value()) {
    entry.mutable_match()->mutable_is_ipv4()->set_value(
        BoolToHexString(*match_fields.is_ipv4));
  }
  if (match_fields.dst_ipv6.has_value()) {
    entry.mutable_match()->mutable_dst_ipv6()->set_value(
        match_fields.dst_ipv6->value.ToString());

    entry.mutable_match()->mutable_dst_ipv6()->set_mask(
        match_fields.dst_ipv6->mask.ToString());
  }
  if (match_fields.is_ipv6.has_value()) {
    entry.mutable_match()->mutable_is_ipv6()->set_value(
        BoolToHexString(*match_fields.is_ipv6));
  }
  
  std::visit(
      gutil::Overload{
          [&](const Forward& action) {
            entry.mutable_action()->mutable_acl_forward();
          },
          [&](const RedirectToIpmcGroup& action) {
            entry.mutable_action()
                ->mutable_redirect_to_ipmc_group()
                ->set_multicast_group_id(
                    pdpi::BitsetToHexString<16>(action.multicast_group_id));
          },
          [&](const RedirectToIpmcGroupAndSetCpuQueueAndCancelCopy& action) {
            auto& proto =
                *entry
                     .mutable_action()
                     // NOLINTNEXTLINE
                     ->mutable_redirect_to_ipmc_group_and_set_cpu_queue_and_cancel_copy();
            proto.set_multicast_group_id(
                pdpi::BitsetToHexString<16>(action.multicast_group_id));
            proto.set_cpu_queue(action.cpu_queue);
          },
          [&](const SetCpuQueueAndCancelCopy& action) {
            entry.mutable_action()
                ->mutable_set_cpu_queue_and_cancel_copy()
                ->set_cpu_queue(action.cpu_queue);
          },
      },
      action);

  entry.set_priority(priority);
  return *this;
}

EntryBuilder& EntryBuilder::AddIngressAclEntryRedirectingToPort(
    absl::string_view port, const MirrorAndRedirectMatchFields& match_fields,
    int priority) {
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
  if (match_fields.vlan_id.has_value()) {
    entry.mutable_match()->mutable_vlan_id()->set_value(
        pdpi::BitsetToHexString<12>(*match_fields.vlan_id));
    entry.mutable_match()->mutable_vlan_id()->set_mask("0xfff");
  }
  if (match_fields.dst_ip.has_value()) {
    entry.mutable_match()->mutable_dst_ip()->set_value(
        match_fields.dst_ip->value.ToString());

    entry.mutable_match()->mutable_dst_ip()->set_mask(
        match_fields.dst_ip->mask.ToString());
  }
  if (match_fields.is_ipv4.has_value()) {
    entry.mutable_match()->mutable_is_ipv4()->set_value(
        BoolToHexString(*match_fields.is_ipv4));
  }
  if (match_fields.dst_ipv6.has_value()) {
    entry.mutable_match()->mutable_dst_ipv6()->set_value(
        match_fields.dst_ipv6->value.ToString());

    entry.mutable_match()->mutable_dst_ipv6()->set_mask(
        match_fields.dst_ipv6->mask.ToString());
  }
  if (match_fields.is_ipv6.has_value()) {
    entry.mutable_match()->mutable_is_ipv6()->set_value(
        BoolToHexString(*match_fields.is_ipv6));
  }
  entry.mutable_action()->mutable_redirect_to_port()->set_redirect_port(port);
  entry.set_priority(priority);
  return *this;
}

EntryBuilder& EntryBuilder::AddIngressAclEntryMirroringAndRedirectingToPort(
    absl::string_view port, absl::string_view mirror_session_id,
    const MirrorAndRedirectMatchFields& match_fields, int priority) {
  EntryBuilder::AddIngressAclEntryRedirectingToPort(port, match_fields,
                                                    priority);
  sai::AclIngressMirrorAndRedirectTableEntry& entry =
      *entries_.mutable_entries()
           ->rbegin()
           ->mutable_acl_ingress_mirror_and_redirect_table_entry();
  sai::AclMirrorAndRedirectToPortAction& action =
      *entry.mutable_action()->mutable_acl_mirror_and_redirect_to_port();
  action.set_redirect_port(port);
  action.set_mirror_session_id(mirror_session_id);
  return *this;
}

EntryBuilder& EntryBuilder::AddMirrorSessionTableEntry(
    const MirrorSessionParams& params) {
  sai::TableEntry pd_entry;
  sai::MirrorSessionTableEntry& mirror_session_entry =
      *pd_entry.mutable_mirror_session_table_entry();
  mirror_session_entry.mutable_match()->set_mirror_session_id(
      params.mirror_session_id);
  sai::MirrorWithVlanTagAndIpfixEncapsulationAction& action =
      *mirror_session_entry.mutable_action()
           ->mutable_mirror_with_vlan_tag_and_ipfix_encapsulation();
  action.set_monitor_port(params.monitor_port);
  // monitor_failover_port's effect is not modeled, so use mirror_egress_port
  // as a dummy value to satisfy the action param requirement.
  action.set_monitor_failover_port(params.monitor_port);
  action.set_mirror_encap_src_mac(params.mirror_encap_src_mac);
  action.set_mirror_encap_dst_mac(params.mirror_encap_dst_mac);
  action.set_mirror_encap_vlan_id(params.mirror_encap_vlan_id);
  action.set_mirror_encap_src_ip(params.mirror_encap_src_ip);
  action.set_mirror_encap_dst_ip(params.mirror_encap_dst_ip);
  action.set_mirror_encap_udp_src_port(params.mirror_encap_udp_src_port);
  action.set_mirror_encap_udp_dst_port(params.mirror_encap_udp_dst_port);
  *entries_.add_entries() = std::move(pd_entry);
  return *this;
}

EntryBuilder& EntryBuilder::AddIpv6TunnelTerminationEntry(
    const Ipv6TunnelTerminationParams& params) {
  sai::TableEntry pd_entry;
  sai::Ipv6TunnelTerminationTableEntry& tunnel_entry =
      *pd_entry.mutable_ipv6_tunnel_termination_table_entry();
  if (params.dst_ipv6.has_value()) {
    tunnel_entry.mutable_match()->mutable_dst_ipv6()->set_value(
        params.dst_ipv6->value.ToString());
    tunnel_entry.mutable_match()->mutable_dst_ipv6()->set_mask(
        params.dst_ipv6->mask.ToString());
  }
  if (params.src_ipv6.has_value()) {
    tunnel_entry.mutable_match()->mutable_src_ipv6()->set_value(
        params.src_ipv6->value.ToString());
    tunnel_entry.mutable_match()->mutable_src_ipv6()->set_mask(
        params.src_ipv6->mask.ToString());
  }
  tunnel_entry.mutable_action()->mutable_tunnel_decap();
  tunnel_entry.set_priority(1);
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

EntryBuilder& EntryBuilder::AddEntryToSetDscpAndQueuesAndDenyAboveRateLimit(
    AclQueueAssignments queue_assignments,
    AclMeterConfiguration meter_configuration) {
  sai::TableEntry& entry = *entries_.add_entries();
  entry.mutable_acl_ingress_qos_table_entry()->set_priority(1);
  auto& meter =
      *entry.mutable_acl_ingress_qos_table_entry()->mutable_meter_config();
  meter.set_bytes_per_second(meter_configuration.bytes_per_second);
  meter.set_burst_bytes(meter_configuration.burst_bytes);
  auto& queue_and_rate_limit_action =
      *entry.mutable_acl_ingress_qos_table_entry()
           ->mutable_action()
           ->mutable_set_dscp_and_queues_and_deny_above_rate_limit();
  queue_and_rate_limit_action.set_dscp("0x05");
  queue_and_rate_limit_action.set_cpu_queue(queue_assignments.cpu_queue);
  queue_and_rate_limit_action.set_green_multicast_queue(
      queue_assignments.multicast_green_queue);
  queue_and_rate_limit_action.set_red_multicast_queue(
      queue_assignments.multicast_red_queue);
  queue_and_rate_limit_action.set_green_unicast_queue(
      queue_assignments.unicast_green_queue);
  queue_and_rate_limit_action.set_red_unicast_queue(
      queue_assignments.unicast_red_queue);
  return *this;
}

EntryBuilder& EntryBuilder::AddVlanEntry(absl::string_view vlan_id_hexstr) {
  sai::TableEntry pd_entry;
  sai::VlanTableEntry& vlan_entry = *pd_entry.mutable_vlan_table_entry();
  vlan_entry.mutable_match()->set_vlan_id(vlan_id_hexstr);
  vlan_entry.mutable_action()->mutable_no_action();
  *entries_.add_entries() = std::move(pd_entry);
  return *this;
}

EntryBuilder& EntryBuilder::AddVlanMembershipEntry(
    absl::string_view vlan_id_hexstr, absl::string_view port,
    VlanTaggingMode tagging_mode) {
  sai::TableEntry pd_entry;
  sai::VlanMembershipTableEntry& vlan_membership_entry =
      *pd_entry.mutable_vlan_membership_table_entry();
  vlan_membership_entry.mutable_match()->set_vlan_id(vlan_id_hexstr);
  vlan_membership_entry.mutable_match()->set_port(port);
  switch (tagging_mode) {
    case VlanTaggingMode::kTagged:
      vlan_membership_entry.mutable_action()->mutable_make_tagged_member();
      break;
    case VlanTaggingMode::kUntagged:
      vlan_membership_entry.mutable_action()->mutable_make_untagged_member();
      break;
  }
  *entries_.add_entries() = std::move(pd_entry);
  return *this;
}

}  // namespace sai
