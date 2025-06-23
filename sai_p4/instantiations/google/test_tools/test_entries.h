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

// Library of common table entries in PI and IR.
//
// These are suitable for use in switch testing and unit testing, e.g. with
// BMv2.

#ifndef PINS_SAI_P4_INSTANTIATIONS_GOOGLE_TEST_TOOLS_TEST_ENTRIES_H_
#define PINS_SAI_P4_INSTANTIATIONS_GOOGLE_TEST_TOOLS_TEST_ENTRIES_H_

#include <bitset>
#include <optional>
#include <string>
#include <utility>
#include <variant>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "absl/types/span.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/netaddr/ipv4_address.h"
#include "p4_infra/netaddr/ipv6_address.h"
#include "p4_infra/netaddr/mac_address.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/ternary.h"
#include "p4_infra/p4_runtime/p4_runtime_session.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"

namespace sai {

// TODO: Clean up these predefined bit widths once further
// refactors are completed.
constexpr int kVlanIdBitwidth = 12;
constexpr int kAclMetadataBitwidth = 8;
// NOTE: The actual bit-width of a multicast group ID is 16 bits, but we
// reserve the uppermost bit for a possible solution to handling L2/L3 multicast
// dependencies. 2^15 groups is more than sufficient for foreseeable use cases.
constexpr int kPdMulticastGroupIdBitwidth = 15;
constexpr int kReplicaInstanceBitwidth = 16;

// -- Actions ------------------------------------------------------------------
// Tagging mode for VLAN membership entries.
enum class VlanTaggingMode {
  kTagged,
  kUntagged,
};

struct Forward {};

struct RedirectToIpmcGroup {
  int multicast_group_id = 0;
};

struct RedirectToIpmcGroupAndSetCpuQueueAndCancelCopy {
  int multicast_group_id = 0;
  std::string cpu_queue;
};

struct SetCpuQueueAndCancelCopy {
  std::string cpu_queue;
};

// Parameters for generating a WCMPGroupTable action.
struct WcmpGroupAction {
  std::string nexthop_id;
  int weight = 1;
  std::optional<std::string> watch_port;
};

using MirrorAndRedirectAction =
    std::variant<Forward, RedirectToIpmcGroup,
                 RedirectToIpmcGroupAndSetCpuQueueAndCancelCopy,
                 SetCpuQueueAndCancelCopy>;

// Different ways of punting packets to the controller.
enum class PuntAction {
  // Punts copy of packet and prevents packet from being forwarded.
  kTrap,
  // Punts copy of packet without preventing packet from being forwarded.
  kCopy,
};

struct SetNextHopId {
  std::string nexthop_id;
};

struct SetWcmpGroupId {
  std::string wcmp_group_id;
};

struct SetVlanId {
  std::string vlan_id;
};

// -- Match Fields and Params --------------------------------------------------

// TODO: As this struct is not only used for nexthop rewrite, it should
// be renamed to better reflect the intended usage.
// Rewrite-related options for nexthop action generation.
struct NexthopRewriteOptions {
  bool disable_decrement_ttl = false;
  // When present, source MAC will be rewritten to the given address. When
  // absent, no rewrite occurs.
  std::optional<netaddr::MacAddress> src_mac_rewrite =
      netaddr::MacAddress(6, 5, 4, 3, 2, 1);
  // When present, destination MAC will be rewritten to the given address. When
  // absent, no rewrite occurs.
  std::optional<netaddr::MacAddress> dst_mac_rewrite =
      netaddr::MacAddress(2, 2, 2, 2, 2, 2);
  // If true, makes the nexthop use a `set_ip_nexthop_and_disable_rewrites`
  // action with `disable_vlan_rewrite` set to true. If false, such an action
  // may still be used based on above values (otherwise a `set_ip_nexthop`
  // action will be used), but `disable_vlan_rewrite` will be set false.
  bool disable_vlan_rewrite = false;
  // When present, causes the RIF to use an
  // `unicast_set_port_and_src_mac_and_vlan_id` action with `vlan_id =
  // egress_rif_vlan`. When absent, the RIF will instead use the
  // `unicast_set_port_and_src_mac` action.
  std::optional<std::string> egress_rif_vlan = std::nullopt;
  // TODO: once the `unicast_set_port_and_src_mac` action is fully
  // rolled out, remove this option and, for tests that need the old action,
  // manually build the entries.
  //
  // If true, makes the RIF use the `unicast_set_port_and_src_mac` action to
  // skip creating new a entry in switch's My MAC table (otherwise the legacy
  // `set_port_and_src_mac` action is used). For RIF with vlan_id, this option
  // is ignored, since it always skips My MAC entry creation.
  bool skip_my_mac_programming = true;
};

enum class IpVersion {
  kIpv4,
  kIpv6,
  // Targets both IPv4 and IPv6 packets.
  kIpv4And6,
};

struct Ipv4Lpm {
  netaddr::Ipv4Address dst_ip;
  int prefix_len = 0;  // Default is wildcard.
};

struct Ipv6Lpm {
  netaddr::Ipv6Address dst_ip;
  int prefix_len = 0;  // Default is wildcard.
};

struct IpForwardingParams {
  // If nullopt, no forwarding for that IP version.
  std::optional<Ipv4Lpm> ipv4_lpm = Ipv4Lpm{};
  std::optional<Ipv6Lpm> ipv6_lpm = Ipv6Lpm{};
};

template <typename Sink>
void AbslStringify(Sink& sink, const IpVersion& ip_version) {
  switch (ip_version) {
    case IpVersion::kIpv4:
      absl::Format(&sink, "IPv4");
      break;
    case IpVersion::kIpv6:
      absl::Format(&sink, "IPv6");
      break;
    case IpVersion::kIpv4And6:
      absl::Format(&sink, "IPv4And6");
      break;
  }
}

template <typename T>
struct P4RuntimeTernary {
  T value;
  T mask;
};

// Parameters for generating a mirror session table entry with IPFIX
// encapsulation.
struct MirrorSessionParams {
  std::string mirror_session_id;
  std::string monitor_port;
  std::string monitor_backup_port;
  std::string mirror_encap_src_mac;
  std::string mirror_encap_dst_mac;
  std::string mirror_encap_vlan_id;
  std::string mirror_encap_src_ip;
  std::string mirror_encap_dst_ip;
  std::string mirror_encap_udp_src_port;
  std::string mirror_encap_udp_dst_port;
};

// Parameters for generating an ipv6 tunnel termination table entry.
struct Ipv6TunnelTerminationParams {
  std::optional<P4RuntimeTernary<netaddr::Ipv6Address>> src_ipv6;
  std::optional<P4RuntimeTernary<netaddr::Ipv6Address>> dst_ipv6;
};

// Parameters for generating an ACL table entry to mark packets to be mirrored.
struct MarkToMirrorParams {
  std::string ingress_port;
  std::string mirror_session_id;
};

struct IpTableEntryParams {
  std::string vrf;
  using IpTableAction = std::variant<SetNextHopId, SetWcmpGroupId>;
  IpTableAction action;
};

struct RouterInterfaceTableParams {
  std::string router_interface_id;
  std::string egress_port;
  netaddr::MacAddress src_mac;
  std::optional<std::string> vlan_id;
  bool skip_my_mac_programming = true;
};

// Convenience struct corresponding to the protos `p4::v1::Replica` and
// `sai::ReplicateAction::Replica`.
struct BackupReplica {
  std::string egress_port;
  int instance = 0;
};
struct Replica {
  std::string egress_port;
  int instance = 0;
  std::vector<BackupReplica> backup_replicas;
};

// Match fields of an ingress mirror or redirect table entry.
struct MirrorAndRedirectMatchFields {
  std::optional<absl::string_view> in_port;
  std::optional<bool> route_hit;
  std::optional<int> vlan_id;
  std::optional<bool> is_ipv4;
  std::optional<sai::P4RuntimeTernary<netaddr::Ipv4Address>> dst_ip;
  std::optional<bool> is_ipv6;
  std::optional<sai::P4RuntimeTernary<netaddr::Ipv6Address>> dst_ipv6;
  std::optional<absl::string_view> vrf;
  pdpi::Ternary<std::bitset<kAclMetadataBitwidth>> acl_metadata;
};

// Queue settings for ACL table entry action.
struct AclQueueAssignments {
  absl::string_view cpu_queue = "0x0";
  absl::string_view unicast_green_queue = "0x1";
  absl::string_view unicast_red_queue = "0x0";
  absl::string_view multicast_green_queue = "0xb";
  absl::string_view multicast_red_queue = "0xa";
};

// Meter settings for ACL table entry action.
struct AclMeterConfiguration {
  int bytes_per_second = 1000;
  int burst_bytes = 1000;
};

struct AclPreIngressMatchFields {
  std::optional<bool> is_ip;
  std::optional<bool> is_ipv4;
  std::optional<bool> is_ipv6;
  std::optional<std::string> in_port;
  pdpi::Ternary<std::bitset<kVlanIdBitwidth>> vlan_id;
  std::optional<pdpi::Ternary<netaddr::Ipv6Address>> dst_ipv6;
};

struct AclPreIngressVlanTableMatchFields {
  pdpi::Ternary<std::bitset<kVlanIdBitwidth>> vlan_id;
  std::optional<bool> is_ip;
  std::optional<bool> is_ipv4;
  std::optional<bool> is_ipv6;
  std::optional<std::string> in_port;
};

struct AclIngressQosMatchFields {
  pdpi::Ternary<netaddr::MacAddress> dst_mac;
};

// -- Entry Builder ------------------------------------------------------------

// Provides methods to conveniently build a set of SAI-P4 table entries for
// testing.
//
// Example usage:
// ```
//   ASSERT_OK_AND_ASSIGN(pdpi::IrEntities ir_entities,
//     EntryBuilder(ir_p4info)
//       .AddEntriesForwardingIpPacketsToGivenPort("egress_port")
//       .AddEntryPuntingAllPackets(PuntAction::kCopy)
//       .GetDedupedIrEntities());
// ```
class EntryBuilder {
 public:
  EntryBuilder() = default;
  explicit EntryBuilder(sai::TableEntries entries)
      : entries_(std::move(entries)) {}

  // Logs the current PD entries in the EntryBuilder to LOG(INFO).
  const EntryBuilder& LogPdEntries() const;
  EntryBuilder& LogPdEntries();

  // Returns the current PD entries in the EntryBuilder in debug format.
  std::string GetPdEntriesDebugString() const;

  // Deduplicates then installs the entities encoded by the EntryBuilder using
  // `session`.
  absl::Status InstallDedupedEntities(
      p4_runtime::P4RuntimeSession& session) const;

  // Extracts and deduplicates the entities encoded by the EntryBuilder using
  // `ir_p4info`, then install them using `session`. This is especially useful
  // for BMv2 where you may *NOT* wish to use the P4Info on the switch for
  // translation.
  absl::Status InstallDedupedEntities(
      const pdpi::IrP4Info& ir_p4info,
      p4_runtime::P4RuntimeSession& session) const;

  absl::StatusOr<std::vector<p4::v1::Entity>> GetDedupedPiEntities(
      const pdpi::IrP4Info& ir_p4info) const;
  absl::StatusOr<pdpi::IrEntities> GetDedupedIrEntities(
      const pdpi::IrP4Info& ir_p4info) const;

  // Adds an entry that matches all packets and punts them according to
  // `action`.
  EntryBuilder& AddEntryPuntingAllPackets(PuntAction action);

  // Constructs all entries required to forward all `ip_version` packets to
  // `egress_port` and modify them using `rewrite_options`.
  // Note: Cannot be combined with other entries that forward *all* IP packets
  // in a specific way.
  EntryBuilder& AddEntriesForwardingIpPacketsToGivenPort(
      absl::string_view egress_port,
      IpVersion ip_version = IpVersion::kIpv4And6,
      const NexthopRewriteOptions& rewrite_options = {});

  // Constructs all entries required to forward IP packets to `egress_port`
  // based on `ip_forwarding_params` and modify them using `rewrite_options`.
  // Note: Cannot be combined with other entries that forward *all* IP packets
  // in a specific way.
  EntryBuilder& AddEntriesForwardingIpPacketsToGivenPort(
      absl::string_view egress_port,
      const IpForwardingParams& ip_forwarding_params,
      const NexthopRewriteOptions& rewrite_options = {});

  // Constructs a default IP route matching packets of `ip_version` with `vrf`
  // and sending them to `egress_port`. Matching packets will be modified using
  // `rewrite_options`.
  // Note: For packets to hit this route, additional entries are required! At a
  // minimum an L3 admit entry and entries that assign the given `vrf`.
  // Note: Cannot be combined with other entries that forward *all* IP packets
  // in a specific way unless they specify a different `vrf`.
  EntryBuilder& AddDefaultRouteForwardingAllPacketsToGivenPort(
      absl::string_view egress_port, IpVersion ip_version,
      absl::string_view vrf, const NexthopRewriteOptions& rewrite_options = {});

  // Constructs an IP route matching packets with `vrf` and
  // `ip_forwarding_params` and sending them to `egress_port`. Matching packets
  // will be modified using `rewrite_options`. Note: For packets to hit this
  // route, additional entries are required! At a minimum an L3 admit entry and
  // entries that assign the given `vrf`. Note: Cannot be combined with other
  // entries that forward *all* IP packets in a specific way unless they specify
  // a different `vrf`.
  EntryBuilder& AddL3LpmRouteForwardingUnicastPacketsToGivenPort(
      absl::string_view egress_port, absl::string_view vrf,
      const IpForwardingParams& ip_forwarding_params = {},
      const NexthopRewriteOptions& rewrite_options = {});

  // Constructs an IPv4 table entry matching packets with `vrf` and 'ipv4_lpm`
  // and setting the next table in the action to `next_table_id` based on the
  // `entry_params.action`.
  EntryBuilder& AddIpv4TableEntry(const IpTableEntryParams& entry_params,
                                  const Ipv4Lpm& ipv4_lpm = {});

  // Constructs an IPv6 table entry matching packets with `vrf` and 'ipv6_lpm`
  // and setting the next table in the action to `next_table_id` based on the
  // `entry_params.action`.
  EntryBuilder& AddIpv6TableEntry(const IpTableEntryParams& entry_params,
                                  const Ipv6Lpm& ipv6_lpm = {});

  // Constructs an IpNexthop entry with `nexthop_id` pointing to a neighbor
  // entry and RIF entry all characterized by `nexthop_rewrite_options`. The
  // RIF will output packets on `egress_port`.
  EntryBuilder& AddNexthopRifNeighborEntries(
      absl::string_view nexthop_id, absl::string_view egress_port,
      const NexthopRewriteOptions& rewrite_options = {});

  EntryBuilder& AddVrfEntry(absl::string_view vrf);
  EntryBuilder& AddEntryAdmittingAllPacketsToL3();
  EntryBuilder& AddMulticastRoute(absl::string_view vrf,
                                  const netaddr::Ipv4Address& dst_ip,
                                  int multicast_group_id);
  EntryBuilder& AddMulticastRoute(absl::string_view vrf,
                                  const netaddr::Ipv6Address& dst_ip,
                                  int multicast_group_id);
  // Adds a pre-ingress ACL table entry that matches packets with the given
  // `match_fields` and forwards them to the given `vrf`.
  EntryBuilder& AddPreIngressAclTableEntry(
      absl::string_view vrf, const AclPreIngressMatchFields& match_fields = {},
      int priority = 1);
  EntryBuilder& AddEntryTunnelTerminatingAllIpInIpv6Packets();
  EntryBuilder& AddEntryPuntingPacketsWithTtlZeroAndOne();
  EntryBuilder& AddEntryPuntingPacketsWithDstMac(
      absl::string_view dst_mac, PuntAction action = PuntAction::kTrap,
      absl::string_view qos_queue = "0x0");
  EntryBuilder& AddMulticastGroupEntry(int multicast_group_id,
                                       absl::Span<const Replica> replicas);
  EntryBuilder& AddMulticastGroupEntry(
      int multicast_group_id, absl::Span<const std::string> egress_ports);
  EntryBuilder& AddMrifEntryRewritingSrcMac(absl::string_view egress_port,
                                            int replica_instance,
                                            const netaddr::MacAddress& src_mac);
  EntryBuilder& AddMrifEntryRewritingSrcMacAndVlanId(
      absl::string_view egress_port, int replica_instance,
      const netaddr::MacAddress& src_mac, int vlan_id);
  EntryBuilder& AddMrifEntryRewritingSrcMacDstMacAndVlanId(
      absl::string_view egress_port, int replica_instance,
      const netaddr::MacAddress& src_mac, const netaddr::MacAddress& dst_mac,
      int vlan_id);
  EntryBuilder& AddMrifEntryRewritingSrcMacAndPreservingIngressVlanId(
      absl::string_view egress_port, int replica_instance,
      const netaddr::MacAddress& src_mac);
  EntryBuilder& AddL2MrifEntry(absl::string_view egress_port,
                               int replica_instance);

  EntryBuilder& AddIngressAclDroppingAllPackets();
  EntryBuilder& AddEgressAclDroppingIpPackets(
      IpVersion ip_version = IpVersion::kIpv4And6);
  EntryBuilder& AddDisableVlanChecksEntry();
  EntryBuilder& AddDisableIngressVlanChecksEntry();
  EntryBuilder& AddDisableEgressVlanChecksEntry();
  EntryBuilder& AddPreIngressAclEntrySettingVlanAndAclMetadata(
      absl::string_view vlan_id_hexstr, absl::string_view acl_metadata_hexstr,
      const AclPreIngressVlanTableMatchFields& match_fields = {},
      int priority = 1);
  EntryBuilder& AddEntrySettingVlanIdInPreIngress(
      absl::string_view vlan_id_hexstr,
      std::optional<absl::string_view> match_vlan_id_hexstr = std::nullopt,
      int priority = 1);
  EntryBuilder& AddIngressAclEntryRedirectingToNexthop(
      absl::string_view nexthop_id,
      const MirrorAndRedirectMatchFields& match_fields = {}, int priority = 1);
  EntryBuilder& AddIngressAclEntryRedirectingToMulticastGroup(
      int multicast_group_id,
      const MirrorAndRedirectMatchFields& match_fields = {});
  EntryBuilder& AddIngressAclMirrorAndRedirectEntry(
      const MirrorAndRedirectAction& action,
      const MirrorAndRedirectMatchFields& match_fields = {}, int priority = 1);
  EntryBuilder& AddIngressAclEntryRedirectingToPort(
      absl::string_view port,
      const MirrorAndRedirectMatchFields& match_fields = {}, int priority = 1);
  EntryBuilder& AddIngressAclEntryMirroringAndRedirectingToPort(
      absl::string_view port, absl::string_view mirror_session_id,
      const MirrorAndRedirectMatchFields& match_fields = {}, int priority = 1);
  EntryBuilder& AddIpv6TunnelTerminationEntry(
      const Ipv6TunnelTerminationParams& params);
  EntryBuilder& AddMirrorSessionTableEntry(const MirrorSessionParams& params);
  EntryBuilder& AddMarkToMirrorAclEntry(const MarkToMirrorParams& params);
  EntryBuilder& AddEntryToSetDscpAndQueuesAndDenyAboveRateLimit(
      AclQueueAssignments queue_assignments,
      AclMeterConfiguration meter_configuration);
  EntryBuilder& AddAclIngressQosDropTableEntry(
      const AclIngressQosMatchFields& match_fields = {}, int priority = 1);
  EntryBuilder& AddVlanEntry(absl::string_view vlan_id_hexstr);
  EntryBuilder& AddVlanMembershipEntry(absl::string_view vlan_id_hexstr,
                                       absl::string_view port,
                                       VlanTaggingMode tagging_mode);
  EntryBuilder& AddWcmpGroupTableEntry(
      absl::string_view wcmp_group_id,
      absl::Span<const WcmpGroupAction> wcmp_group_actions);

  EntryBuilder& AddIngressQoSTimestampingAclEntry(std::string ingress_port);

 private:
  sai::TableEntries entries_;
};

} // namespace sai

#endif // PINS_SAI_P4_INSTANTIATIONS_GOOGLE_TEST_TOOLS_TEST_ENTRIES_H_
