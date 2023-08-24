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

#ifndef GOOGLE_SAI_P4_INSTANTIATIONS_GOOGLE_TEST_TOOLS_TEST_ENTRIES_H_
#define GOOGLE_SAI_P4_INSTANTIATIONS_GOOGLE_TEST_TOOLS_TEST_ENTRIES_H_

#include <string>
#include <utility>
#include <vector>

#include "absl/base/attributes.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "absl/types/span.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/netaddr/mac_address.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"

namespace sai {

// Different ways of punting packets to the controller.
enum class PuntAction {
  // Punts copy of packet and prevents packet from being forwarded.
  kTrap,
  // Punts copy of packet without preventing packet from being forwarded.
  kCopy,
};

// Rewrite-related options for nexthop action generation.
struct NexthopRewriteOptions {
  bool disable_ttl_rewrite = false;
  bool disable_src_mac_rewrite = false;
  bool disable_dst_mac_rewrite = false;
  bool disable_vlan_rewrite = false;
};

enum class IpVersion {
  kIpv4,
  kIpv6,
  kIpv4And6,
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

// Convenience struct corresponding to the protos `p4::v1::Replica` and
// `sai::ReplicateAction::Replica`.
struct Replica {
  std::string egress_port;
  int instance = 0;
};

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

  absl::StatusOr<std::vector<p4::v1::Entity>> GetDedupedPiEntities(
      const pdpi::IrP4Info& ir_p4info, bool allow_unsupported = false) const;
  absl::StatusOr<pdpi::IrEntities> GetDedupedIrEntities(
      const pdpi::IrP4Info& ir_p4info, bool allow_unsupported = false) const;

  // Convenience struct corresponding to the proto
  // `MulticastRouterInterfaceTableEntry`
  // in `sai_pd.proto`.
  struct MulticastRouterInterfaceTableEntry {
    std::string multicast_replica_port;
    int multicast_replica_instance = 0;
    netaddr::MacAddress src_mac;
  };

  EntryBuilder& AddEntryPuntingAllPackets(PuntAction action);
  // Note: Cannot be combined with other entries that forward *all* IP packets
  // in a specific way.
  EntryBuilder& AddEntriesForwardingIpPacketsToGivenPort(
      absl::string_view egress_port);
  // Note: Cannot be combined with other entries that forward *all* IP packets
  // in a specific way.

  EntryBuilder& AddEntriesForwardingIpPacketsToGivenPort(
      absl::string_view egress_port,
      const NexthopRewriteOptions& rewrite_options);
  // Note: Cannot be combined with other entries that forward *all* IP packets
  // in a specific way.
  EntryBuilder& AddEntriesForwardingIpPacketsToGivenMulticastGroup(
      int multicast_group_id);
  EntryBuilder& AddVrfEntry(absl::string_view vrf);
  EntryBuilder& AddEntryAdmittingAllPacketsToL3();

  EntryBuilder& AddDefaultRouteForwardingAllPacketsToGivenPort(
      absl::string_view egress_port, IpVersion ip_version,
      absl::string_view vrf);
  EntryBuilder& AddDefaultRouteForwardingAllPacketsToGivenMulticastGroup(
      int multicast_group_id, IpVersion ip_version, absl::string_view vrf);
  EntryBuilder& AddPreIngressAclEntryAssigningVrfForGivenIpType(
      absl::string_view vrf, IpVersion ip_version);
  EntryBuilder& AddEntryDecappingAllIpInIpv6PacketsAndSettingVrf(
      absl::string_view vrf);
  EntryBuilder& AddEntryPuntingPacketsWithTtlZeroAndOne();
  EntryBuilder& AddMulticastGroupEntry(int multicast_group_id,
                                         absl::Span<const Replica> replicas);
  EntryBuilder& AddMulticastGroupEntry(
      int multicast_group_id, absl::Span<const std::string> egress_ports);
  EntryBuilder& AddMulticastRouterInterfaceEntry(
      const MulticastRouterInterfaceTableEntry& entry);
  EntryBuilder& AddIngressAclDroppingAllPackets();
  EntryBuilder& AddDisableVlanChecksEntry();

 private:
  sai::TableEntries entries_;
};

// Returns an ACL table entry that punts all packets to the controller using the
// given punt `action`.
ABSL_DEPRECATED(
    "Use "
    "EntryBuilder().AddEntryPuntingAllPackets(`action`)."
    "GetDedupedPiEntities(`ir_p4info`) instead.")
absl::StatusOr<p4::v1::TableEntry> MakePiEntryPuntingAllPackets(
    PuntAction action, const pdpi::IrP4Info& ir_p4info);
ABSL_DEPRECATED(
    "Use "
    "EntryBuilder().AddEntryPuntingAllPackets(`action`)."
    "GetDedupedIrEntities(`ir_p4info`) instead.")
absl::StatusOr<pdpi::IrTableEntry> MakeIrEntryPuntingAllPackets(
    PuntAction action, const pdpi::IrP4Info& ir_p4info);
ABSL_DEPRECATED(
    "Use "
    "EntryBuilder().AddEntryPuntingAllPackets(`action`)."
    "GetDedupedPiEntities(`ir_p4info`) instead.")
absl::StatusOr<sai::TableEntry> MakePdEntryPuntingAllPackets(PuntAction action);

// Returns a set of table entries that cause all IP packets to be forwarded
// out of the given `egress_port`.
ABSL_DEPRECATED(
    "Use "
    "EntryBuilder().AddEntriesForwardingIpPacketsToGivenPort(`egress_port`)."
    "GetDedupedPiEntities(`ir_p4info`) instead.")
absl::StatusOr<std::vector<p4::v1::TableEntry>>
MakePiEntriesForwardingIpPacketsToGivenPort(absl::string_view egress_port,
                                            const pdpi::IrP4Info& ir_p4info);
ABSL_DEPRECATED(
    "Use "
    "EntryBuilder().AddEntriesForwardingIpPacketsToGivenPort(`egress_port`)."
    "GetDedupedIrEntities(`ir_p4info`) instead.")
absl::StatusOr<pdpi::IrTableEntries>
MakeIrEntriesForwardingIpPacketsToGivenPort(absl::string_view egress_port,
                                            const pdpi::IrP4Info& ir_p4info);
ABSL_DEPRECATED(
    "Use "
    "EntryBuilder().AddEntriesForwardingIpPacketsToGivenPort(`egress_port`)."
    "GetDedupedPiEntities(`ir_p4info`) instead.")
absl::StatusOr<sai::TableEntries> MakePdEntriesForwardingIpPacketsToGivenPort(
    absl::string_view egress_port);

}  // namespace sai

#endif  // GOOGLE_SAI_P4_INSTANTIATIONS_GOOGLE_TEST_TOOLS_TEST_ENTRIES_H_
