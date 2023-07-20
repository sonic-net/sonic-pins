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

// Library of common table entries in PI, IR, and PD encodings.
//
// CAUTION: PD entries are not suitable for switch testing, as the PD
// representation is not backward-compatible and thus will not work for release
// testing. However, PD entries can be useful in unit testing, e.g. with BMv2.

#ifndef GOOGLE_SAI_P4_INSTANTIATIONS_GOOGLE_TEST_TOOLS_TEST_ENTRIES_H_
#define GOOGLE_SAI_P4_INSTANTIATIONS_GOOGLE_TEST_TOOLS_TEST_ENTRIES_H_

#include <utility>
#include <vector>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"

namespace sai {

// Different ways of punting packets to the controller.
enum class PuntAction {
  // Punts copy of packet and prevents packet from being forwarded.
  kTrap,
  // Punts copy of packet without preventing packet from being forwarded.
  kCopy,
};

enum class IpVersion {
  kIpv4,
  kIpv6,
  kIpv4And6,
};

// Provides methods to conveniently build a set of SAI PD table entries for
// testing.
//
// CAUTION: PD entries are not suitable for switch testing, as the PD
// representation is not backward-compatible and thus will not work for release
// testing. However, PD entries can be useful in unit testing, e.g. with BMv2.
//
// Example usage:
// ```
//   sai::TableEntries entries =
//     PdEntryBuilder()
//       .AddEntriesForwardingIpPacketsToGivenPort("egress_port")
//       .AddEntryPuntingAllPackets(PuntAction::kCopy)
//       .GetDedupedEntries();
// ```
class PdEntryBuilder {
 public:
  PdEntryBuilder() = default;
  PdEntryBuilder(sai::TableEntries entries) : entries_(std::move(entries)) {}
  sai::TableEntries GetDedupedEntries();

  PdEntryBuilder& AddEntryPuntingAllPackets(PuntAction action);
  PdEntryBuilder& AddEntriesForwardingIpPacketsToGivenPort(
      absl::string_view egress_port);
  PdEntryBuilder& AddVrfEntry(absl::string_view vrf);
  PdEntryBuilder& AddEntryAdmittingAllPacketsToL3();
  PdEntryBuilder& AddDefaultRouteForwardingAllPacketsToGivenPort(
      absl::string_view egress_port, IpVersion ip_version,
      absl::string_view vrf);
  PdEntryBuilder& AddPreIngressAclEntryAssigningVrfForGivenIpType(
      absl::string_view vrf, IpVersion ip_version);
  PdEntryBuilder& AddEntryDecappingAllIpInIpv6PacketsAndSettingVrf(
      absl::string_view vrf);

 private:
  sai::TableEntries entries_;
};

// Returns an ACL table entry that punts all packets to the controller using the
// given punt `action`.
absl::StatusOr<p4::v1::TableEntry> MakePiEntryPuntingAllPackets(
    PuntAction action, const pdpi::IrP4Info& ir_p4info);
absl::StatusOr<pdpi::IrTableEntry> MakeIrEntryPuntingAllPackets(
    PuntAction action, const pdpi::IrP4Info& ir_p4info);
absl::StatusOr<sai::TableEntry> MakePdEntryPuntingAllPackets(PuntAction action);

// Returns a set of table entries that cause all IP packets to be forwarded
// out of the given `egress_port`.
absl::StatusOr<std::vector<p4::v1::TableEntry>>
MakePiEntriesForwardingIpPacketsToGivenPort(absl::string_view egress_port,
                                            const pdpi::IrP4Info& ir_p4info);
absl::StatusOr<pdpi::IrTableEntries> 
MakeIrEntriesForwardingIpPacketsToGivenPort(absl::string_view egress_port,
                                            const pdpi::IrP4Info& ir_p4info);
absl::StatusOr<sai::TableEntries> MakePdEntriesForwardingIpPacketsToGivenPort(
    absl::string_view egress_port);

}  // namespace sai

#endif  // GOOGLE_SAI_P4_INSTANTIATIONS_GOOGLE_TEST_TOOLS_TEST_ENTRIES_H_
