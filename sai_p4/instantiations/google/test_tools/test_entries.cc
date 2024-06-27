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

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "gutil/proto.h"
#include "gutil/status.h"
#include "gutil/testing.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/pd.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"

namespace sai {

absl::StatusOr<sai::TableEntries> MakePdEntriesForwardingIpPacketsToGivenPort(
    absl::string_view egress_port) {
  ASSIGN_OR_RETURN(
      sai::TableEntries entries,
      gutil::ParseTextProto<sai::TableEntries>(
          R"pb(
            entries {
              l3_admit_table_entry {
                match {}  # Wildcard.
                action { admit_to_l3 {} }
                priority: 1
              }
            }
            entries {
              vrf_table_entry {
                match { vrf_id: "vrf" }
                action { no_action {} }
              }
            }
            entries {
              acl_pre_ingress_table_entry {
                match {}  # Wildcard.
                action { set_vrf { vrf_id: "vrf" } }
                priority: 1
              }
            }
            entries {
              ipv4_table_entry {
                match { vrf_id: "vrf" }  # Default route.
                action { set_nexthop_id { nexthop_id: "nexthop" } }
              }
            }
            entries {
              ipv6_table_entry {
                match { vrf_id: "vrf" }  # Default route.
                action { set_nexthop_id { nexthop_id: "nexthop" } }
              }
            }
            entries {
              nexthop_table_entry {
                match { nexthop_id: "nexthop" }
                action {
                  set_ip_nexthop {
                    router_interface_id: "rif"
                    neighbor_id: "fe80::2:2ff:fe02:202"
                  }
                }
              }
            }
            entries {
              neighbor_table_entry {
                match {
                  router_interface_id: "rif"
                  neighbor_id: "fe80::2:2ff:fe02:202"
                }
                action { set_dst_mac { dst_mac: "02:03:04:05:06:07" } }
              }
            }
          )pb"));
  sai::TableEntry& router_interface_table_entry = *entries.add_entries();
  router_interface_table_entry = gutil::ParseProtoOrDie<sai::TableEntry>(
      R"pb(
        router_interface_table_entry {
          match { router_interface_id: "rif" }
          action { set_port_and_src_mac { src_mac: "00:01:02:03:04:05" } }
        }
      )pb");
  router_interface_table_entry.mutable_router_interface_table_entry()
      ->mutable_action()
      ->mutable_set_port_and_src_mac()
      // Open-source proto does not yet support string_views here.
      ->set_port(std::string(egress_port));
  return entries;
}

absl::StatusOr<sai::TableEntry> MakePdEntryPuntingAllPackets(
    PuntAction action) {
  ASSIGN_OR_RETURN(sai::TableEntry entry,
                   gutil::ParseTextProto<sai::TableEntry>(
                       R"pb(
                         acl_ingress_table_entry {
                           match {}     # Wildcard match
                           priority: 1  # Highest priority
                         }
                       )pb"));
  auto& acl_action = *entry.mutable_acl_ingress_table_entry()->mutable_action();
  switch (action) {
    case PuntAction::kTrap:
      acl_action.mutable_acl_trap()->set_qos_queue("0x7");
      return entry;
    case PuntAction::kCopy:
      acl_action.mutable_acl_copy()->set_qos_queue("0x7");
      return entry;
  }
  return gutil::InvalidArgumentErrorBuilder()
         << "invalid punt action: " << static_cast<int>(action);
}

absl::StatusOr<std::vector<p4::v1::TableEntry>>
MakePiEntriesForwardingIpPacketsToGivenPort(absl::string_view egress_port,
                                            const pdpi::IrP4Info& ir_p4info) {
  ASSIGN_OR_RETURN(sai::TableEntries pd_entries,
                   MakePdEntriesForwardingIpPacketsToGivenPort(egress_port));
  return pdpi::PartialPdTableEntriesToPiTableEntries(ir_p4info, pd_entries);
}

absl::StatusOr<pdpi::IrTableEntries> 
MakeIrEntriesForwardingIpPacketsToGivenPort(
			absl::string_view egress_port,
                        const pdpi::IrP4Info& ir_p4info) {
  ASSIGN_OR_RETURN(sai::TableEntries pd_entries,
                   MakePdEntriesForwardingIpPacketsToGivenPort(egress_port));
  return pdpi::PartialPdTableEntriesToIrTableEntries(ir_p4info, pd_entries);
}

absl::StatusOr<p4::v1::TableEntry> MakePiEntryPuntingAllPackets(
    PuntAction action, const pdpi::IrP4Info& ir_p4info) {
  ASSIGN_OR_RETURN(sai::TableEntry pd, MakePdEntryPuntingAllPackets(action));
  return pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, pd);
}
absl::StatusOr<pdpi::IrTableEntry> MakeIrEntryPuntingAllPackets(
    PuntAction action, const pdpi::IrP4Info& ir_p4info) {
  ASSIGN_OR_RETURN(sai::TableEntry pd, MakePdEntryPuntingAllPackets(action));
  return pdpi::PartialPdTableEntryToIrTableEntry(ir_p4info, pd);
}

}  // namespace sai
