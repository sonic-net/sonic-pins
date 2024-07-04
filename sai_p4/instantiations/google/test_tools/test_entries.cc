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

#include <algorithm>
#include <string>
#include <utility>
#include <vector>

#include "absl/algorithm/container.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "glog/logging.h"
#include "google/protobuf/message.h"
#include "google/protobuf/message_lite.h"
#include "google/protobuf/repeated_ptr_field.h"
#include "gutil/proto.h"
#include "gutil/status.h"
#include "gutil/testing.h"
#include "p4/v1/p4runtime.pb.h"
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
      // TODO: Pass string_view directly once proto supports it.
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

// -- PdEntryBuilder -----------------------------------------------------------

namespace {

bool ProtoLessThan(const google::protobuf::Message& x,
                   const google::protobuf::Message& y) {
  return x.SerializeAsString() < y.SerializeAsString();
}
bool ProtoEqual(const google::protobuf::Message& x,
                const google::protobuf::Message& y) {
  return google::protobuf::util::MessageDifferencer::Equals(x, y);
}

// TODO: Use `google::protobuf::util::StableSortAndUnique` instead once that
// is open source.
template <class T>
void StableSortAndUnique(
    google::protobuf::RepeatedPtrField<T>& repeated_field) {
  auto sorted = std::move(repeated_field);
  absl::c_stable_sort(sorted, ProtoLessThan);
  repeated_field.Clear();
  absl::c_unique_copy(
      sorted, google::protobuf::RepeatedPtrFieldBackInserter(&repeated_field),
      ProtoEqual);
}

}  // namespace

sai::TableEntries PdEntryBuilder::GetDedupedEntries() {
  sai::TableEntries result = entries_;
  StableSortAndUnique(*result.mutable_entries());
  return result;
}

PdEntryBuilder& PdEntryBuilder::AddVrfEntry(absl::string_view vrf) {
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

PdEntryBuilder& PdEntryBuilder::AddEntryAdmittingAllPacketsToL3() {
  *entries_.add_entries() = gutil::ParseProtoOrDie<sai::TableEntry>(R"pb(
    l3_admit_table_entry {
      match {}  # Wildcard.
      action { admit_to_l3 {} }
      priority: 1
    }
  )pb");
  return *this;
}

PdEntryBuilder& PdEntryBuilder::AddEntryPuntingAllPackets(PuntAction action) {
  absl::StatusOr<sai::TableEntry> entry = MakePdEntryPuntingAllPackets(action);
  CHECK_OK(entry.status());  // Crash ok: test-only library.
  *entries_.add_entries() = std::move(*entry);
  return *this;
}

PdEntryBuilder& PdEntryBuilder::AddDefaultRouteForwardingAllPacketsToGivenPort(
    absl::string_view egress_port, IpVersion ip_version,
    absl::string_view vrf) {
  const std::string kNexthopId =
      absl::StrFormat("nexthop(%s, %s)", egress_port, vrf);
  const std::string kRifId = absl::StrFormat("rif(port = %s)", egress_port);
  if (ip_version == IpVersion::kIpv4 || ip_version == IpVersion::kIpv4And6) {
    sai::TableEntry& entry = *entries_.add_entries();
    entry = gutil::ParseProtoOrDie<sai::TableEntry>(R"pb(
      ipv4_table_entry {
        # IP match field ommitted so this entry serves as the default route.
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
        # IP match field ommitted so this entry serves as the default route.
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
  {
    sai::TableEntry& entry = *entries_.add_entries();
    entry = gutil::ParseProtoOrDie<sai::TableEntry>(R"pb(
      nexthop_table_entry {
        match { nexthop_id: "nexthop" }
        action {
          set_ip_nexthop { router_interface_id: "rif" neighbor_id: "fe80::2" }
        }
      }
    )pb");
    entry.mutable_nexthop_table_entry()->mutable_match()->set_nexthop_id(
        kNexthopId);
    entry.mutable_nexthop_table_entry()
        ->mutable_action()
        ->mutable_set_ip_nexthop()
        ->set_router_interface_id(kRifId);
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
    sai::TableEntry& entry = *entries_.add_entries();
    entry = gutil::ParseProtoOrDie<sai::TableEntry>(R"pb(
      router_interface_table_entry {
        match { router_interface_id: "rif" }
        action { set_port_and_src_mac { src_mac: "00:01:02:03:04:05" } }
      }
    )pb");
    entry.mutable_router_interface_table_entry()
        ->mutable_match()
        ->set_router_interface_id(kRifId);
    entry.mutable_router_interface_table_entry()
        ->mutable_action()
        ->mutable_set_port_and_src_mac()
        // TODO: Pass string_view directly once proto supports it.
        ->set_port(std::string(egress_port));
  }
  return *this;
}

PdEntryBuilder& PdEntryBuilder::AddEntriesForwardingIpPacketsToGivenPort(
    absl::string_view egress_port) {
  absl::StatusOr<sai::TableEntries> entries =
      MakePdEntriesForwardingIpPacketsToGivenPort(egress_port);
  CHECK_OK(entries.status());  // Crash ok: test-only library.
  for (auto& entry : *entries->mutable_entries()) {
    *entries_.add_entries() = std::move(entry);
  }
  return *this;
}

PdEntryBuilder& PdEntryBuilder::AddPreIngressAclEntryAssigningVrfForGivenIpType(
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

}  // namespace sai
