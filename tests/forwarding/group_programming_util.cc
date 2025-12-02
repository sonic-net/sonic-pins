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

#include "tests/forwarding/group_programming_util.h"

#include "absl/random/random.h"
#include "absl/random/uniform_int_distribution.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/substitute.h"
#include "google/protobuf/util/message_differencer.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/pd.h"
#include "sai_p4/fixed/ids.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"

namespace pins {

absl::Status ProgramNextHops(thinkit::TestEnvironment& test_environment,
                             pdpi::P4RuntimeSession& p4_session,
                             const pdpi::IrP4Info& ir_p4info,
                             std::vector<pins::GroupMember>& members) {
  std::vector<std::string> nexthops;
  std::vector<p4::v1::TableEntry> pi_entries;
  std::vector<sai::TableEntry> pd_entries;
  // Create router interface, neighbor and nexthop entry for every member.
  for (const auto& member : members) {
    // Create a router interface.
    auto router_interface =
        gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
            R"pb(
              router_interface_table_entry {
                match { router_interface_id: "$0" }
                action {
                  unicast_set_port_and_src_mac { port: "$1" src_mac: "$2" }
                }
              })pb",
            absl::StrCat("rif-", member.port), member.port,
            "00:02:03:04:05:06"));
    ASSIGN_OR_RETURN(
        p4::v1::TableEntry pi_entry,
        pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, router_interface),
        _.SetPrepend() << "Failed in PD table conversion to PI, entry: "
                       << router_interface.DebugString() << " error: ");
    pi_entries.push_back(pi_entry);
    pd_entries.push_back(router_interface);

    // Create neighbor entry.
    std::string neighbor_id = "fe80::2";
    auto neighbor_entry =
        gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
            R"pb(
              neighbor_table_entry {
                match { router_interface_id: "$0" neighbor_id: "$1" }
                action { set_dst_mac { dst_mac: "$2" } }
              })pb",
            absl::StrCat("rif-", member.port), neighbor_id,
            "3c:28:6d:34:c0:02"));
    ASSIGN_OR_RETURN(
        pi_entry,
        pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, neighbor_entry),
        _.SetPrepend() << "Failed in PD table conversion to PI, entry: "
                       << neighbor_entry.DebugString() << " error: ");
    pi_entries.push_back(pi_entry);
    pd_entries.push_back(neighbor_entry);

    // Create nexthop table entry.
    auto nexthop_id = absl::StrCat("nexthop-", member.port);
    auto nexthop_entry =
        gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
            R"pb(
              nexthop_table_entry {
                match { nexthop_id: "$0" }
                action {
                  set_ip_nexthop { router_interface_id: "$1" neighbor_id: "$2" }
                }
              })pb",
            nexthop_id, absl::StrCat("rif-", member.port), neighbor_id));
    ASSIGN_OR_RETURN(
        pi_entry,
        pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, nexthop_entry),
        _.SetPrepend() << "Failed in PD table conversion to PI, entry: "
                       << nexthop_entry.DebugString() << " error: ");
    pi_entries.push_back(pi_entry);
    pd_entries.push_back(nexthop_entry);
    nexthops.push_back(nexthop_id);
  }

  // Program the switch.
  RETURN_IF_ERROR(
      (pdpi::InstallPiTableEntries(&p4_session, ir_p4info, pi_entries)));

  // Write the PI & PD entries to artifacts.
  for (const auto& pi : pi_entries) {
    RETURN_IF_ERROR(test_environment.AppendToTestArtifact(
        "flows.pi.txt", absl::StrCat(pi.DebugString(), "\n")));
  }
  for (const auto& pd : pd_entries) {
    RETURN_IF_ERROR(test_environment.AppendToTestArtifact(
        "flows.pd.txt", absl::StrCat(pd.DebugString(), "\n")));
  }

  // Update the nexthop object strings(output) after successful nexthop create.
  for (int i = 0; i < nexthops.size(); i++) {
    members[i].nexthop = nexthops[i];
  }

  return absl::OkStatus();
}

absl::Status ProgramGroupWithMembers(thinkit::TestEnvironment& test_environment,
                                     pdpi::P4RuntimeSession& p4_session,
                                     const pdpi::IrP4Info& ir_p4info,
                                     absl::string_view group_id,
                                     absl::Span<const GroupMember> members,
                                     const p4::v1::Update_Type& type) {
  auto group_update = gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
      R"pb(
        wcmp_group_table_entry { match { wcmp_group_id: "$0" } })pb",
      group_id));
  switch (type) {
    case p4::v1::Update::INSERT:
    case p4::v1::Update::MODIFY: {
      for (const auto& member : members) {
        auto member_update =
            gutil::ParseProtoOrDie<sai::WcmpGroupTableEntry::WcmpAction>(
                absl::Substitute(
                    R"pb(
                      action { set_nexthop_id { nexthop_id: "$0" } }
                      weight: $1
                      watch_port: "$2"
                    )pb",
                    member.nexthop, member.weight, member.port));
        *group_update.mutable_wcmp_group_table_entry()->add_wcmp_actions() =
            member_update;
      }
      break;
    }
    default:
      return absl::InvalidArgumentError(
          absl::StrCat("Invalid update type ", static_cast<int>(type),
                       " specified for group entry programming"));
  }

  ASSIGN_OR_RETURN(
      p4::v1::TableEntry pi_entry,
      pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, group_update),
      _.SetPrepend() << "Failed in PD table conversion to PI, entry: "
                     << group_update.DebugString() << " error: ");

  p4::v1::WriteRequest write_request;
  p4::v1::Update* update = write_request.add_updates();
  update->set_type(type);
  *update->mutable_entity()->mutable_table_entry() = pi_entry;
  RETURN_IF_ERROR(
      pdpi::SetMetadataAndSendPiWriteRequest(&p4_session, write_request));

  // Append the PI & PD entries.
  RETURN_IF_ERROR(test_environment.AppendToTestArtifact(
      "flows.pi.txt", absl::StrCat(pi_entry.DebugString(), "\n")));
  RETURN_IF_ERROR(test_environment.AppendToTestArtifact(
      "flows.pd.txt", absl::StrCat(group_update.DebugString(), "\n")));
  return absl::OkStatus();
}

absl::Status DeleteGroup(pdpi::P4RuntimeSession& p4_session,
                         const pdpi::IrP4Info& ir_p4info,
                         absl::string_view group_id) {
  ASSIGN_OR_RETURN(
      p4::v1::WriteRequest write_request,
      pdpi::PdWriteRequestToPi(
          ir_p4info,
          gutil::ParseProtoOrDie<sai::WriteRequest>(absl::Substitute(
              R"pb(
                updates {
                  type: DELETE
                  table_entry {
                    wcmp_group_table_entry { match { wcmp_group_id: "$0" } }
                  }
                }
              )pb",
              group_id))));

  return pdpi::SetMetadataAndSendPiWriteRequest(&p4_session, write_request);
}

// Verifies  the actual members received from P4 read response matches the
// expected members.
absl::Status VerifyGroupMembersFromP4Read(
    pdpi::P4RuntimeSession& p4_session, const pdpi::IrP4Info& ir_p4info,
    absl::string_view group_id,
    absl::Span<const GroupMember> expected_members) {
  p4::v1::ReadRequest read_request;
  read_request.add_entities()->mutable_table_entry();
  ASSIGN_OR_RETURN(
      p4::v1::ReadResponse read_response,
      pdpi::SetMetadataAndSendPiReadRequest(&p4_session, read_request));

  // Filter out WCMP group entries separately from the whole read response.
  absl::flat_hash_map<std::string, p4::v1::TableEntry>
      actual_entries_per_group_id;
  for (const auto& entity : read_response.entities()) {
    if (entity.has_table_entry() &&
        entity.table_entry().table_id() == ROUTING_WCMP_GROUP_TABLE_ID) {
      auto temp_group_id = entity.table_entry().match(0).exact().value();
      actual_entries_per_group_id[temp_group_id] = entity.table_entry();
    }
  }
  // Pickup the required group entry.
  ASSIGN_OR_RETURN(
      const auto& actual_group_entry,
      gutil::FindOrStatus(actual_entries_per_group_id, std::string(group_id)));

  // Compute expected_group_entries.
  auto pd_group_update =
      gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
          R"pb(
            wcmp_group_table_entry { match { wcmp_group_id: "$0" } })pb",
          group_id));
  for (const auto& member : expected_members) {
    // Member weight and watch_port will be ignored in the MessageDifferencer
    // when checking for member validity.
    auto member_update =
        gutil::ParseProtoOrDie<sai::WcmpGroupTableEntry::WcmpAction>(
            absl::Substitute(R"pb(
                               action { set_nexthop_id { nexthop_id: "$0" } }
                               weight: 1
                               watch_port: ""
                             )pb",
                             member.nexthop));
    *pd_group_update.mutable_wcmp_group_table_entry()->add_wcmp_actions() =
        member_update;
  }
  ASSIGN_OR_RETURN(
      auto expected_group_entries,
      pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, pd_group_update),
      _.SetPrepend() << "Failed in PD table conversion to PI, entry: "
                     << pd_group_update.DebugString() << " error: ");

  google::protobuf::util::MessageDifferencer diff;
  diff.set_repeated_field_comparison(
      google::protobuf::util::MessageDifferencer::RepeatedFieldComparison::
          AS_SET);
  diff.IgnoreField(
      p4::v1::ActionProfileAction::descriptor()->FindFieldByName("weight"));
  diff.IgnoreField(
      p4::v1::ActionProfileAction::descriptor()->FindFieldByName("watch_port"));
  std::string diff_str;
  diff.ReportDifferencesToString(&diff_str);
  RET_CHECK(diff.Compare(actual_group_entry, expected_group_entries) == true)
      << "\nDifference in actual vs expected group entry: " << diff_str;
  return absl::OkStatus();
}

absl::StatusOr<std::vector<int>> GenerateNRandomWeights(int n,
                                                        int total_weight) {
  absl::BitGen gen;
  if (n > total_weight || n <= 0) {
    return absl::InvalidArgumentError("Invalid input argument");
  }

  std::vector<int> weights(n, 1);
  for (int i = 0; i < (total_weight - n); i++) {
    int x = absl::uniform_int_distribution<int>(0, n - 1)(gen);
    weights[x]++;
  }
  return weights;
}

std::string DescribeDistribution(
    int expected_total_test_packets,
    absl::Span<const pins::GroupMember> members,
    const absl::flat_hash_map<int, int>& num_packets_per_port,
    bool expect_single_port) {
  double total_weight = 0;
  for (const auto& member : members) {
    total_weight += member.weight;
  }
  std::string explanation = "";
  for (const auto& member : members) {
    double actual_packets = num_packets_per_port.contains(member.port)
                                ? num_packets_per_port.at(member.port)
                                : 0;
    if (expect_single_port) {
      absl::StrAppend(&explanation, "\nport ", member.port,
                      ": actual_count = ", actual_packets);
    } else {
      double expected_packets =
          expected_total_test_packets * member.weight / total_weight;
      absl::StrAppend(&explanation, "\nport ", member.port, " with weight ",
                      member.weight, ": expected_count = ", expected_packets,
                      ", actual_count = ", actual_packets);
    }
  }
  return explanation;
}

}  // namespace pins
