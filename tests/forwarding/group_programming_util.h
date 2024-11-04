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

#ifndef PINS_TESTS_FORWARDING_GROUP_PROGRAMMING_H_
#define PINS_TESTS_FORWARDING_GROUP_PROGRAMMING_H_

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/ir.pb.h"
#include "thinkit/test_environment.h"

// Set of helper functions to program and verify group operations.

namespace pins {

// Structure that holds the member details like port, weight and the
// nexthop object key (output) that was created.
struct Member {
  int weight = 1;
  int port = 0;
  std::string nexthop;
};

// Programs nexthop for the given set of members, also creates the dependant
// router interfaces and neighbor entries.
// members.nexthop is an output here with the updated nexthop object that was
// created.
absl::Status ProgramNextHops(thinkit::TestEnvironment& test_environment,
                             pdpi::P4RuntimeSession* const p4_session,
                             const pdpi::IrP4Info& ir_p4info,
                             std::vector<pins::Member>& members);

// Programs (insert/modify) a nexthop group on the switch with the given
// set of nexthops and weights. It is expected that the dependant nexthops are
// already created for an insert/modify operation.
absl::Status ProgramGroupWithMembers(thinkit::TestEnvironment& test_environment,
                                     pdpi::P4RuntimeSession* const p4_session,
                                     const pdpi::IrP4Info& ir_p4info,
                                     absl::string_view group_id,
                                     absl::Span<const Member> members,
                                     const p4::v1::Update_Type& type);

// Deletes the group with the given group_id. It is expected that the caller
// takes care of cleaning up the dependant nexthops.
absl::Status DeleteGroup(pdpi::P4RuntimeSession* const p4_session,
                         const pdpi::IrP4Info& ir_p4info,
                         absl::string_view group_id);

// Verifies the actual members received from P4 read response matches the
// expected members.
absl::Status VerifyGroupMembersFromP4Read(
    pdpi::P4RuntimeSession* const p4_session, const pdpi::IrP4Info& ir_p4info,
    absl::string_view group_id, absl::Span<const Member> expected_members);

// Verifies the actual members inferred from receive traffic matches the
// expected members.
// actual_ports is a map of the number of packets received(value) per port(key).
absl::Status VerifyGroupMembersFromReceiveTraffic(
    const absl::flat_hash_map<int, int>& actual_packets_received_per_port,
    const absl::flat_hash_set<int>& expected_member_ports);

// Generates N random weights that add up to total_weight, with at least 1 in
// each bucket.
absl::StatusOr<std::vector<int>> GenerateNRandomWeights(int n,
                                                        int total_weight);

// TODO: Temporary fix to rescale TH3 weights.
// To be removed when 256 member support is available.
int RescaleWeightForTomahawk3(int weight);

// TODO: Rescales the member weights to <=128 for now to match
// hardware behaviour, remove when hardware supports > 128 weights.
// Halves member weights >= 2 and works only for sum of initial member weights
// <= 256.
void RescaleMemberWeights(std::vector<Member>& members);

}  // namespace pins

#endif  // PINS_TESTS_FORWARDING_GROUP_PROGRAMMING_H_
