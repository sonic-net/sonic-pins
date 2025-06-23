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

#include <string>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/types/span.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_runtime/p4_runtime_session.h"
#include "thinkit/test_environment.h"

// Set of helper functions to program and verify group operations.

namespace pins {

// Structure that holds the member details like port, weight and the
// nexthop object key (output) that was created.
struct GroupMember {
  int weight = 1;
  int port = 0;
  std::string nexthop;
};

// Programs nexthop for the given set of members, also creates the dependant
// router interfaces and neighbor entries.
// members.nexthop is an output here with the updated nexthop object that was
// created.
absl::Status ProgramNextHops(thinkit::TestEnvironment& test_environment,
                             p4_runtime::P4RuntimeSession& p4_session,
                             const pdpi::IrP4Info& ir_p4info,
                             std::vector<pins::GroupMember>& members);

// Programs (insert/modify) a nexthop group on the switch with the given
// set of nexthops and weights. It is expected that the dependant nexthops are
// already created for an insert/modify operation.
absl::Status ProgramGroupWithMembers(thinkit::TestEnvironment& test_environment,
                                     p4_runtime::P4RuntimeSession& p4_session,
                                     const pdpi::IrP4Info& ir_p4info,
                                     absl::string_view group_id,
                                     absl::Span<const GroupMember> members,
                                     const p4::v1::Update_Type &type);

// Deletes the group with the given group_id. It is expected that the caller
// takes care of cleaning up the dependant nexthops.
absl::Status DeleteGroup(p4_runtime::P4RuntimeSession& p4_session,
                         const pdpi::IrP4Info& ir_p4info,
                         absl::string_view group_id);

// Verifies the actual members received from P4 read response matches the
// expected members.
absl::Status VerifyGroupMembersFromP4Read(
    p4_runtime::P4RuntimeSession& p4_session, const pdpi::IrP4Info& ir_p4info,
    absl::string_view group_id, absl::Span<const GroupMember> expected_members);

// Generates N random weights that add up to total_weight, with at least 1 in
// each bucket.
absl::StatusOr<std::vector<int>> GenerateNRandomWeights(int n,
                                                        int total_weight);

// Returns a human-readable description of the actual vs expected
// distribution of packets on the group member ports.
// expect_single_port specifies whether all packets are expected on a single
// output port(since no hashing applies) or multiple ports(with hashing).
std::string
DescribeDistribution(int expected_total_test_packets,
                     absl::Span<const pins::GroupMember> members,
                     const absl::flat_hash_map<int, int> &num_packets_per_port,
                     bool expect_single_port);

} // namespace pins

#endif // PINS_TESTS_FORWARDING_GROUP_PROGRAMMING_H_
