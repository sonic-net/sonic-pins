// Copyright 2025 Google LLC
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

#include "tests/forwarding/multistage_hash_test.h"

#include <string>
#include <utility>
#include <vector>

#include "absl/container/btree_set.h"
#include "absl/container/flat_hash_set.h"
#include "absl/container/node_hash_map.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/p4rt/p4rt_port.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "tests/forwarding/group_programming_util.h"
#include "tests/forwarding/hash_statistics_util.h"
#include "tests/forwarding/hash_testfixture.h"
#include "thinkit/switch.h"

namespace pins_test {

namespace {
constexpr char kIpv4Packets[] = "IPv4Packets";
constexpr char kIpv6Packets[] = "IPv6Packets";
constexpr absl::string_view kEcmpInterfaceHashAlgPath =
    "interfaces/interface[name=$0]/$1/ecmp-hash-algorithm";

struct WcmpGroup {
  std::vector<pins::GroupMember> members;
  int total_weight = 0;
};

absl::StatusOr<WcmpGroup> CreateWcmpGroup(
    const absl::btree_set<P4rtPortId>& port_ids, int size) {
  // Make the first weight the largest since we track packets from that member.
  // Making the first member the largest means we can get the largest number of
  // packets.
  static const auto* const kWeights = new std::vector<int>{8, 7, 6};
  if (port_ids.size() < size) {
    return absl::FailedPreconditionError(
        absl::StrCat("Not enough ports available for test. Needed ", size,
                     " but got ", port_ids.size(), "."));
  }
  WcmpGroup wcmp_group;
  auto weight = kWeights->begin();
  auto port_id = port_ids.begin();
  while (wcmp_group.members.size() < size) {
    wcmp_group.members.push_back({
        .weight = *weight,
        .port = static_cast<int>(port_id->GetOpenConfigEncoding()),
    });
    wcmp_group.total_weight += *weight;
    if (++weight == kWeights->end()) weight = kWeights->begin();
    ++port_id;
  }
  return wcmp_group;
}

// Returns a hash algorithm that is different than the 'old_hash_alg' but
// still within the max of 2 hash algorithms allowed per port.
absl::StatusOr<std::string> GetNewHashAlgorithm(
    gnmi::gNMI::StubInterface& sut_gnmi_stub, absl::string_view old_hash_alg) {
  ASSIGN_OR_RETURN(
      openconfig::Interfaces all_interfaces,
      GetInterfacesAsProto(sut_gnmi_stub, gnmi::GetRequest::CONFIG));

  absl::flat_hash_set<std::string> hash_algorithms;
  for (const auto& interface : all_interfaces.interfaces()) {
    if (interface.config().has_ecmp_hash_algorithm()) {
      hash_algorithms.insert(interface.config().ecmp_hash_algorithm());
    }
  }

  // Pick a different hash algorithm if available.
  for (const auto& hash_algorithm : hash_algorithms) {
    if (hash_algorithm != old_hash_alg) return hash_algorithm;
  }
  return old_hash_alg == "CRC_CCITT" ? "CRC" : "CRC_CCITT";
}

void VerifyDistribution(
    const TestPacketMap& test_packet_map,
    const std::vector<pins::GroupMember>& members,
    const absl::node_hash_map<std::string, HashTest::TestData>& hash_test_data,
    absl::string_view test_stage, double confidence, Statistic statistic) {
  SCOPED_TRACE(absl::StrCat("Hash distribution failed for ", test_stage));
  LOG(INFO) << "Hash distribution results for " << test_stage;
  for (const auto& [config, data] : hash_test_data) {
    Distribution actual_distribution;
    for (const auto& [port, packets] : data.Results()) {
      int port_id;
      ASSERT_TRUE(absl::SimpleAtoi(port, &port_id));
      actual_distribution[port_id] = packets.size();
    }
    SCOPED_TRACE(absl::StrCat("Failed to verify ", config));
    LOG(INFO) << "Results for " << config;
    double actual_confidence;
    ASSERT_OK(TestDistribution(members, actual_distribution, confidence,
                               test_packet_map.at(config).size(), statistic,
                               actual_confidence));
    testing::Test::RecordProperty(
        absl::StrCat(test_stage, ".", config, ".confidence"),
        actual_confidence);
  }
}

}  // namespace

TEST_P(HashMultiStage, MultiStageHashingHasNoPolarizationWithWcmp) {
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub,
                       GetMirrorTestbed().Sut().CreateGnmiStub());

  ASSERT_OK_AND_ASSIGN(WcmpGroup first_stage_group,
                       CreateWcmpGroup(PortIds(), 4));
  pins::GroupMember intermediate_member = *first_stage_group.members.begin();
  P4rtPortId intermediate_port =
      P4rtPortId::MakeFromOpenConfigEncoding(intermediate_member.port);
  ASSERT_OK_AND_ASSIGN(WcmpGroup test_group, CreateWcmpGroup(PortIds(), 10));

  // Generate IPv4 & IPv6 packets with random field values of all applicable
  // hash fields.
  // The number of packets generated should be large enough that the
  // intermediate member port receives enough packets for the stage 2 test.
  const int num_packets = PercentErrorTestPacketCount(test_group.total_weight) *
                          first_stage_group.total_weight /
                          intermediate_member.weight;
  ASSERT_OK_AND_ASSIGN(auto ipv4_packets,
                       GeneratePackets(Ipv4HashingOptions(), num_packets));
  ASSERT_OK_AND_ASSIGN(auto ipv6_packets,
                       GeneratePackets(Ipv6HashingOptions(), num_packets));
  TestPacketMap test_packets = {
      {kIpv4Packets, std::move(ipv4_packets)},
      {kIpv6Packets, std::move(ipv6_packets)},
  };

  // Program groups on SUT, send packets from control switch to sut
  // and capture packets on Control switch to verify distribution.
  ForwardAllPacketsToMembers(test_p4_info(), first_stage_group.members);
  const P4rtPortId ingress_port = DefaultIngressPort();
  absl::node_hash_map<std::string, TestData> hash_test_data;
  LOG(INFO) << "Sending " << num_packets * 2
            << " packets to first stage members, ingress port: "
            << ingress_port.GetP4rtEncoding();
  ASSERT_OK(SendPacketsAndRecordResultsPerTest(test_packets, test_p4_info(),
                                               "first_stage_", ingress_port,
                                               hash_test_data));
  VerifyDistribution(test_packets, first_stage_group.members, hash_test_data,
                     "first_stage", /*confidence=*/0.85,
                     Statistic::kPercentError);

  // Change the hash algorithm for the new ingress port.
  ASSERT_OK_AND_ASSIGN(std::string ingress_interface_name,
                       GnmiInterfaceName(ingress_port));
  ASSERT_OK_AND_ASSIGN(
      std::string ingress_port_old_hash_alg,
      GetGnmiStateLeafValue(sut_gnmi_stub.get(),
                            absl::Substitute(kEcmpInterfaceHashAlgPath,
                                             ingress_interface_name, "state")));
  ASSERT_OK_AND_ASSIGN(
      std::string ingress_port_new_hash_alg,
      GetNewHashAlgorithm(*sut_gnmi_stub, ingress_port_old_hash_alg));
  ASSERT_OK(
      UpdateGnmiConfigLeaf(sut_gnmi_stub.get(),
                           absl::Substitute(kEcmpInterfaceHashAlgPath,
                                            ingress_interface_name, "config"),
                           ingress_port_new_hash_alg));
  LOG(INFO) << "Changed hash alg for ingress port " << ingress_interface_name
            << " from " << ingress_port_old_hash_alg << " to "
            << ingress_port_new_hash_alg;

  // Use packets received on the itermediate port for the second stage.
  test_packets.clear();
  int total_packets = 0;
  for (const auto& [config_name, data] : hash_test_data) {
    auto packets = data.GetReceivedPacketsOnPort(intermediate_port);
    total_packets += packets.size();
    test_packets[config_name] = std::move(packets);
  }

  hash_test_data.clear();
  ASSERT_OK(pdpi::ClearEntities(sut_p4_session()));
  // Send and record results for second stage .
  ForwardAllPacketsToMembers(test_p4_info(), test_group.members);
  LOG(INFO) << "Sending " << total_packets << " packets received from the "
            << "first stage on intermediate port " << intermediate_port
            << " to second stage members, ingress port: "
            << ingress_port.GetOpenConfigEncoding();
  ASSERT_OK(SendPacketsAndRecordResultsPerTest(test_packets, test_p4_info(),
                                               "second_stage_", ingress_port,
                                               hash_test_data));
  VerifyDistribution(test_packets, test_group.members, hash_test_data,
                     "second_stage", /*confidence=*/0.85,
                     Statistic::kPercentError);

  LOG(INFO) << "Restoring hash alg for second stage ingress port ("
            << ingress_interface_name << ") from " << ingress_port_new_hash_alg
            << " to " << ingress_port_old_hash_alg;
  EXPECT_OK(
      UpdateGnmiConfigLeaf(sut_gnmi_stub.get(),
                           absl::Substitute(kEcmpInterfaceHashAlgPath,
                                            ingress_interface_name, "config"),
                           ingress_port_old_hash_alg));
}

}  // namespace pins_test
