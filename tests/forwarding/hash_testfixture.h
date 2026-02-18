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

#ifndef PINS_TESTS_FORWARDING_HASH_TESTFIXTURE_H_
#define PINS_TESTS_FORWARDING_HASH_TESTFIXTURE_H_

#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "absl/base/thread_annotations.h"
#include "absl/container/btree_map.h"
#include "absl/container/btree_set.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/node_hash_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/synchronization/mutex.h"
#include "lib/p4rt/p4rt_port.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.pb.h"
#include "tests/forwarding/group_programming_util.h"
#include "tests/forwarding/packet_test_util.h"
#include "tests/lib/packet_generator.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/mirror_testbed_fixture.h"
#include "thinkit/test_environment.h"
#include "gtest/gtest.h"

namespace pins_test {

using TestConfigurationMap =
    absl::btree_map<std::string /*test_name*/, pins::TestConfiguration>;
using TestPacketMap =
    absl::btree_map<std::string /*test_name*/, std::vector<packetlib::Packet>>;
using TestPacketGenOptionsMap =
    absl::btree_map<std::string /*test_name*/, packetgen::Options>;

// This class stores and reports data on received packets. Particularly, it
// keeps track of packets based on the egress port for the SUT / ingress port of
// the Control Switch.
// Test class for the hash config test.
class HashTest : public testing::Test {
public:
  class TestData {
  public:
    // Map of port to the set of indices of received packets.
    // Sorted (btree) maps and sets help to make error messages more readable
    // when doing container comparisons.
    using ResultMap = absl::btree_map<std::string, absl::btree_set<int>>;

    // Return the results of the received packets.
    ResultMap Results() const ABSL_LOCKS_EXCLUDED(mutex_) {
      absl::MutexLock lock(&mutex_);
      return packets_by_port_;
    }

    // Add a received packet to this test data holder. Return false if the
    // packet isn't part of the hashing test.
    bool AddPacket(absl::string_view egress_port, packetlib::Packet packet)
        ABSL_LOCKS_EXCLUDED(mutex_);

    // Return the number of packets that have been received.
    int PacketCount() const ABSL_LOCKS_EXCLUDED(mutex_) {
      absl::MutexLock lock(&mutex_);
      return received_packets_.size();
    }

    // Log the packets while holding the mutex lock so we don't need to create
    // and return copy of received_packets_.
    absl::Status Log(thinkit::TestEnvironment &environment,
                     absl::string_view artifact_name)
        ABSL_LOCKS_EXCLUDED(mutex_);

    // Return all packets received on a particular port.
    // Note that repeated calls will return the same set of packets unless there
    // are new packets received from the last time it was called.
    std::vector<packetlib::Packet> GetReceivedPacketsOnPort(
        const P4rtPortId& port) const ABSL_LOCKS_EXCLUDED(mutex_);

   protected:
    // Mutex to guard the data values. Values are written by the receiver thread
    // and read by the main thread.
    mutable absl::Mutex mutex_;

    // Results as the set of packets arriving at each port.
    ResultMap packets_by_port_ ABSL_GUARDED_BY(mutex_);

    // In-order log of all the received packets paired with the egress port.
    // Useful for logging.
    std::vector<std::pair<std::string, packetlib::Packet>>
        received_packets_ ABSL_GUARDED_BY(mutex_);
  };

  // This enum represents the style of packet generation to use in
  // GeneratePackets().
  enum class PacketGeneratorStyle {
    kSequential,  // Values are sequentially generated with a wrap-around.
    kUniform,     // Values are randomly distributed uniformly across the range.
  };

  // Condition for running mirror_testbed_->TearDown().
  enum class TearDownCondition {
    kAlways,
    kOnFailure,
  };

  // Constructors.
  HashTest(thinkit::MirrorTestbedInterface *mirror_testbed_interface,
           p4::config::v1::P4Info p4info,
           TearDownCondition testbed_teardown_condition)
      : mirror_testbed_(mirror_testbed_interface),
        test_p4info_(std::move(p4info)),
        mirror_testbed_teardown_condition_(testbed_teardown_condition) {}

  HashTest(thinkit::MirrorTestbedInterface *mirror_testbed_interface,
           p4::config::v1::P4Info p4info)
      : HashTest(mirror_testbed_interface, p4info, TearDownCondition::kAlways) {
  }

  void SetUp() override;

  void TearDown() override;

  // Return the p4_info that was applied to the SUT during SetUp().
  const p4::config::v1::P4Info& test_p4_info() const { return test_p4info_; }

  // Return the p4_info on the control switch after SetUp().
  const p4::config::v1::P4Info& control_switch_p4_info() const {
    return control_switch_p4info_;
  }

  // MirrorTestbed accessors
  thinkit::MirrorTestbed &GetMirrorTestbed() {
    return mirror_testbed_->GetMirrorTestbed();
  }
  absl::Status SaveSwitchLogs(absl::string_view prefix) {
    return mirror_testbed_->SaveSwitchLogs(prefix);
  }

  // Record the P4Info file for debugging.
  absl::Status RecordP4Info(absl::string_view test_stage,
                            const p4::config::v1::P4Info& p4info);

  // Generate packets based on the provided test config. Values are sequential
  // if num_packets is sufficiently large compared to the range of unique
  // values. Otherwise, packets are generated with random values across the
  // available value range. Returns an error if the config is invalid.
  static absl::StatusOr<std::vector<packetlib::Packet>> GeneratePackets(
      const pins::TestConfiguration& test_config, int num_packets,
      PacketGeneratorStyle style);
  static absl::StatusOr<TestPacketMap> GeneratePackets(
      const TestConfigurationMap& test_configs, int num_packets,
      PacketGeneratorStyle style);
  static absl::StatusOr<std::vector<packetlib::Packet>> GeneratePackets(
      const packetgen::Options& options, int num_packets);

  // Send and receive packets for all test configs. Save the resulting test
  // data as a map of TestConfiguration name to TestData.
  absl::Status SendPacketsAndRecordResultsPerTest(
      const TestPacketMap &test_packets, const p4::config::v1::P4Info &p4info,
      absl::string_view test_stage, const P4rtPortId &ingress_port_id,
      absl::node_hash_map<std::string, TestData> &output_record);

  absl::Status SendPacketsToDefaultPortAndRecordResultsPerTest(
      const TestPacketMap &test_packets, const p4::config::v1::P4Info &p4info,
      absl::string_view test_stage,
      absl::node_hash_map<std::string, TestData> &output_record) {
    return SendPacketsAndRecordResultsPerTest(
        test_packets, p4info, test_stage, DefaultIngressPort(), output_record);
  }

  // Initializes the forwarding pipeline to forward all packets to the provided
  // group members distributed according to their weight.
  // Adds the nexthop-id to all members.
  void ForwardAllPacketsToMembers(const p4::config::v1::P4Info &p4info,
                                  std::vector<pins::GroupMember> &members);

  // Initializes the forwarding pipeline to forward all packets to the provided
  // ports with an equal distribution.
  void ForwardAllPacketsToPorts(const p4::config::v1::P4Info &p4info,
                                const absl::btree_set<P4rtPortId> &port_ids) {
    std::vector<pins::GroupMember> members;
    for (const auto &port_id : port_ids) {
      members.push_back(
          {.weight = 1,
           .port = static_cast<int>(port_id.GetOpenConfigEncoding())});
    }
    return ForwardAllPacketsToMembers(p4info, members);
  }

  // Returns the default ingress port for SendPacket requests.
  const P4rtPortId &DefaultIngressPort() const { return *PortIds().begin(); }

  // Returns the port IDs available to this test.
  const absl::btree_set<P4rtPortId> &PortIds() const { return port_ids_; }

  // Returns the gNMI interface for a given port ID.
  absl::StatusOr<std::string>
  GnmiInterfaceName(const P4rtPortId &port_id) const;

  // Returns the current P4Info from the SUT. If the forwarding pipeline is not
  // configured, returns an empty protobuf.
  absl::StatusOr<p4::config::v1::P4Info> GetSutP4Info();

  // Update the P4Info on the SUT.
  absl::Status UpdateSutP4Info(const p4::config::v1::P4Info& p4_info);

  // Accessors for the persistent P4 sessions for the test.
  pdpi::P4RuntimeSession& sut_p4_session() { return *sut_p4_session_; }
  pdpi::P4RuntimeSession& control_switch_p4_session() {
    return *control_p4_session_;
  }

protected:
  // Send and receive packets for a particular test config. Save the resulting
  // test data.
 absl::Status SendAndReceivePackets(
     const pdpi::IrP4Info &ir_p4info, absl::string_view record_prefix,
     const P4rtPortId &ingress_port_id,
     const std::vector<packetlib::Packet> &packets, TestData &test_data);

 private:
  void InitializeTestbed();

  // Set of interfaces to hash against. There is a 1:1 mapping of interfaces_ to
  // port_ids_, but we don't care about the mapping in the test.
  std::vector<std::string> interfaces_;


  // Set of port IDs to hash against.
  absl::btree_set<P4rtPortId> port_ids_;

  // A map of port IDs to interface names.
  absl::flat_hash_map<P4rtPortId, std::string> port_ids_to_interfaces_;

  // Testbed accessors.
  thinkit::MirrorTestbedInterface* mirror_testbed_;

  std::unique_ptr<pdpi::P4RuntimeSession> sut_p4_session_;
  std::unique_ptr<pdpi::P4RuntimeSession> control_p4_session_;

  p4::config::v1::P4Info test_p4info_;
  p4::config::v1::P4Info control_switch_p4info_;

 // Condition for running mirror_testbed_->TearDown().
 TearDownCondition mirror_testbed_teardown_condition_;
};

// Return the list of all packet TestConfigurations to be tested. Each
// TestConfiguration should result in a hash difference.
const TestConfigurationMap &HashingTestConfigs();

// Returns the list of all HashingTestConfigs() test names.
const std::vector<std::string> &HashingTestConfigNames();

const packetgen::Options& Ipv4HashingOptions();
const packetgen::Options& Ipv6HashingOptions();

// Return the list of all possible packet TestConfigurations that do not result
// in a hash difference.
const TestConfigurationMap &NonHashingTestConfigs();

// Returns the list of all NonHashingTestConfigs() test names.
const std::vector<std::string> &NonHashingTestConfigNames();

} // namespace pins_test

#endif // PINS_TESTS_FORWARDING_HASH_TESTFIXTURE_H_
