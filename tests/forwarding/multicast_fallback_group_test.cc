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

#include "tests/forwarding/multicast_fallback_group_test.h"

#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <thread>  // NOLINT(build/c++11)
#include <utility>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/escaping.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/synchronization/mutex.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "dvaas/test_vector.pb.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/p4rt/p4rt_port.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4_infra/p4_pdpi/pd.h"
#include "p4_infra/packetlib/packetlib.h"
#include "p4_infra/packetlib/packetlib.pb.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"
#include "tests/forwarding/packet_test_util.h"
#include "tests/forwarding/util.h"
#include "tests/lib/p4rt_fixed_table_programming_helper.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/test_environment.h"

namespace pins {

namespace {

// Vrf used in the test.
constexpr absl::string_view kVrfId = "vrf-1";

// Vlan used in the test.
constexpr int kVlanId = 2;
constexpr absl::string_view kVlanIdStr = "0x002";

// Multicast instance used in the test.
constexpr int kMulticastInstance = 1;

// Multicast group id used in the test.
constexpr int kMulticastGroupId = 1;

// Multicast IP address used in the test.
constexpr auto kMulticastDstIpv4 = netaddr::Ipv4Address(0xe0, 0, 0, 0x1);

// Time to wait after which received packets are processed.
constexpr absl::Duration kDurationToWaitForPackets = absl::Seconds(10);

// Number of replica ports used in the test, including the primary and backups.
constexpr int kNumReplicaPortsForTest = 5;

// Number of packets used in the test for multicast fallback.
constexpr int kNumTestPacketsForMulticastFallback = 6000;

// Rate of packets in packets per seconds.
constexpr int kPacketRateInSeconds = 600;

// Default input port index, on which packets arrive.
constexpr int kDefaultInputPortIndex = 0;

// Default replica port index.
constexpr int kDefaultReplicaPortIndex = 1;

// Punts all packets on the control switch.
absl::Status SetUpControlSwitch(pdpi::P4RuntimeSession& p4_session) {
  // Trap all packets on control switch.
  return sai::EntryBuilder()
      .AddEntryPuntingAllPackets(sai::PuntAction::kTrap)
      .LogPdEntries()
      .InstallDedupedEntities(p4_session);
}

// Gets replica ports from the controller port ids.
absl::StatusOr<std::vector<std::string>> GetReplicaPorts(
    int size, absl::Span<const pins_test::P4rtPortId> controller_port_ids_) {
  if (size + 2 > controller_port_ids_.size()) {
    return absl::InvalidArgumentError(
        absl::StrCat("Not enough ports: ", controller_port_ids_.size(),
                     " to reserve an input port and a default replica port and "
                     "create the replica ports with size: ",
                     size));
  }
  std::vector<std::string> replica_ports;
  for (int i = 0;
       i < controller_port_ids_.size() && replica_ports.size() < size; i++) {
    if (i != kDefaultInputPortIndex && i != kDefaultReplicaPortIndex) {
      replica_ports.push_back(controller_port_ids_[i].GetP4rtEncoding());
    }
  }
  return replica_ports;
}

// Program L3 Admit table for the given mac-address.
absl::Status InstallL3Admit(pdpi::P4RuntimeSession& p4_session,
                            const pdpi::IrP4Info& ir_p4info,
                            const L3AdmitOptions& options) {
  p4::v1::WriteRequest write_request;
  ASSIGN_OR_RETURN(
      *write_request.add_updates(),
      L3AdmitTableUpdate(ir_p4info, p4::v1::Update::INSERT, options));
  return pdpi::SetMetadataAndSendPiWriteRequest(&p4_session, write_request);
}

// Returns a map of number of packets received per port.
absl::flat_hash_map<std::string, int> CountNumPacketsPerPort(
    absl::Span<const dvaas::Packet> output_packets) {
  absl::flat_hash_map<std::string, int> num_packets_per_port;
  for (const auto& output : output_packets) {
    num_packets_per_port[output.port()]++;
  }
  return num_packets_per_port;
}

// Generates a multicast packet.
absl::StatusOr<packetlib::Packet> GenerateMulticastPacket() {
  std::string packet_hex =
      "01005e01010100000000007b08004528005c000000002011b66201020304e00000010929"
      "11d700485c7a6669656c643d49505f44535420697076343d3120656e6361707065643d30"
      "20696e6e65725f697076343d302064656361703d302e2e2e2e2e2e2e2e2e2e2e2e2e";
  return packetlib::ParsePacket(absl::HexStringToBytes(packet_hex));
}

// Sends N packets from the control switch to sut at a rate of packets_rate
// packets/sec.
absl::Status SendNPacketsToSut(int num_packets,
                               absl::Span<const pins_test::P4rtPortId> port_ids,
                               const pdpi::IrP4Info& ir_p4info,
                               pdpi::P4RuntimeSession& p4_session,
                               int packets_rate) {
  LOG(INFO) << "Starting to send " << num_packets << " packets at a rate of "
            << packets_rate << "packets per second.";
  const absl::Time start_time = absl::Now();
  for (int i = 0; i < num_packets; i++) {
    // Rate limit to "packets_rate" packets per second.
    auto earliest_send_time =
        start_time + (i * absl::Seconds(1) / packets_rate);
    absl::SleepFor(earliest_send_time - absl::Now());
    pins_test::P4rtPortId port = port_ids[kDefaultInputPortIndex];

    ASSIGN_OR_RETURN(packetlib::Packet packet, GenerateMulticastPacket());
    ASSIGN_OR_RETURN(std::string raw_packet, SerializePacket(packet));
    RETURN_IF_ERROR(InjectEgressPacket(port.GetP4rtEncoding(), raw_packet,
                                       ir_p4info, &p4_session,
                                       /*packet_delay=*/std::nullopt));
  }

  LOG(INFO) << "Sent " << num_packets << " packets in "
            << (absl::Now() - start_time) << ".";
  return absl::OkStatus();
}

bool HandleStreamMessage(const pdpi::IrP4Info& ir_p4info,
                         thinkit::MirrorTestbed* testbed,
                         const p4::v1::StreamMessageResponse& pi_response,
                         TestData* test_data) {
  absl::MutexLock lock(&test_data->mutex);
  sai::StreamMessageResponse pd_response;
  if (absl::Status status = pdpi::PiStreamMessageResponseToPd(
          ir_p4info, pi_response, &pd_response);
      !status.ok()) {
    ADD_FAILURE() << " PacketIn PI to PD failed: " << status;
    return false;
  }
  if (!pd_response.has_packet()) {
    LOG(WARNING) << " Received unexpected stream message (expected packet in): "
                 << pd_response.DebugString();
    return false;
  }
  absl::string_view raw_packet = pd_response.packet().payload();
  dvaas::Packet packet;
  packet.set_port(pd_response.packet().metadata().ingress_port());
  packet.set_hex(absl::BytesToHexString(raw_packet));
  *packet.mutable_parsed() = packetlib::ParsePacket(raw_packet);
  std::string key = packet.parsed().payload();
  if (!test_data->input_output_per_packet.contains(key)) {
    LOG(WARNING) << "Unexpected Packet: " << packet.DebugString();
    absl::Status log_to_file = testbed->Environment().AppendToTestArtifact(
        "control_unexpected_packet_ins.pb.txt",
        absl::StrCat(packet.DebugString(), "\n"));
    LOG_IF(WARNING, !log_to_file.ok())
        << "Could not write to file: " << log_to_file;
    test_data->total_invalid_packets_received += 1;
    return false;
  }
  test_data->input_output_per_packet[key].output.push_back(packet);
  test_data->total_packets_received += 1;
  return true;
}

absl::Status InstallVlanMembership(pdpi::P4RuntimeSession& switch_session,
                                   const std::vector<std::string>& ports) {
  sai::EntryBuilder entry_builder;
  entry_builder.AddVlanEntry(kVlanIdStr);
  for (int r = 0; r < ports.size(); ++r) {
    entry_builder.AddVlanMembershipEntry(kVlanIdStr, ports[r],
                                         sai::VlanTaggingMode::kUntagged);
  }
  return entry_builder.LogPdEntries().InstallDedupedEntities(switch_session);
}

absl::Status InstallMulticastRitfs(pdpi::P4RuntimeSession& switch_session,
                                   const std::vector<std::string>& ports) {
  std::vector<p4::v1::Entity> entities;
  sai::EntryBuilder entry_builder;
  for (int r = 0; r < ports.size(); ++r) {
    entry_builder.AddMrifEntryRewritingSrcMacAndVlanId(
        ports[r], kMulticastInstance,
        netaddr::MacAddress(0x00, 0x20, 0x30, 0x40, 0x50, 0x60), kVlanId);
  }
  return entry_builder.LogPdEntries().InstallDedupedEntities(switch_session);
}

absl::Status InstallMulticastGroup(pdpi::P4RuntimeSession& switch_session,
                                   absl::string_view default_replica_port,
                                   const std::vector<std::string>& ports) {
  sai::EntryBuilder entry_builder;
  std::vector<sai::BackupReplica> backup_replicas;
  for (int r = 1; r < ports.size(); ++r) {
    backup_replicas.push_back(sai::BackupReplica{
        .egress_port = ports[r], .instance = kMulticastInstance});
  }
  std::vector<sai::Replica> sai_replicas;
  sai_replicas.push_back(sai::Replica{.egress_port = ports[0],
                                      .instance = kMulticastInstance,
                                      .backup_replicas = backup_replicas});
  sai_replicas.push_back(
      sai::Replica{.egress_port = std::string(default_replica_port),
                   .instance = kMulticastInstance});
  entry_builder.AddMulticastGroupEntry(kMulticastGroupId, sai_replicas);
  return entry_builder.LogPdEntries().InstallDedupedEntities(switch_session);
}

absl::Status InstallMulticastRoute(pdpi::P4RuntimeSession& switch_session) {
  sai::EntryBuilder entry_builder;
  entry_builder.AddMulticastRoute(kVrfId, kMulticastDstIpv4, kMulticastGroupId);
  return entry_builder.LogPdEntries().InstallDedupedEntities(switch_session);
}

}  // namespace

absl::Status MulticastFallbackGroupTestFixture::SetUpSut(
    const pdpi::IrP4Info& ir_p4info) {
  // Create default VRF for test.
  ASSIGN_OR_RETURN(
      p4::v1::Entity pi_entity,
      pdpi::PdTableEntryToPiEntity(
          ir_p4info, gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
                         R"pb(
                           vrf_table_entry {
                             match { vrf_id: "$0" }
                             action { no_action {} }
                           })pb",
                         kVrfId))));
  RETURN_IF_ERROR(pdpi::InstallPiTableEntry(sut_p4_session_.get(),
                                            pi_entity.table_entry()));

  // Set default VRF for all packets.
  ASSIGN_OR_RETURN(
      pi_entity,
      pdpi::PdTableEntryToPiEntity(
          ir_p4info, gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
                         R"pb(
                           acl_pre_ingress_table_entry {
                             match {}                             # Wildcard match
                             action { set_vrf { vrf_id: "$0" } }  # Default vrf
                             priority: 1129
                           })pb",
                         kVrfId))));

  RETURN_IF_ERROR(pdpi::InstallPiTableEntry(sut_p4_session_.get(),
                                            pi_entity.table_entry()));

  std::vector<std::string> replica_ports_with_default_port = replica_ports_;
  replica_ports_with_default_port.push_back(
      controller_port_ids_[kDefaultReplicaPortIndex].GetP4rtEncoding());
  std::vector<std::string> replica_ports_with_default_and_input_port =
      replica_ports_with_default_port;
  replica_ports_with_default_port.push_back(
      controller_port_ids_[kDefaultInputPortIndex].GetP4rtEncoding());

  // Programs the required vlan, vlan members, and multicast ritfs.
  RETURN_IF_ERROR(InstallVlanMembership(
      *sut_p4_session_, replica_ports_with_default_and_input_port));
  RETURN_IF_ERROR(
      InstallMulticastRitfs(*sut_p4_session_, replica_ports_with_default_port));

  // Programs the multicast group.
  RETURN_IF_ERROR(InstallMulticastGroup(
      *sut_p4_session_,
      controller_port_ids_[kDefaultReplicaPortIndex].GetP4rtEncoding(),
      replica_ports_));

  // Programs L3 admit.
  RETURN_IF_ERROR(InstallL3Admit(
      *sut_p4_session_, ir_p4info,
      L3AdmitOptions{
          .priority = 2070,
          .dst_mac = std ::make_pair(pins::GetIthDstMac(0).ToString(),
                                     "FF:FF:FF:FF:FF:FF"),
      }));

  // Programs multicast routing.
  RETURN_IF_ERROR(InstallMulticastRoute(*sut_p4_session_));

  return absl::OkStatus();
}

void MulticastFallbackGroupTestFixture::SetUp() {
  GetParam().testbed->SetUp();
  thinkit::MirrorTestbed& testbed = GetParam().testbed->GetMirrorTestbed();

  ASSERT_OK(testbed.Environment().StoreTestArtifact(
      "p4info.pb.txt", GetParam().p4_info.DebugString()));

  // Setup SUT & control switch.
  ASSERT_OK_AND_ASSIGN(
      sut_p4_session_,
      pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
          testbed.Sut(), GetParam().gnmi_config, GetParam().p4_info));
  ASSERT_OK_AND_ASSIGN(
      control_p4_session_,
      pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
          testbed.ControlSwitch(), GetParam().gnmi_config, GetParam().p4_info));

  // Create GNMI stub for admin operations.
  ASSERT_OK_AND_ASSIGN(sut_gnmi_stub_, testbed.Sut().CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(control_gnmi_stub_,
                       testbed.ControlSwitch().CreateGnmiStub());

  // Store the original control switch gNMI interface config before changing it.
  ASSERT_OK_AND_ASSIGN(original_control_interfaces_,
                       pins_test::GetInterfacesAsProto(
                           *control_gnmi_stub_, gnmi::GetRequest::CONFIG));

  // Ensures that the SUT and Control Switch are set up with the same
  // P4rtPortIds for the connected interfaces.
  ASSERT_OK(pins_test::MirrorSutP4rtPortIdConfigToControlSwitch(
      GetParam().testbed->GetMirrorTestbed()));

  // Store GNMI config for debugging.
  ASSERT_OK_AND_ASSIGN(std::string sut_gnmi_config,
                       pins_test::GetGnmiConfig(*sut_gnmi_stub_));
  ASSERT_OK(testbed.Environment().StoreTestArtifact("sut_gnmi_config.txt",
                                                    sut_gnmi_config));

  ASSERT_OK_AND_ASSIGN(ir_p4info_, pdpi::CreateIrP4Info(GetParam().p4_info));

  ASSERT_OK_AND_ASSIGN(
      controller_port_ids_,
      pins_test::GetMatchingP4rtPortIds(*sut_gnmi_stub_,
                                        pins_test::IsEnabledEthernetInterface));
  ASSERT_OK_AND_ASSIGN(replica_ports_, GetReplicaPorts(kNumReplicaPortsForTest,
                                                       controller_port_ids_));

  ASSERT_OK(SetUpSut(ir_p4info_));
  ASSERT_OK(SetUpControlSwitch(*control_p4_session_));

  // Create test data entry.
  ASSERT_OK_AND_ASSIGN(packetlib::Packet packet, GenerateMulticastPacket());
  test_config_key_ = packet.payload();
  {
    absl::MutexLock lock(&test_data_.mutex);
    test_data_.input_output_per_packet[test_config_key_] = TestInputOutput{};
  }
}

void MulticastFallbackGroupTestFixture::TearDown() {
  thinkit::MirrorTestbedInterface& testbed = *GetParam().testbed;

  // Do some general cleanup for control switch.
  if (control_p4_session_ != nullptr) {
    EXPECT_OK(pdpi::ClearEntities(*control_p4_session_.get()));
  }
  if (control_gnmi_stub_) {
    ASSERT_OK_AND_ASSIGN(const auto port_name_per_port_id,
                         pins_test::GetPortNamePerPortId(*control_gnmi_stub_));
    // Restore the admin state to UP.
    for (const auto& [port_id, name] : port_name_per_port_id) {
      EXPECT_OK(pins_test::SetInterfaceEnabledState(*control_gnmi_stub_, name,
                                                    /*enabled=*/true));
    }
    // Restore the original control switch gNMI interface config's P4RT IDs.
    ASSERT_OK(pins_test::SetInterfaceP4rtIds(*control_gnmi_stub_,
                                             original_control_interfaces_));
  }

  // Clear SUT table entries.
  if (sut_p4_session_ != nullptr) {
    EXPECT_OK(pdpi::ClearEntities(*sut_p4_session_.get()));
    EXPECT_OK(sut_p4_session_->Finish());
  }

  testbed.TearDown();
}

namespace {

// Measure multicast fallback duration by sending packets to a port and then
// setting the port to down, and then measure the number of packets received by
// the control switch to calculate the multicast fallback rate.
TEST_P(MulticastFallbackGroupTestFixture, MeasureMulticastFallbackDuration) {
  thinkit::TestEnvironment& environment =
      GetParam().testbed->GetMirrorTestbed().Environment();
  environment.SetTestCaseID("fa811b07-0c6a-4b9d-a6e0-c9c340cd915f");
  if (!GetParam().check_and_export_duration.has_value()) {
    GTEST_SKIP() << "Multicast fallback duration test skipped because threshold"
                    "and export vector is not defined";
  }

  // Get port_name to port id mapping for the control switch.
  ASSERT_OK_AND_ASSIGN(const auto port_name_per_port_id,
                       pins_test::GetPortNamePerPortId(*control_gnmi_stub_));
  // Get port_name for the primary replica.
  ASSERT_OK_AND_ASSIGN(
      const auto& port_name,
      gutil::FindOrStatus(port_name_per_port_id, replica_ports_[0]));

  int64_t total_packets_sent;
  int64_t total_packets_received;
  int64_t expected_receive_packets;
  int64_t total_packets_lost;
  double multicast_fallback_duration;

  // Verify the oper status is reflected on the SUT.
  ASSERT_OK(pins_test::VerifyInterfaceOperState(*sut_gnmi_stub_, port_name,
                                                pins_test::OperStatus::kUp));

  // Start a new thread to send packets to the SUT. This is to ensure that
  // the packets are being sent to the SUT while the port changes state.
  std::thread send_packets_thread([&]() {
    ASSERT_OK(SendNPacketsToSut(kNumTestPacketsForMulticastFallback,
                                controller_port_ids_, ir_p4info_,
                                *control_p4_session_, kPacketRateInSeconds));
  });

  // Wait for 25% of the time to change the port state to DOWN.
  double delay_before_multicast_fallback =
      (kNumTestPacketsForMulticastFallback / kPacketRateInSeconds) * 0.25;
  LOG(INFO) << "Waiting for " << delay_before_multicast_fallback
            << " seconds to change the port state to DOWN";
  absl::SleepFor(absl::Seconds(delay_before_multicast_fallback));
  // Set the selected port to new state.
  ASSERT_OK(pins_test::SetInterfaceEnabledState(*control_gnmi_stub_, port_name,
                                                /*enabled=*/false));
  // Verify the oper status is reflected on the SUT.
  LOG(INFO) << "Setting port " << port_name << " to state DOWN";
  ASSERT_OK(pins_test::VerifyInterfaceOperState(*sut_gnmi_stub_, port_name,
                                                pins_test::OperStatus::kDown));
  // Join the thread to ensure that all packets are sent to the SUT after the
  // port is changed to new state.
  send_packets_thread.join();

  test_data_.ClearReceivedPackets();
  test_data_.total_packets_sent = kNumTestPacketsForMulticastFallback;
  // Wait for packets from the SUT to arrive. Since some packets are expected
  // to be lost due to the port being in new state, we don't verify the number
  // of packets received.
  absl::Status status = control_p4_session_->HandleNextNStreamMessages(
      [&](const p4::v1::StreamMessageResponse& message) {
        return HandleStreamMessage(ir_p4info_,
                                   &GetParam().testbed->GetMirrorTestbed(),
                                   message, &test_data_);
      },
      2 * kNumTestPacketsForMulticastFallback, kDurationToWaitForPackets);
  if (!status.ok() && !absl::IsDeadlineExceeded(status)) {
    FAIL() << "Failed to receive packets from SUT: " << status;
  }

  {
    absl::MutexLock lock(&test_data_.mutex);
    TestInputOutput& test =
        test_data_.input_output_per_packet[test_config_key_];

    total_packets_sent = test_data_.total_packets_sent;
    total_packets_received = test.output.size();
    // There are two replicas. The received packet count is double the sent
    // packet count.
    expected_receive_packets = 2 * total_packets_sent;
    total_packets_lost = expected_receive_packets - total_packets_received;
    multicast_fallback_duration =
        1000 * total_packets_lost / kPacketRateInSeconds;
  }

  LOG(INFO) << "Multicast fallback packet rate(pps): " << kPacketRateInSeconds
            << "\n"
            << "Total Packets sent: " << total_packets_sent << "\n"
            << "Total Packets received: " << total_packets_received << "\n"
            << "Total Packets lost: " << total_packets_lost << "\n"
            << "Multicast fallback duration: " << multicast_fallback_duration
            << " msecs.";

  LOG(INFO) << "Checking multicast fallback duration against "
               "threshold and exporting data to perfgate storage";
  ASSERT_OK((*GetParam().check_and_export_duration)(
      GetParam().testbed->GetMirrorTestbed().Sut().ChassisName(),
      absl::Milliseconds(multicast_fallback_duration)));

  // Bring the port back to UP state.
  ASSERT_OK(pins_test::SetInterfaceEnabledState(*control_gnmi_stub_, port_name,
                                                /*enabled=*/true));
  ASSERT_OK(pins_test::VerifyInterfaceOperState(*sut_gnmi_stub_, port_name,
                                                pins_test::OperStatus::kUp));
}

// Bring up primary replicas to trigger multicast restore action.
// Verify that there is no duplicate packets sent on one replica.
TEST_P(MulticastFallbackGroupTestFixture, VerifyMulticastRestoreAction) {
  thinkit::TestEnvironment& environment =
      GetParam().testbed->GetMirrorTestbed().Environment();
  environment.SetTestCaseID("a4f484cc-df55-455c-b008-d3753eaa1507");

  // Get port_name to port id mapping for the control switch.
  ASSERT_OK_AND_ASSIGN(const auto port_name_per_port_id,
                       pins_test::GetPortNamePerPortId(*control_gnmi_stub_));
  // Get port_name for the primary replica.
  ASSERT_OK_AND_ASSIGN(
      const auto& port_name,
      gutil::FindOrStatus(port_name_per_port_id, replica_ports_[0]));

  int64_t total_packets_sent;
  int64_t total_packets_received;

  // Bring down the primary replica.
  ASSERT_OK(pins_test::SetInterfaceEnabledState(*control_gnmi_stub_, port_name,
                                                /*enabled=*/false));
  ASSERT_OK(pins_test::VerifyInterfaceOperState(*sut_gnmi_stub_, port_name,
                                                pins_test::OperStatus::kDown));
  absl::SleepFor(absl::Seconds(1));

  // Start a new thread to send packets to the SUT. This is to ensure that
  // the packets are being sent to the SUT while the port changes state.
  std::thread send_packets_thread([&]() {
    ASSERT_OK(SendNPacketsToSut(kNumTestPacketsForMulticastFallback,
                                controller_port_ids_, ir_p4info_,
                                *control_p4_session_, kPacketRateInSeconds));
  });

  // Wait for 25% of the time to change the port state to UP.
  double delay_before_multicast_fallback =
      (kNumTestPacketsForMulticastFallback / kPacketRateInSeconds) * 0.25;
  LOG(INFO) << "Waiting for " << delay_before_multicast_fallback
            << " seconds to change the port state to UP";
  absl::SleepFor(absl::Seconds(delay_before_multicast_fallback));
  // Set the primary replica to UP state.
  ASSERT_OK(pins_test::SetInterfaceEnabledState(*control_gnmi_stub_, port_name,
                                                /*enabled=*/true));
  ASSERT_OK(pins_test::VerifyInterfaceOperState(*sut_gnmi_stub_, port_name,
                                                pins_test::OperStatus::kUp));
  // Join the thread to ensure that all packets are sent to the SUT after the
  // port is changed to new state.
  send_packets_thread.join();

  test_data_.ClearReceivedPackets();
  test_data_.total_packets_sent = kNumTestPacketsForMulticastFallback;
  // Wait for packets from the SUT to arrive.
  // It is expected to receive exactly 2 times the number of packets sent.
  // No duplicate packets are allowed. And hence we will try to receive 3 times
  // the number of packets sent to capture the duplicate packet failure.
  absl::Status status = control_p4_session_->HandleNextNStreamMessages(
      [&](const p4::v1::StreamMessageResponse& message) {
        return HandleStreamMessage(ir_p4info_,
                                   &GetParam().testbed->GetMirrorTestbed(),
                                   message, &test_data_);
      },
      3 * kNumTestPacketsForMulticastFallback, kDurationToWaitForPackets);
  if (!status.ok() && !absl::IsDeadlineExceeded(status)) {
    FAIL() << "Failed to receive packets from SUT: " << status;
  }

  {
    absl::MutexLock lock(&test_data_.mutex);
    TestInputOutput& test =
        test_data_.input_output_per_packet[test_config_key_];

    total_packets_sent = test_data_.total_packets_sent;
    total_packets_received = test.output.size();
  }

  ASSERT_EQ(2 * total_packets_sent, total_packets_received)
      << "Packet loss or duplicate packets received";
}

// Bring down/up ports and verify traffic is distributed to the first up port in
// each replica.
TEST_P(MulticastFallbackGroupTestFixture, VerifyBasicMulticastFallbackAction) {
  thinkit::TestEnvironment& environment =
      GetParam().testbed->GetMirrorTestbed().Environment();
  environment.SetTestCaseID("f9815b85-8bdf-451c-91b0-0441f306ce47");

  // Get port_name to port id mapping for the control switch.
  ASSERT_OK_AND_ASSIGN(const auto port_name_per_port_id,
                       pins_test::GetPortNamePerPortId(*control_gnmi_stub_));
  // Get port_name for the primary and secondary replica.
  ASSERT_OK_AND_ASSIGN(
      const auto& primary_replica_port_name,
      gutil::FindOrStatus(port_name_per_port_id, replica_ports_[0]));
  ASSERT_OK_AND_ASSIGN(
      const auto& secondary_replica_port_name,
      gutil::FindOrStatus(port_name_per_port_id, replica_ports_[1]));

  struct port_state {
    std::string name;
    pins_test::OperStatus state;
  };
  struct test_case {
    std::vector<port_state> port_states;
    std::vector<std::string> expected_active_replica_ports;
  };
  std::vector<test_case> tests = {
      // Bring down the primary replica. Expect the traffic is sent to the first
      // backup replica.
      {
          std::vector<port_state>{
              {primary_replica_port_name, pins_test::OperStatus::kDown},
              {secondary_replica_port_name, pins_test::OperStatus::kUp}},
          std::vector<std::string>{
              replica_ports_[1],
              controller_port_ids_[kDefaultReplicaPortIndex].GetP4rtEncoding()},
      },
      // Bring down both the primary replica and the first backup replica.
      // Expect the traffic is sent to the second backup replica.
      {
          std::vector<port_state>{
              {primary_replica_port_name, pins_test::OperStatus::kDown},
              {secondary_replica_port_name, pins_test::OperStatus::kDown}},
          std::vector<std::string>{
              replica_ports_[2],
              controller_port_ids_[kDefaultReplicaPortIndex].GetP4rtEncoding()},
      },
      // Bring down the first backup replica. Expect the traffic is sent to the
      // primary replica.
      {
          std::vector<port_state>{
              {primary_replica_port_name, pins_test::OperStatus::kUp},
              {secondary_replica_port_name, pins_test::OperStatus::kDown}},
          std::vector<std::string>{
              replica_ports_[0],
              controller_port_ids_[kDefaultReplicaPortIndex].GetP4rtEncoding()},
      },
  };

  for (const auto& test_case : tests) {
    for (const auto& port_state : test_case.port_states) {
      ASSERT_OK(pins_test::SetInterfaceEnabledState(
          *control_gnmi_stub_, port_state.name,
          port_state.state == pins_test::OperStatus::kUp));
      ASSERT_OK(pins_test::VerifyInterfaceOperState(
          *sut_gnmi_stub_, port_state.name, port_state.state));
    }
    absl::SleepFor(absl::Seconds(1));
    test_data_.ClearReceivedPackets();
    ASSERT_OK(SendNPacketsToSut(kNumTestPacketsForMulticastFallback,
                                controller_port_ids_, ir_p4info_,
                                *control_p4_session_, kPacketRateInSeconds));
    test_data_.total_packets_sent = kNumTestPacketsForMulticastFallback;
    ASSERT_OK(control_p4_session_->HandleNextNStreamMessages(
        [&](const p4::v1::StreamMessageResponse& message) {
          return HandleStreamMessage(ir_p4info_,
                                     &GetParam().testbed->GetMirrorTestbed(),
                                     message, &test_data_);
        },
        2 * kNumTestPacketsForMulticastFallback, kDurationToWaitForPackets));
    {
      absl::MutexLock lock(&test_data_.mutex);
      TestInputOutput& test =
          test_data_.input_output_per_packet[test_config_key_];
      EXPECT_EQ(test.output.size(), 2 * test_data_.total_packets_sent)
          << "Mismatch in expected: " << 2 * test_data_.total_packets_sent
          << " and actual: " << test.output.size() << "packets received";
      auto num_packets_per_port = CountNumPacketsPerPort(test.output);
      for (const auto& expected_active_replica_port :
           test_case.expected_active_replica_ports) {
        ASSERT_EQ(num_packets_per_port[expected_active_replica_port],
                  kNumTestPacketsForMulticastFallback);
      }
    }
  }

  // Restore the port state to UP.
  ASSERT_OK(pins_test::SetInterfaceEnabledState(
      *control_gnmi_stub_, primary_replica_port_name, /*enabled=*/true));
  ASSERT_OK(pins_test::VerifyInterfaceOperState(
      *sut_gnmi_stub_, primary_replica_port_name, pins_test::OperStatus::kUp));
  ASSERT_OK(pins_test::SetInterfaceEnabledState(
      *control_gnmi_stub_, secondary_replica_port_name, /*enabled=*/true));
  ASSERT_OK(pins_test::VerifyInterfaceOperState(*sut_gnmi_stub_,
                                                secondary_replica_port_name,
                                                pins_test::OperStatus::kUp));
}

}  // namespace
}  // namespace pins
