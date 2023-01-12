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

#include "tests/forwarding/hash_testfixture.h"

#include <memory>
#include <optional>
#include <string>
#include <thread> // NOLINT
#include <utility>
#include <vector>

#include "absl/base/thread_annotations.h"
#include "absl/container/btree_set.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/node_hash_map.h"
#include "absl/functional/bind_front.h"
#include "absl/meta/type_traits.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/synchronization/mutex.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/utility/utility.h"
#include "glog/logging.h"
#include "gutil/proto_matchers.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/p4rt/p4rt_port.h"
#include "lib/validator/validator_lib.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_pdpi/pd.h"
#include "re2/re2.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "system/system.pb.h"
#include "tests/forwarding/group_programming_util.h"
#include "tests/forwarding/packet_test_util.h"
#include "tests/forwarding/util.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "tests/thinkit_sanity_tests.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/mirror_testbed_fixture.h"
#include "thinkit/switch.h"
#include "thinkit/test_environment.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace pins_test {

namespace {

using ::gutil::EqualsProto;
using ::pins::PacketField;
using ::pins::TestConfiguration;
using ::testing::Matches;

// The minimum number of ports needed to perform the test.
constexpr int kMinimumMembersForTest = 3;

// Average interval between packet injections.
constexpr absl::Duration kPacketInterval = absl::Milliseconds(10); // 100pps

// P4TableEntry templates needed to set up hashing.
constexpr absl::string_view kAddVrfTableEntry = R"pb(
  vrf_table_entry {
    match { vrf_id: "vrf-80" }
    action { no_action {} }
  })pb";

constexpr absl::string_view kSetVrfTableEntry = R"pb(
  acl_pre_ingress_table_entry {
    match {}
    action { set_vrf { vrf_id: "vrf-80" } }
    priority: 1129
  })pb";

constexpr absl::string_view kIpv4DefaultRouteEntry = R"pb(
  ipv4_table_entry {
    match { vrf_id: "vrf-80" }
    action { set_wcmp_group_id { wcmp_group_id: "group-1" } }
  })pb";

constexpr absl::string_view kIpv6DefaultRouteEntry = R"pb(
  ipv6_table_entry {
    match { vrf_id: "vrf-80" }
    action { set_wcmp_group_id { wcmp_group_id: "group-1" } }
  })pb";

constexpr absl::string_view kL3AdmitUnicastTableEntry = R"pb(
  l3_admit_table_entry {
    match { dst_mac { value: "00:00:00:00:00:00" mask: "01:00:00:00:00:00" } }
    action { admit_to_l3 {} }
    priority: 2070
  })pb";

// Set the payload for a HashTest packet that contains an identifier
// and the packet index.
void SetPayload(packetlib::Packet &packet, int index) {
  packet.set_payload(
      absl::Substitute("HashAlgPacket($0): $1", index, packet.payload()));
}

// Return the index of a HashTest packet or an error if parsing fails.
absl::StatusOr<int> GetPacketIndex(const packetlib::Packet &packet) {
  static const LazyRE2 kIndexRegex = {R"re(^HashAlgPacket\(([0-9]*)\))re"};
  int index;
  if (!RE2::PartialMatch(packet.payload(), *kIndexRegex, &index)) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Packet payload does not match expected format: "
              "HashAlgPacket(<index>): <original_payload>. ";
  }
  return index;
}

// Log a set of packets as a single artifact for debugging.
void LogPackets(thinkit::TestEnvironment &environment,
                const std::vector<packetlib::Packet> &packets,
                absl::string_view artifact_name) {
  std::string packet_log;
  for (const auto &packet : packets) {
    absl::StrAppend(&packet_log, packet.ShortDebugString(), "\n");
  }
  ASSERT_OK(environment.StoreTestArtifact(absl::StrCat(artifact_name, ".txt"),
                                          packet_log));
}

// Initialize the testbed for the test.
//   Push gNMI config.
//   Add the trap rule to the control switch.
void InitializeTestbed(thinkit::MirrorTestbed &testbed,
                       const p4::config::v1::P4Info &p4info) {
  // Wait for ports to come up before the test. We don't need all the ports to
  // be up, but it helps with reproducibility. We're using a short timeout (1
  // minute) so the impact is small if the testbed doesn't bring up every port.
  if (auto all_interfaces_up_status = WaitForCondition(
          AllPortsUp, absl::Minutes(1), testbed.Sut(), /*with_healthz=*/false);
      !all_interfaces_up_status.ok()) {
    LOG(WARNING) << "Some ports are down at the start of the test. Continuing "
                 << "with only the UP ports. " << all_interfaces_up_status;
    // Collect port debug data but don't fail the test.
    absl::Status tmp_status = AllPortsUp(testbed.Sut(), /*with_healthz=*/true);
    LOG_IF(WARNING, !tmp_status.ok()) << "SUT Ports Up Check: " << tmp_status;
    tmp_status = AllPortsUp(testbed.ControlSwitch(), /*with_healthz=*/true);
    LOG_IF(WARNING, !tmp_status.ok())
        << "Control Ports Up Check: " << tmp_status;
  }

  // Setup control switch P4 state.
  LOG(INFO) << "Initializing forwarding pipeline for control switch.";
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<pdpi::P4RuntimeSession> control_p4_session,
      ConfigureSwitchAndReturnP4RuntimeSession(testbed.ControlSwitch(),
                                               /*gnmi_config=*/std::nullopt,
                                               p4info));

  // Trap all packets on control switch.
  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info ir_p4info, pdpi::CreateIrP4Info(p4info));
  ASSERT_OK_AND_ASSIGN(p4::v1::TableEntry punt_all_pi_entry,
                       pdpi::PartialPdTableEntryToPiTableEntry(
                           ir_p4info, gutil::ParseProtoOrDie<sai::TableEntry>(
                                          R"pb(
                acl_ingress_table_entry {
                  match {}                                  # Wildcard match.
                  action { acl_trap { qos_queue: "0x7" } }  # Action: punt.
                  priority: 1                               # Highest priority.
                  meter_config {
                    bytes_per_second: 987654321  # ~ 1 GB
                    burst_bytes: 987654321       # ~ 1 GB
                  }
                }
              )pb")));
  ASSERT_OK(
      pdpi::InstallPiTableEntry(control_p4_session.get(), punt_all_pi_entry));
}

// Receive and record a single packet.
void ReceivePacket(thinkit::MirrorTestbed *testbed,
                   const pdpi::IrP4Info *ir_p4info,
                   p4::v1::StreamMessageResponse pi_response,
                   HashTest::TestData *test_data) {
  sai::StreamMessageResponse pd_response;
  ASSERT_OK(
      pdpi::PiStreamMessageResponseToPd(*ir_p4info, pi_response, &pd_response))
      << " PacketIn PI to PD failed: ";
  if (!pd_response.has_packet()) {
    LOG(WARNING) << "Ignoring unexpected stream message for packet in: "
                 << pd_response.DebugString();
  }

  absl::string_view raw_packet = pd_response.packet().payload();
  packetlib::Packet packet = packetlib::ParsePacket(raw_packet);
  test_data->AddPacket(pd_response.packet().metadata().target_egress_port(),
                       std::move(packet));
}

// Thread function to receive and record test packets.
void ReceivePacketsUntilStreamIsClosed(
    thinkit::MirrorTestbed *testbed, const pdpi::IrP4Info *ir_p4info,
    pdpi::P4RuntimeSession *control_p4_session, HashTest::TestData *test_data) {
  p4::v1::StreamMessageResponse pi_response;
  // The only way to break out of this loop is for the stream channel to
  // be closed. gRPC does not support selecting on both stream Read and
  // fiber Cancel.
  while (control_p4_session->StreamChannelRead(pi_response)) {
    ReceivePacket(testbed, ir_p4info, pi_response, test_data);
  }
}

// Send a test packet to the SUT.
void SendPacket(const pdpi::IrP4Info &ir_p4info, packetlib::Packet packet,
                pdpi::P4RuntimeSession &control_p4_session,
                P4rtPortId ingress_port) {
  SCOPED_TRACE(
      absl::StrCat("Failed to inject packet ", packet.ShortDebugString()));
  ASSERT_OK_AND_ASSIGN(std::string raw_packet, SerializePacket(packet));
  ASSERT_OK(pins::InjectEgressPacket(ingress_port.GetP4rtEncoding(), raw_packet,
                                     ir_p4info, &control_p4_session,
                                     kPacketInterval));
}

// Send test packets to the SUT. Packets are generated based on the test config.
void SendPackets(const pdpi::IrP4Info &ir_p4info, int num_packets,
                 const TestConfiguration &test_config,
                 pdpi::P4RuntimeSession &control_p4_session,
                 P4rtPortId ingress_port,
                 std::vector<packetlib::Packet> &injected_packets) {
  // Try to generate one packet first to see if the config is valid.
  {
    ASSERT_OK_AND_ASSIGN(packetlib::Packet packet,
                         pins::GenerateIthPacket(test_config, 0));
    ASSERT_OK(SerializePacket(packet).status())
        << "Failed to generate raw packet for " << packet.ShortDebugString();
  }
  for (int i = 0; i < num_packets; ++i) {
    ASSERT_OK_AND_ASSIGN(packetlib::Packet packet,
                         pins::GenerateIthPacket(test_config, i));
    SetPayload(packet, i);
    injected_packets.push_back(packet);
    // Don't check errors from SendPacket. Continue sending packets.
    SendPacket(ir_p4info, packet, control_p4_session, ingress_port);
  }
}

// Retrieve the current known port IDs from the switch. Must use numerical port
// id names.
void GetPortIds(thinkit::Switch &target, std::vector<std::string> &interfaces,
                absl::btree_set<P4rtPortId> &port_ids) {
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, target.CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(const auto interface_id_map,
                       GetAllInterfaceNameToPortId(*sut_gnmi_stub));
  ASSERT_OK_AND_ASSIGN(const auto up_interfaces,
                       GetUpInterfacesOverGnmi(*sut_gnmi_stub));

  for (const auto &interface_name : up_interfaces) {
    ASSERT_THAT(interface_id_map,
                testing::Contains(testing::Key(interface_name)));
    ASSERT_OK_AND_ASSIGN(
        P4rtPortId port_id,
        P4rtPortId::MakeFromP4rtEncoding(interface_id_map.at(interface_name)));
    port_ids.insert(port_id);
    interfaces.push_back(interface_name);
  }
}

std::string PacketFieldName(PacketField field) {
  switch (field) {
  case PacketField::kEthernetSrc:
    return "EthernetSrc";
  case PacketField::kEthernetDst:
    return "EthernetDst";
  case PacketField::kIpSrc:
    return "IpSrc";
  case PacketField::kIpDst:
    return "IpDst";
  case PacketField::kHopLimit:
    return "HopLimit";
  case PacketField::kDscp:
    return "Dscp";
  case PacketField::kFlowLabelLower16:
    return "FlowLabelLower16";
  case PacketField::kFlowLabelUpper4:
    return "FlowLabelUpper4";
  case PacketField::kInnerIpSrc:
    return "InnerIpSrc";
  case PacketField::kInnerIpDst:
    return "InnerIpDst";
  case PacketField::kInnerHopLimit:
    return "InnerHopLimit";
  case PacketField::kInnerDscp:
    return "InnerDscp";
  case PacketField::kInnerFlowLabelLower16:
    return "InnerFlowLabelLower16";
  case PacketField::kInnerFlowLabelUpper4:
    return "InnerFlowLabelUpper4";
  case PacketField::kL4SrcPort:
    return "L4SrcPort";
  case PacketField::kL4DstPort:
    return "L4DstPort";
  case PacketField::kInputPort:
    return "InputPort";
  }
}

std::string TestConfigName(const TestConfiguration &config) {
  if (config.encapped) {
    return absl::Substitute(
        "$0In$1$2Diff$3", config.inner_ipv4 ? "IPv4" : "IPv6",
        config.ipv4 ? "IPv4" : "IPv6", config.decap ? "Decap" : "",
        PacketFieldName(config.field));
  } else {
    return absl::Substitute("$0Diff$1", config.ipv4 ? "IPv4" : "IPv6",
                            PacketFieldName(config.field));
  }
}

} // namespace

// Return the list of all packet TestConfigurations to be tested. Each
// TestConfiguration should result in a hash difference.
const TestConfigurationMap &HashingTestConfigs() {
  static const auto *const kTestConfigMap = [&]() {
    std::vector<TestConfiguration> test_configs({
        {.field = PacketField::kIpSrc, .ipv4 = true},
        {.field = PacketField::kIpDst, .ipv4 = true},
        {.field = PacketField::kIpSrc, .ipv4 = false},
        {.field = PacketField::kIpDst, .ipv4 = false},
        {.field = PacketField::kFlowLabelLower16, .ipv4 = false},
        {.field = PacketField::kL4SrcPort, .ipv4 = true},
        {.field = PacketField::kL4DstPort, .ipv4 = true},
        {.field = PacketField::kL4SrcPort, .ipv4 = false},
        {.field = PacketField::kL4DstPort, .ipv4 = false},
        // The upper-4 bits should create a hash difference but may not be
        // enough to produce a statistically-sound set.
        // {.field = PacketField::kFlowLabelUpper4, .ipv4 = false},
    });

    auto test_config_map = new TestConfigurationMap();
    for (const auto &config : test_configs) {
      (*test_config_map)[TestConfigName(config)] = config;
    }
    return test_config_map;
  }();
  return *kTestConfigMap;
}

// Return the list of all TestConfig() names.
const std::vector<std::string> &HashingTestConfigNames() {
  static const auto *const kConfigNames = []() {
    auto config_names = new std::vector<std::string>();
    for (const auto &[config_name, test_config] : HashingTestConfigs()) {
      config_names->push_back(config_name);
    }
    return config_names;
  }();
  return *kConfigNames;
}

// Return the list of all packet TestConfigurations to be tested. Each
// TestConfiguration should result in a hash difference.
const TestConfigurationMap &NonHashingTestConfigs() {
  static const auto add_if_valid = [](TestConfiguration config,
                                      TestConfigurationMap &config_map) {
    if (pins::IsValidTestConfiguration(config)) {
      config_map[TestConfigName(config)] = std::move(config);
    }
  };

  static const auto *const kTestConfigs = []() {
    auto *configs = new TestConfigurationMap();
    for (pins::PacketField field : pins::AllPacketFields()) {
      // kFlowLabelUpper4 should produce a hash difference but isn't wide
      // enough to produce a statisticaly-sound result.
      if (field == PacketField::kFlowLabelUpper4)
        continue;
      add_if_valid({.field = field, .ipv4 = true}, *configs);
      add_if_valid({.field = field, .ipv4 = false}, *configs);
    }
    // Erase all the hashing configs.
    for (const auto &test_config_name : HashingTestConfigNames()) {
      configs->erase(test_config_name);
    }
    return configs;
  }();
  return *kTestConfigs;
}

// Return the list of all TestConfig() names.
const std::vector<std::string> &NonHashingTestConfigNames() {
  static const auto *const kConfigNames = []() {
    auto config_names = new std::vector<std::string>();
    for (const auto &[config_name, test_config] : NonHashingTestConfigs()) {
      config_names->push_back(config_name);
    }
    return config_names;
  }();
  return *kConfigNames;
}

void HashTest::TestData::AddPacket(absl::string_view egress_port,
                                   packetlib::Packet packet) {
  absl::StatusOr<int> status_or_index = GetPacketIndex(packet);
  if (status_or_index.ok()) {
    absl::MutexLock lock(&mutex_);
    packets_by_port_[egress_port].insert(*status_or_index);
    received_packets_.push_back({std::string(egress_port), absl::move(packet)});
  } else {
    // Ignore packets that don't match.
    VLOG(1) << "Received unexpected packet: " << packet.ShortDebugString()
            << ". " << status_or_index.status();
  }
}

absl::Status HashTest::TestData::Log(thinkit::TestEnvironment &environment,
                                     absl::string_view artifact_name)
    ABSL_LOCKS_EXCLUDED(mutex_) {
  absl::MutexLock lock(&mutex_);
  std::string packet_log;
  for (const auto &[port, packet] : received_packets_) {
    absl::StrAppend(&packet_log, port, ": ", packet.ShortDebugString(), "\n");
  }
  return environment.StoreTestArtifact(absl::StrCat(artifact_name, ".txt"),
                                       packet_log);
}

void HashTest::SetUp() {
  MirrorTestbedFixture::SetUp();

  ASSERT_NO_FATAL_FAILURE(
      GetPortIds(GetMirrorTestbed().Sut(), interfaces_, port_ids_));
  LOG(INFO) << "Using ports: ["
            << absl::StrJoin(port_ids_, ", ", absl::StreamFormatter()) << "]";
  ASSERT_GE(port_ids_.size(), kMinimumMembersForTest);
}

void HashTest::TearDown() {
  // Clean up flows on the control switch. We're using a non-fatal failure
  // here so we continue cleanup.
  EXPECT_OK(SaveSwitchLogs("teardown_before_table_clear"));
  auto result_or_control_p4_session =
      pdpi::P4RuntimeSession::Create(GetMirrorTestbed().ControlSwitch());
  if (result_or_control_p4_session.ok()) {
    EXPECT_OK(pdpi::ClearTableEntries(result_or_control_p4_session->get()))
        << "failed to clean up control switch P4 entries.";
  } else {
    ADD_FAILURE() << "failed to connect to control switch: "
                  << result_or_control_p4_session.status();
  }
  auto p4info_matches_result = HasDefaultOrNoP4Info(GetMirrorTestbed().Sut());
  if (!p4info_matches_result.ok()) {
    ADD_FAILURE() << "Failed to query SUT P4Info on "
                  << GetMirrorTestbed().Sut().ChassisName()
                  << " during TearDown: " << p4info_matches_result.status();
  }
  // TODO: Restore original P4Info instead of reboot when Reconcile
  // is supported.
  if (!p4info_matches_result.ok() || !*p4info_matches_result) {
    EXPECT_OK(SaveSwitchLogs("teardown_before_reboot"));
    SCOPED_TRACE("Failed to restore base P4Info.");
    LOG(INFO) << "Rebooting switch to remove the P4Info.";
    RebootSut(); // Ignore fatal failures to continue cleanup.
  }
  MirrorTestbedFixture::TearDown();
}

absl::StatusOr<bool> HashTest::HasDefaultOrNoP4Info(thinkit::Switch &target) {
  ASSIGN_OR_RETURN(auto p4_session, pdpi::P4RuntimeSession::Create(target));
  ASSIGN_OR_RETURN(p4::v1::GetForwardingPipelineConfigResponse response,
                   pdpi::GetForwardingPipelineConfig(p4_session.get()));
  return !response.config().has_p4info() ||
         Matches(EqualsProto(p4_info()))(response.config().p4info());
}

absl::Status HashTest::RecordP4Info(absl::string_view test_stage,
                                    const p4::config::v1::P4Info &p4info) {
  return GetMirrorTestbed().Environment().StoreTestArtifact(
      absl::StrCat(test_stage, "_p4info.pb.txt"), p4info.DebugString());
}

void HashTest::RebootSut() {
  constexpr absl::Duration kRebootTimeout = absl::Minutes(7);
  absl::Time reboot_deadline = absl::Now() + kRebootTimeout;

  // Reboot the switch.
  thinkit::Switch &sut = GetMirrorTestbed().Sut();
  ASSERT_NO_FATAL_FAILURE(TestGnoiSystemColdReboot(sut));

  absl::Status ports_up_status =
      WaitForCondition(PortsUp,
                       /*timeout=*/reboot_deadline - absl::Now(),
                       GetMirrorTestbed().Sut(), interfaces_,
                       /*with_healthz=*/false);
  if (!ports_up_status.ok()) {
    // Collect port debug data.
    EXPECT_OK(PortsUp(GetMirrorTestbed().Sut(), interfaces_,
                      /*with_healthz=*/true));
    EXPECT_OK(PortsUp(GetMirrorTestbed().ControlSwitch(), interfaces_,
                      /*with_healthz=*/true));
  }
  ASSERT_OK(ports_up_status);

  // Wait for P4Runtime to be reachable.
  absl::StatusOr<std::unique_ptr<pdpi::P4RuntimeSession>> status_or_p4_session;
  do {
    status_or_p4_session = pdpi::P4RuntimeSession::Create(sut);
  } while (!status_or_p4_session.ok() && absl::Now() < reboot_deadline);
  ASSERT_OK(status_or_p4_session)
      << "Switch failed to reboot and come up after " << kRebootTimeout;
}

void HashTest::SendAndReceivePackets(const pdpi::IrP4Info &ir_p4info,
                                     absl::string_view record_prefix,
                                     int num_packets,
                                     const TestConfiguration &test_config,
                                     TestData &test_data) {
  SCOPED_TRACE(absl::StrCat("Failed while testing config: ", record_prefix));
  P4rtPortId ingress_port = *port_ids_.begin();

  // Set up the receive thread to record packets output by the SUT.
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<pdpi::P4RuntimeSession> control_p4_session,
      pdpi::P4RuntimeSession::Create(GetMirrorTestbed().ControlSwitch()));
  std::thread receive_packet_thread(
      absl::bind_front(ReceivePacketsUntilStreamIsClosed, &GetMirrorTestbed(),
                       &ir_p4info, control_p4_session.get(), &test_data));

  // Inject the packets.
  std::vector<packetlib::Packet> injected_packets;
  SendPackets(ir_p4info, num_packets, test_config, *control_p4_session,
              ingress_port, injected_packets);
  LogPackets(GetMirrorTestbed().Environment(), injected_packets,
             absl::StrCat(record_prefix, "_injected_packets"));

  // Wait for all the packets to arrive.
  absl::Time deadline = absl::Now() + absl::Seconds(30);
  while (test_data.PacketCount() < num_packets && absl::Now() < deadline) {
    absl::SleepFor(absl::Seconds(1));
  }
  EXPECT_OK(test_data.Log(GetMirrorTestbed().Environment(),
                          absl::StrCat(record_prefix, "_received_packets")));
  std::set<int> missing_packets;
  if (test_data.PacketCount() != num_packets) {
    for (int i = 0; i < num_packets; ++i) {
      missing_packets.insert(i);
      for (const auto &[port, packetlist] : test_data.Results()) {
        for (int packet : packetlist) {
          missing_packets.erase(packet);
        }
      }
    }
  }
  EXPECT_EQ(test_data.PacketCount(), num_packets)
      << "Unexpected number of packets received. "
      << (missing_packets.empty()
              ? ""
              : absl::Substitute("Missing packets [$0]",
                                 absl::StrJoin(missing_packets, ", ")));
  // Clean up.
  EXPECT_OK(control_p4_session->Finish());
  receive_packet_thread.join();
}

// Initializes the forwarding pipeline to forward all packets to the provided
// group members distributed according to their weight.
//
// The pipeline is as follows:
//  l3_admit: Forward all unicast packets.
//  pre_ingress_acl: Set vrf-80 for all packets.
//  ipv4/ipv6: Send all vrf-80 packets to wcmp_group: "group-1"
//  wcmp_group: Initialize "group-1" with the provided members.
void HashTest::ForwardAllPacketsToMembers(
    const p4::config::v1::P4Info &p4info,
    std::vector<pins::GroupMember> &members) {
  auto &testbed = GetMirrorTestbed();
  ASSERT_OK_AND_ASSIGN(auto ir_p4info, pdpi::CreateIrP4Info(p4info));
  ASSERT_OK_AND_ASSIGN(
      auto session, ConfigureSwitchAndReturnP4RuntimeSession(
                        testbed.Sut(), /*gnmi_config=*/std::nullopt, p4info));
  ASSERT_OK(pins::ProgramNextHops(testbed.Environment(), *session, ir_p4info,
                                  members));

  ASSERT_OK(pins::ProgramGroupWithMembers(testbed.Environment(), *session,
                                          ir_p4info, "group-1", members,
                                          p4::v1::Update::INSERT))
      << "Failed to program WCMP group.";

  std::vector<p4::v1::TableEntry> pi_entries;
  // Create default VRF.
  ASSERT_OK_AND_ASSIGN(p4::v1::TableEntry pi_entry,
                       pdpi::PartialPdTableEntryToPiTableEntry(
                           ir_p4info, gutil::ParseProtoOrDie<sai::TableEntry>(
                                          kAddVrfTableEntry)));
  pi_entries.push_back(pi_entry);

  // Set default VRF for all packets.
  ASSERT_OK_AND_ASSIGN(pi_entry,
                       pdpi::PartialPdTableEntryToPiTableEntry(
                           ir_p4info, gutil::ParseProtoOrDie<sai::TableEntry>(
                                          kSetVrfTableEntry)));
  pi_entries.push_back(pi_entry);

  // Add flows to allow all unicast destination mac addresses.
  ASSERT_OK_AND_ASSIGN(pi_entry,
                       pdpi::PartialPdTableEntryToPiTableEntry(
                           ir_p4info, gutil::ParseProtoOrDie<sai::TableEntry>(
                                          kL3AdmitUnicastTableEntry)));
  pi_entries.push_back(pi_entry);

  // Add minimal set of flows to allow forwarding.
  ASSERT_OK_AND_ASSIGN(pi_entry,
                       pdpi::PartialPdTableEntryToPiTableEntry(
                           ir_p4info, gutil::ParseProtoOrDie<sai::TableEntry>(
                                          kIpv4DefaultRouteEntry)));
  pi_entries.push_back(pi_entry);

  ASSERT_OK_AND_ASSIGN(pi_entry,
                       pdpi::PartialPdTableEntryToPiTableEntry(
                           ir_p4info, gutil::ParseProtoOrDie<sai::TableEntry>(
                                          kIpv6DefaultRouteEntry)));
  pi_entries.push_back(pi_entry);

  ASSERT_OK(pdpi::InstallPiTableEntries(session.get(), ir_p4info, pi_entries));
}

void HashTest::SendPacketsAndRecordResultsPerTestConfig(
    const TestConfigurationMap &test_configs,
    const p4::config::v1::P4Info &p4info, absl::string_view test_stage,
    int num_packets,
    absl::node_hash_map<std::string, TestData> &output_record) {
  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info ir_p4info, pdpi::CreateIrP4Info(p4info));
  for (const auto &[config_name, test_config] : test_configs) {
    std::string record_prefix = absl::StrCat(test_stage, "_", config_name);
    ASSERT_NO_FATAL_FAILURE(SendAndReceivePackets(ir_p4info, record_prefix,
                                                  num_packets, test_config,
                                                  output_record[config_name]));
  }
}

} // namespace pins_test
