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
#include <sstream>
#include <string>
#include <utility>
#include <vector>

#include "absl/base/thread_annotations.h"
#include "absl/container/btree_set.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/node_hash_map.h"
#include "absl/random/distributions.h"
#include "absl/random/random.h"
#include "absl/random/seed_sequences.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/synchronization/mutex.h"
#include "absl/time/time.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "gutil/gutil/version.h"
#include "lib/p4rt/p4rt_port.h"
#include "lib/validator/validator_lib.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4_infra/p4_pdpi/p4_runtime_session_extras.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_infra/p4_pdpi/pd.h"
#include "re2/re2.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "sai_p4/instantiations/google/versions.h"
#include "tests/forwarding/group_programming_util.h"
#include "tests/forwarding/packet_test_util.h"
#include "tests/forwarding/util.h"
#include "tests/lib/common_ir_table_entries.h"
#include "tests/lib/packet_generator.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/mirror_testbed_fixture.h"
#include "thinkit/switch.h"
#include "thinkit/test_environment.h"

namespace pins_test {

namespace {

using ::pins::PacketField;
using ::pins::TestConfiguration;

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

absl::BitGen &HashTestBitGen() {
  static auto *bit_gen = new absl::BitGen();

  return *bit_gen;
}

// Set the payload for a HashTest packet that contains an identifier,
// the packet index, and optionally the generator index.
void SetPayload(packetlib::Packet &packet, int packet_index,
                std::optional<int> generator_index) {
  if (generator_index == std::nullopt) {
    packet.set_payload(absl::Substitute("HashAlgPacket($0): $1", packet_index,
                                        packet.payload()));
  } else {
    packet.set_payload(absl::Substitute("HashAlgPacket($0), Generator($1): $2",
                                        packet_index, *generator_index,
                                        packet.payload()));
  }
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

// Sets the P4Info on the switch to the desired P4Info. If the switch requires a
// reboot, updates the p4 session to a new session after the reboot.
absl::Status SetP4Info(std::unique_ptr<pdpi::P4RuntimeSession>& p4_session,
                       thinkit::Switch& device,
                       const p4::config::v1::P4Info& default_p4info) {
  absl::Status reconcile = pdpi::SetMetadataAndSetForwardingPipelineConfig(
      p4_session.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      default_p4info);
  if (!reconcile.ok()) {
    LOG(WARNING) << "Failed to reconcile P4Info. Attempting P4Info push with "
                    "reboot. Reconcile result: "
                 << reconcile;
    ASSIGN_OR_RETURN(p4_session, ConfigureSwitchAndReturnP4RuntimeSession(
                                     device, std::nullopt, default_p4info));
  }
  return absl::OkStatus();
}

bool ReceivePacket(const pdpi::IrP4Info& ir_p4info,
                   const p4::v1::StreamMessageResponse& pi_response,
                   HashTest::TestData* test_data) {
  sai::StreamMessageResponse pd_response;
  if (auto status = pdpi::PiStreamMessageResponseToPd(ir_p4info, pi_response,
                                                      &pd_response);
      !status.ok()) {
    ADD_FAILURE() << " PacketIn PI to PD failed: " << status;
    return false;
  }
  if (!pd_response.has_packet()) {
    LOG(WARNING) << "Ignoring unexpected stream message for packet in: "
                 << pd_response.DebugString();
    return false;
  }

  absl::string_view raw_packet = pd_response.packet().payload();
  packetlib::Packet packet = packetlib::ParsePacket(raw_packet);
  return test_data->AddPacket(
      pd_response.packet().metadata().target_egress_port(), std::move(packet));
}

absl::Status SendPacket(const pdpi::IrP4Info &ir_p4info,
                        packetlib::Packet packet,
                        pdpi::P4RuntimeSession &control_p4_session,
                        const P4rtPortId &ingress_port_id) {
  ASSIGN_OR_RETURN(
      std::string raw_packet, SerializePacket(packet),
      _ << "Failed to inject packet: " << packet.ShortDebugString());
  RETURN_IF_ERROR(
      pins::InjectEgressPacket(ingress_port_id.GetP4rtEncoding(), raw_packet,
                               ir_p4info, &control_p4_session, kPacketInterval))
      << "Failed to inject packet: " << packet.ShortDebugString();
  return absl::OkStatus();
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

const packetgen::Options& Ipv4HashingOptions() {
  static const auto* const kOptions = new packetgen::Options({
      .ip_type = packetgen::IpType::kIpv4,
      .variables =
          {
              packetgen::Field::kIpSrc,
              packetgen::Field::kIpDst,
              packetgen::Field::kL4SrcPort,
              packetgen::Field::kL4DstPort,
          },
  });
  return *kOptions;
}

const packetgen::Options& Ipv6HashingOptions() {
  static const auto* const kOptions = new packetgen::Options({
      .ip_type = packetgen::IpType::kIpv6,
      .variables =
          {
              packetgen::Field::kIpSrc,
              packetgen::Field::kIpDst,
              packetgen::Field::kL4SrcPort,
              packetgen::Field::kL4DstPort,
              packetgen::Field::kFlowLabelLower16,
              packetgen::Field::kFlowLabelUpper4,
          },
  });
  return *kOptions;
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

bool HashTest::TestData::AddPacket(absl::string_view egress_port,
                                   packetlib::Packet packet) {
  absl::StatusOr<int> status_or_index = GetPacketIndex(packet);
  if (!status_or_index.ok()) {
    // Ignore packets that don't match.
    VLOG(1) << "Received unexpected packet: " << packet.ShortDebugString()
            << ". " << status_or_index.status();
    return false;
  }

  absl::MutexLock lock(&mutex_);
  packets_by_port_[egress_port].insert(*status_or_index);
  received_packets_.push_back({std::string(egress_port), std::move(packet)});
  return true;
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

std::vector<packetlib::Packet> HashTest::TestData::GetReceivedPacketsOnPort(
    const P4rtPortId& port_id) const ABSL_LOCKS_EXCLUDED(mutex_) {
  std::vector<packetlib::Packet> port_packets;
  const std::string& match_port = port_id.GetP4rtEncoding();
  absl::MutexLock lock(&mutex_);
  for (const auto& [inport, packet] : received_packets_) {
    if (inport == match_port) {
      port_packets.push_back(packet);
    }
  }
  return port_packets;
}

// Initialize the testbed for the test.
//   Set up P4 sessions.
//   Push gNMI config.
//   Add the trap rule to the control switch.
void HashTest::InitializeTestbed() {
  thinkit::Switch& sut = GetMirrorTestbed().Sut();
  thinkit::Switch& control_switch = GetMirrorTestbed().ControlSwitch();
  ASSERT_OK_AND_ASSIGN(sut_p4_session_, pdpi::P4RuntimeSession::Create(sut));
  ASSERT_OK_AND_ASSIGN(control_p4_session_,
                       pdpi::P4RuntimeSession::Create(control_switch));

  // Wait for ports to come up before the test. We don't need all the ports to
  // be up, but it helps with reproducibility. We're using a short timeout (10
  // seconds) so the impact is small if the testbed doesn't bring up every port.
  if (auto all_interfaces_up_status = WaitForCondition(
          AllPortsUp, absl::Seconds(10), sut, /*with_healthz=*/false);
      !all_interfaces_up_status.ok()) {
    LOG(WARNING) << "Some ports are down at the start of the test. "
                 << "Continuing with only the UP ports.";
    // Collect port debug data but don't fail the test.
    absl::Status tmp_status = AllPortsUp(sut, /*with_healthz=*/true);
    LOG_IF(WARNING, !tmp_status.ok()) << "SUT Ports Up Check: " << tmp_status;
    tmp_status = AllPortsUp(control_switch, /*with_healthz=*/true);
    LOG_IF(WARNING, !tmp_status.ok())
        << "Control Ports Up Check: " << tmp_status;
  }

  LOG(INFO) << "Initializing forwarding pipeline for SUT.";
  // Use this function to push P4Info if needed. Then clear the forwarding
  // state.
  ASSERT_OK(SetP4Info(sut_p4_session_, sut, test_p4_info()));
  ASSERT_OK(pdpi::ClearEntities(sut_p4_session()))
      << "failed to clear SUT flows before test.";

  // Setup control switch P4 state.
  LOG(INFO) << "Initializing forwarding pipeline for control switch.";
  ASSERT_OK_AND_ASSIGN(
      control_switch_p4info_,
      GetOrSetP4Info(control_switch_p4_session(), test_p4_info()));
  ASSERT_OK(pdpi::ClearEntities(control_switch_p4_session()))
      << "failed to clear Control flows before test.";

  // Trap all packets on control switch.
  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info control_switch_ir_p4info,
                       pdpi::CreateIrP4Info(control_switch_p4_info()));
  ASSERT_OK(pdpi::InstallIrTableEntry(
      control_switch_p4_session(),
      pins::PuntAllPacketsToControllerIrTableEntry("0x7")));
}

void HashTest::SetUp() {
  mirror_testbed_->SetUp();
  ASSERT_NO_FATAL_FAILURE(InitializeTestbed());

  ASSERT_OK_AND_ASSIGN(std::vector<MirroredPort> mirrored_ports,
                       MirroredPorts(GetMirrorTestbed()));
  for (const auto& mirrored_port : mirrored_ports) {
    port_ids_to_interfaces_.insert_or_assign(mirrored_port.sut,
                                             mirrored_port.interface);
    port_ids_.insert(mirrored_port.sut);
    interfaces_.push_back(mirrored_port.interface);
  }
  LOG(INFO) << "Using ports: ["
            << absl::StrJoin(port_ids_, ", ", absl::StreamFormatter()) << "]";
  ASSERT_GE(port_ids_.size(), kMinimumMembersForTest);
}

void HashTest::TearDown() {
  // Clean up flows on the control switch. We're using a non-fatal failure
  // here so we continue cleanup.
  EXPECT_OK(SaveSwitchLogs("teardown_before_table_clear"));
  auto control_p4_session =
      pdpi::P4RuntimeSession::Create(GetMirrorTestbed().ControlSwitch());
  if (control_p4_session.ok()) {
    EXPECT_OK(pdpi::ClearEntities(**control_p4_session))
        << "failed to clean up control switch P4 entries.";
  } else {
    ADD_FAILURE() << "failed to connect to control switch: "
                  << control_p4_session.status();
  }
  auto sut_p4_session =
      pdpi::P4RuntimeSession::Create(GetMirrorTestbed().Sut());
  if (sut_p4_session.ok()) {
    EXPECT_OK(pdpi::ClearEntities(**sut_p4_session))
        << "failed to clean up sut switch P4 entries.";
  } else {
    ADD_FAILURE() << "failed to connect to sut switch: "
                  << sut_p4_session.status();
  }

  switch (mirror_testbed_teardown_condition_) {
  case TearDownCondition::kAlways:
    mirror_testbed_->TearDown();
    break;
  case TearDownCondition::kOnFailure:
    if (HasFailure())
      mirror_testbed_->TearDown();
    break;
  }
}

absl::Status HashTest::RecordP4Info(absl::string_view test_stage,
                                    const p4::config::v1::P4Info &p4info) {
  return GetMirrorTestbed().Environment().StoreTestArtifact(
      absl::StrCat(test_stage, "_p4info.pb.txt"), p4info.DebugString());
}

absl::StatusOr<std::vector<packetlib::Packet>> HashTest::GeneratePackets(
    const pins::TestConfiguration& test_config, int num_packets,
    HashTest::PacketGeneratorStyle style) {
  // Try to generate one packet first to see if the config is valid.
  ASSIGN_OR_RETURN(packetlib::Packet packet,
                   pins::GenerateIthPacket(test_config, 0));
  RETURN_IF_ERROR(SerializePacket(packet).status())
      << "Failed to generate raw packet for " << packet.ShortDebugString();

  // If the range of values available in the hashed field is sufficiently larger
  // than the number of packets we want to send, generate packets with random
  // values distributed from the full range. Otherwise, choose sequential
  // values.
  int range = pins::Range(test_config);
  bool use_random_index = style == PacketGeneratorStyle::kUniform;
  LOG(INFO) << "Generating " << num_packets << " "
            << (use_random_index ? "random" : "sequential")
            << " packets for config: " << pins::DescribeTestConfig(test_config)
            << " allowing for up to " << range << " unique values";

  std::vector<packetlib::Packet> packets;
  for (int packet_index = 0; packet_index < num_packets; ++packet_index) {
    int generator_index = use_random_index
                              ? absl::Uniform(HashTestBitGen(), 0, range)
                              : packet_index;
    ASSIGN_OR_RETURN(packetlib::Packet packet,
                     pins::GenerateIthPacket(test_config, generator_index));
    SetPayload(
        packet, packet_index,
        use_random_index ? std::optional<int>(generator_index) : std::nullopt);
    packets.push_back(packet);
  }
  return packets;
}

absl::StatusOr<TestPacketMap> HashTest::GeneratePackets(
    const TestConfigurationMap& test_configs, int num_packets,
    HashTest::PacketGeneratorStyle style) {
  TestPacketMap packets;
  for (const auto &[field, config] : test_configs) {
    ASSIGN_OR_RETURN(packets[field],
                     GeneratePackets(config, num_packets, style),
                     _ << "Invalid test config for " << field);
  }
  return packets;
}

absl::StatusOr<std::vector<packetlib::Packet>> HashTest::GeneratePackets(
    const packetgen::Options& options, int num_packets) {
  ASSIGN_OR_RETURN(auto generator, packetgen::PacketGenerator::Create(options));
  std::vector<packetlib::Packet> packets = generator.Packets(num_packets);
  for (int i = 0; i < num_packets; ++i) {
    SetPayload(packets[i], i, std::nullopt);
  }
  return packets;
}

absl::Status HashTest::SendAndReceivePackets(
    const pdpi::IrP4Info &ir_p4info, absl::string_view record_prefix,
    const P4rtPortId &ingress_port_id,
    const std::vector<packetlib::Packet> &packets, TestData &test_data) {
  SCOPED_TRACE(absl::StrCat("Failed while testing config: ", record_prefix));
  // Set up the receive thread to record packets output by the SUT.
  ASSIGN_OR_RETURN(
      std::unique_ptr<pdpi::P4RuntimeSession> control_p4_session,
      pdpi::P4RuntimeSession::Create(GetMirrorTestbed().ControlSwitch()));

  for (const auto &packet : packets) {
    RETURN_IF_ERROR(
        SendPacket(ir_p4info, packet, *control_p4_session, ingress_port_id));
  }
  LogPackets(GetMirrorTestbed().Environment(), packets,
             absl::StrCat(record_prefix, "_injected_packets"));

  // Wait for all the packets to arrive.
  if (absl::Status packet_status =
          control_p4_session->HandleNextNStreamMessages(
              [&](const p4::v1::StreamMessageResponse &message) {
                return ReceivePacket(ir_p4info, message, &test_data);
              },
              packets.size(), absl::Minutes(2));
      !packet_status.ok()) {
    LOG(WARNING) << packet_status;
  }
  if (auto result =
          test_data.Log(GetMirrorTestbed().Environment(),
                        absl::StrCat(record_prefix, "_received_packets"));
      !result.ok()) {
    LOG(ERROR) << result;
  }
  absl::btree_set<int> missing_packets;
  if (test_data.PacketCount() != packets.size()) {
    for (int i = 0; i < packets.size(); ++i) {
      missing_packets.insert(i);
      for (const auto &[port, packetlist] : test_data.Results()) {
        for (int packet : packetlist) {
          missing_packets.erase(packet);
        }
      }
    }
  }
  std::vector<packetlib::Packet> missing_packet_list;
  if (!missing_packets.empty()) {
    missing_packet_list.reserve(missing_packets.size());
    for (int index : missing_packets) {
      missing_packet_list.push_back(packets[index]);
    }
    LogPackets(GetMirrorTestbed().Environment(), missing_packet_list,
               absl::StrCat(record_prefix, "_missing_packets"));
  }
  std::vector<std::string> errors;
  if (test_data.PacketCount() != packets.size()) {
    std::string error = absl::Substitute(
        "Unexpected number of packets received. Expected $0. Got $1.$2",
        packets.size(), test_data.PacketCount(),
        missing_packets.empty()
            ? ""
            : absl::Substitute(" Missing packets [$0]",
                               absl::StrJoin(missing_packets, ", ")));
    if (missing_packets.size() < 10) { // Don't make this too noisy.
      absl::StrAppend(
          &error, ":\n",
          absl::StrJoin(missing_packet_list, "\n",
                        [](std::string *out, const packetlib::Packet &packet) {
                          absl::StrAppend(out, packet.ShortDebugString());
                        }));
    }
    errors.push_back(std::move(error));
  }
  // Clean up.
  if (absl::Status finished = control_p4_session->Finish(); !finished.ok()) {
    errors.push_back(absl::StrCat("Failed control_p4_session->Finish(): ",
                                  finished.message()));
  }
  if (errors.empty()) return absl::OkStatus();
  return absl::InternalError(absl::StrJoin(errors, "\n"));
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
  ASSERT_OK(pins::ProgramNextHops(testbed.Environment(), sut_p4_session(),
                                   ir_p4info, members));

  ASSERT_OK(pins::ProgramGroupWithMembers(
      testbed.Environment(), sut_p4_session(), ir_p4info, "group-1", members,
      p4::v1::Update::INSERT))
      << "Failed to program WCMP group.";

  std::vector<p4::v1::Entity> pi_entities;
  // Create default VRF.
  ASSERT_OK_AND_ASSIGN(p4::v1::Entity pi_entity,
                       pdpi::PdTableEntryToPiEntity(
                           ir_p4info, gutil::ParseProtoOrDie<sai::TableEntry>(
                                          kAddVrfTableEntry)));
  pi_entities.push_back(pi_entity);

  // Set default VRF for all packets.
  ASSERT_OK_AND_ASSIGN(pi_entity,
                       pdpi::PdTableEntryToPiEntity(
                           ir_p4info, gutil::ParseProtoOrDie<sai::TableEntry>(
                                          kSetVrfTableEntry)));
  pi_entities.push_back(pi_entity);

  // Add flows to allow all unicast destination mac addresses.
  ASSERT_OK_AND_ASSIGN(pi_entity,
                       pdpi::PdTableEntryToPiEntity(
                           ir_p4info, gutil::ParseProtoOrDie<sai::TableEntry>(
                                          kL3AdmitUnicastTableEntry)));
  pi_entities.push_back(pi_entity);

  // Add minimal set of flows to allow forwarding.
  ASSERT_OK_AND_ASSIGN(pi_entity,
                       pdpi::PdTableEntryToPiEntity(
                           ir_p4info, gutil::ParseProtoOrDie<sai::TableEntry>(
                                          kIpv4DefaultRouteEntry)));
  pi_entities.push_back(pi_entity);

  ASSERT_OK_AND_ASSIGN(pi_entity,
                       pdpi::PdTableEntryToPiEntity(
                           ir_p4info, gutil::ParseProtoOrDie<sai::TableEntry>(
                                          kIpv6DefaultRouteEntry)));
  pi_entities.push_back(pi_entity);

  ASSERT_OK(pdpi::InstallPiEntities(&sut_p4_session(), ir_p4info, pi_entities));
}

absl::Status HashTest::SendPacketsAndRecordResultsPerTest(
    const TestPacketMap &test_packets, const p4::config::v1::P4Info &p4info,
    absl::string_view test_stage, const P4rtPortId &ingress_port_id,
    absl::node_hash_map<std::string, TestData> &output_record) {
  ASSIGN_OR_RETURN(pdpi::IrP4Info ir_p4info, pdpi::CreateIrP4Info(p4info));
  for (const auto &[config_name, packets] : test_packets) {
    std::string record_prefix = absl::StrCat(test_stage, "_", config_name);
    RETURN_IF_ERROR(SendAndReceivePackets(ir_p4info, record_prefix,
                                          ingress_port_id, packets,
                                          output_record[config_name]))
        << "Failed during test " << record_prefix;
  }
  return absl::OkStatus();
}

absl::StatusOr<std::string>
HashTest::GnmiInterfaceName(const P4rtPortId &port_id) const {
  auto result = port_ids_to_interfaces_.find(port_id);
  if (result == port_ids_to_interfaces_.end()) {
    return absl::NotFoundError(absl::StrCat(
        "No gNMI interface known for port id ", port_id.GetP4rtEncoding()));
  }
  return result->second;
}

absl::StatusOr<p4::config::v1::P4Info> HashTest::GetSutP4Info() {
  return GetP4Info(sut_p4_session());
}

absl::Status HashTest::UpdateSutP4Info(const p4::config::v1::P4Info& p4_info) {
  auto result = pdpi::SetMetadataAndSetForwardingPipelineConfig(
      &sut_p4_session(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      p4_info);
  if (!result.ok()) {
    ASSIGN_OR_RETURN(gutil::Version current_version,
                     gutil::ParseVersion(p4_info.pkg_info().version()));
    if (current_version >=
        gutil::ParseVersionOrDie(SAI_P4_PKGINFO_VERSION_SUPPORTS_RECONCILE)) {
      return result;
    }
    LOG(WARNING) << "Rebooting after SetForwardingPipelineConfig failure: "
                 << result;
    ASSIGN_OR_RETURN(sut_p4_session_,
                     ConfigureSwitchAndReturnP4RuntimeSession(
                         GetMirrorTestbed().Sut(), std::nullopt, p4_info));
  }
  return absl::OkStatus();
}

} // namespace pins_test
