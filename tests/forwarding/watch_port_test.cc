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

#include "tests/forwarding/watch_port_test.h"

#include <memory>
#include <string>
#include <thread>  // NOLINT
#include <type_traits>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/random/random.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/escaping.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/synchronization/mutex.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "dvaas/test_vector.pb.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/collections.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "lib/gnmi/gnmi_helper.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_pdpi/pd.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/string_encodings/decimal_string.h"
#include "p4rt_app/tests/lib/p4runtime_grpc_service.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "tests/forwarding/group_programming_util.h"
#include "tests/forwarding/packet_test_util.h"
#include "tests/forwarding/util.h"
#include "tests/thinkit_sanity_tests.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/mirror_testbed_fixture.h"
#include "thinkit/switch.h"
#include "thinkit/test_environment.h"
// Tests for the watchport functionality in Action Profile Group operation.

namespace pins {

namespace {
// Admin down/up state used for interfaces.
enum class AdminState {
  kDown,
  kUp,
};

// Group id used in this test.
constexpr absl::string_view kGroupId = "group-1";

// Vrf used in the test.
constexpr absl::string_view kVrfId = "vrf-1";

// Time to wait after which received packets are processed.
constexpr absl::Duration kDurationToWaitForPackets = absl::Seconds(5);

// Number of members used in the test.
constexpr int kNumWcmpMembersForTest = 5;

// Number of packets used in the test.
constexpr int kNumTestPackets = 5000;

// Default input port index of the group members vector, on which packets
// arrive.
constexpr int kDefaultInputPortIndex = 0;

// Helper function that sets up the  input port for packet recieve.
// Creates the router interface for the input port. Without this input packets
// get dropped (b/190736007).
absl::Status SetUpInputPortForPacketReceive(pdpi::P4RuntimeSession& p4_session,
                                            const pdpi::IrP4Info& ir_p4info,
                                            int input_port) {
  ASSIGN_OR_RETURN(
      p4::v1::WriteRequest write_request,
      pdpi::PdWriteRequestToPi(
          ir_p4info, gutil::ParseProtoOrDie<sai::WriteRequest>(absl::Substitute(
                         R"pb(
                           updates {
                             type: INSERT
                             table_entry {
                               router_interface_table_entry {
                                 match { router_interface_id: "$0" }
                                 action {
                                   set_port_and_src_mac {
                                     port: "$1"
                                     src_mac: "00:02:03:04:05:06"
                                   }
                                 }
                               }
                             }
                           }
                         )pb",
                         input_port, input_port))));

  return pdpi::SetMetadataAndSendPiWriteRequest(&p4_session, write_request);
}

// Helper function that creates/deletes V4, V6 default route entries.
absl::Status ProgramDefaultRoutes(pdpi::P4RuntimeSession& p4_session,
                                  const pdpi::IrP4Info& ir_p4info,
                                  absl::string_view default_vrf,
                                  const p4::v1::Update_Type& type) {
  if (!p4::v1::Update_Type_IsValid(type) ||
      type == p4::v1::Update_Type_UNSPECIFIED) {
    return absl::InvalidArgumentError(
        absl::StrCat("Type: ", type, " not supported."));
  }
  std::string type_str = p4::v1::Update_Type_Name(type);
  // Add minimal set of flows to allow forwarding.
  auto ipv4_fallback = gutil::ParseProtoOrDie<sai::Update>(absl::Substitute(
      R"pb(
        type: $0
        table_entry {
          ipv4_table_entry {
            match { vrf_id: "$1" }
            action { set_wcmp_group_id { wcmp_group_id: "$2" } }
          }
        })pb",
      type_str, default_vrf, kGroupId));
  auto ipv6_fallback = gutil::ParseProtoOrDie<sai::Update>(absl::Substitute(
      R"pb(
        type: $0
        table_entry {
          ipv6_table_entry {
            match { vrf_id: "$1" }
            action { set_wcmp_group_id { wcmp_group_id: "$2" } }
          }
        })pb",
      type_str, default_vrf, kGroupId));

  p4::v1::WriteRequest write_request;
  for (const auto& pd_entry : {ipv4_fallback, ipv6_fallback}) {
    ASSIGN_OR_RETURN(
        p4::v1::Update pi_entry, pdpi::PdUpdateToPi(ir_p4info, pd_entry),
        _.SetPrepend() << "Failed in PD table conversion to PI, entry: "
                       << pd_entry.DebugString() << " error: ");
    *write_request.add_updates() = pi_entry;
  }
  return pdpi::SetMetadataAndSendPiWriteRequest(&p4_session, write_request);
}

// Installs a default vrf for all packets on the SUT.
absl::Status SetUpSut(pdpi::P4RuntimeSession& p4_session,
                      const pdpi::IrP4Info& ir_p4info,
                      absl::string_view default_vrf) {
  // Create default VRF for test.
  ASSIGN_OR_RETURN(
      p4::v1::TableEntry pi_entry,
      pdpi::PartialPdTableEntryToPiTableEntry(
          ir_p4info, gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
                         R"pb(
                           vrf_table_entry {
                             match { vrf_id: "$0" }
                             action { no_action {} }
                           })pb",
                         default_vrf))));
  RETURN_IF_ERROR(pdpi::InstallPiTableEntry(&p4_session, pi_entry));

  // Set default VRF for all packets.
  ASSIGN_OR_RETURN(
      pi_entry,
      pdpi::PartialPdTableEntryToPiTableEntry(
          ir_p4info, gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
                         R"pb(
                           vrf_table_entry {
                             match { vrf_id: "$0" }
                             action { no_action {} }
                           })pb",
                         default_vrf))));
  RETURN_IF_ERROR(pdpi::InstallPiTableEntry(&p4_session, pi_entry));

  // Set default VRF for all packets.
  ASSIGN_OR_RETURN(
      pi_entry,
      pdpi::PartialPdTableEntryToPiTableEntry(
          ir_p4info, gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
                         R"pb(
                           acl_pre_ingress_table_entry {
                             match {}  # Wildcard match
                             action { set_vrf { vrf_id: "$0" } }  # Default vrf
                             priority: 1129
                           })pb",
                         default_vrf))));

  return pdpi::InstallPiTableEntry(&p4_session, pi_entry);
}

// Punts all packets on the control switch.
absl::Status SetUpControlSwitch(pdpi::P4RuntimeSession& p4_session,
                                const pdpi::IrP4Info& ir_p4info) {
  // Trap all packets on control switch.
  ASSIGN_OR_RETURN(
      p4::v1::TableEntry punt_all_pi_entry,
      pdpi::PartialPdTableEntryToPiTableEntry(
          ir_p4info,
          gutil::ParseProtoOrDie<sai::TableEntry>(
              R"pb(
                acl_ingress_table_entry {
                  match {}                                  # Wildcard match.
                  action { acl_trap { qos_queue: "0x7" } }  # Action: punt.
                  priority: 1                               # Highest priority.
                }
              )pb")));
  return pdpi::InstallPiTableEntry(&p4_session, punt_all_pi_entry);
}

// Creates members by filling in the controller port ids and random weights for
// each member that add upto 30(random). Skips the default input port on which
// traffic is received, since that is excluded from the traffic forwarding
// members in the group.
absl::StatusOr<std::vector<GroupMember>> CreateGroupMembers(
    int group_size, absl::Span<const int> controller_port_ids) {
  if (group_size + /*input_port=*/1 > controller_port_ids.size()) {
    return absl::InvalidArgumentError(absl::StrCat(
        "Not enough members: ", controller_port_ids.size(),
        " to reserve an input port and create the group with size: ",
        group_size));
  }
  std::vector<GroupMember> members;
  for (int i = 0; i < controller_port_ids.size() && members.size() < group_size;
       i++) {
    // Add port ids except for the default input port id.
    if (i != kDefaultInputPortIndex) {
      members.push_back(
          pins::GroupMember{.weight = 0, .port = controller_port_ids[i]});
    }
  }

  ASSIGN_OR_RETURN(std::vector<int> weights,
                   GenerateNRandomWeights(group_size,
                                          /*total_weight=*/30));
  for (int i = 0; i < members.size(); i++) {
    members[i].weight = weights[i];
  }
  return members;
}

// Creates a set of expected port ids from the member ports.
absl::flat_hash_set<int> CreateExpectedMemberPorts(
    absl::Span<const GroupMember> members) {
  absl::flat_hash_set<int> expected_member_ports;
  for (const auto& member : members) {
    expected_member_ports.insert(member.port);
  }
  return expected_member_ports;
}

// Returns a map of number of packets received per port.
absl::StatusOr<absl::flat_hash_map<int, int>> CountNumPacketsPerPort(
    absl::Span<const dvaas::Packet> output_packets) {
  absl::flat_hash_map<int, int> num_packets_per_port;
  for (const auto& output : output_packets) {
    ASSIGN_OR_RETURN(int out_port, pdpi::DecimalStringToInt(output.port()));
    num_packets_per_port[out_port]++;
  }
  return num_packets_per_port;
}

// Sends N packets from the control switch to sut at a rate of 500 packets/sec.
absl::Status SendNPacketsToSut(int num_packets,
                               const TestConfiguration& test_config,
                               absl::Span<const GroupMember> members,
                               absl::Span<const int> port_ids,
                               const pdpi::IrP4Info& ir_p4info,
                               pdpi::P4RuntimeSession& p4_session,
                               thinkit::TestEnvironment& test_environment) {
  const absl::Time start_time = absl::Now();
  for (int i = 0; i < num_packets; i++) {
    // Rate limit to 500 packets per second.
    // TODO: Limit to 100 pps until the cpu queue
    // assignment issue is fixed.
    int punt_rate_limit_pps = 500;
    if (test_environment.MaskKnownFailures()) {
      punt_rate_limit_pps = 100;
    }
    auto earliest_send_time =
        start_time + (i * absl::Seconds(1) / punt_rate_limit_pps);
    absl::SleepFor(earliest_send_time - absl::Now());

    // Vary the port on which to send the packet if the hash field selected is
    // input port.
    int port = port_ids[kDefaultInputPortIndex];
    if (test_config.field == PacketField::kInputPort) {
      port = port_ids[i % members.size()];
    }

    ASSIGN_OR_RETURN(packetlib::Packet packet,
                     pins::GenerateIthPacket(test_config, i));
    ASSIGN_OR_RETURN(std::string raw_packet, SerializePacket(packet));
    ASSIGN_OR_RETURN(std::string port_string, pdpi::IntToDecimalString(port));
    RETURN_IF_ERROR(
        pins::InjectEgressPacket(port_string, raw_packet, ir_p4info, &p4_session));

    dvaas::Packet p;
    p.set_port(port_string);
    *p.mutable_parsed() = packet;
    p.set_hex(absl::BytesToHexString(raw_packet));
    // Save log of packets.
    RETURN_IF_ERROR(test_environment.AppendToTestArtifact(
        absl::StrCat(
            "packets-for-config-",
            absl::StrJoin(absl::StrSplit(DescribeTestConfig(test_config), " "),
                          "-"),
            ".txt"),
        p.DebugString()));
  }

  LOG(INFO) << "Sent " << num_packets << " packets in "
            << (absl::Now() - start_time) << ".";
  return absl::OkStatus();
}

void PrettyPrintDistribution(
    const TestConfiguration& config, const TestInputOutput& test,
    const TestData& test_data, absl::Span<const GroupMember> members,
    const absl::flat_hash_map<int, int>& num_packets_per_port) {
  LOG(INFO) << "Results for " << DescribeTestConfig(config) << ":";
  LOG(INFO) << "- received " << test.output.size() << " packets";
  LOG(INFO) << "- observed distribution was:"
            << DescribeDistribution(test_data.total_packets_sent, members,
                                    num_packets_per_port,
                                    /*expect_single_port=*/false);
  LOG(INFO) << "Number of sent packets:               "
            << test_data.total_packets_sent;
  LOG(INFO) << "Number of received packets (valid):   "
            << test_data.total_packets_received;
  LOG(INFO) << "Number of received packets (invalid): "
            << test_data.total_invalid_packets_received;
}

// Creates the port_names_per_port_id map from GNMI config.
absl::StatusOr<absl::flat_hash_map<const std::string, std::string>>
GetPortNamePerPortId(gnmi::gNMI::StubInterface& gnmi_stub) {
  absl::flat_hash_map<const std::string, std::string> port_name_per_port_id;
  ASSIGN_OR_RETURN(auto port_id_per_port_name,
                   pins_test::GetAllInterfaceNameToPortId(gnmi_stub));
  for (const auto& [name, port_id] : port_id_per_port_name) {
    port_name_per_port_id[port_id] = name;
  }
  return port_name_per_port_id;
}

// Sets the admin state of the interface to UP/DOWN using GNMI config path.
// Queries the  state path to verify if the desired state is achieved or not.
absl::Status SetInterfaceAdminState(gnmi::gNMI::StubInterface& gnmi_stub,
                                    absl::string_view if_name,
                                    AdminState admin_state) {
  const std::string if_status =
      admin_state == AdminState::kDown ? "DOWN" : "UP";
  const std::string config_value =
      admin_state == AdminState::kDown ? "false" : "true";
  const std::string if_admin_config_path =
      absl::StrCat("interfaces/interface[name=", if_name, "]/config/enabled");
  LOG(INFO) << "Setting interface " << if_name << " to admin " << if_status;
  RETURN_IF_ERROR(SetGnmiConfigPath(
      &gnmi_stub, if_admin_config_path, pins_test::GnmiSetType::kUpdate,
      absl::Substitute("{\"enabled\":$0}", config_value)));
  // Wait for the admin state to take effect.
  absl::SleepFor(absl::Seconds(1));
  // Verifies /interfaces/interface[name=<port>]/state/admin-status = UP/DOWN.
  const std::string if_state_path =
      absl::StrCat("interfaces/interface[name=", if_name, "]/state");
  ASSIGN_OR_RETURN(const std::string state_path_response,
                   pins_test::GetGnmiStatePathInfo(
                       &gnmi_stub, if_state_path,
                       /*resp_parse_str=*/"openconfig-interfaces:state"));
  if (!absl::StrContains(state_path_response, if_status)) {
    return absl::UnknownError(absl::StrCat("Unable to set interface ", if_name,
                                           " to admin ", if_status));
  }
  return absl::OkStatus();
}

// Checks if the switch is in critical state.
bool IsSwitchInCriticalState(gnmi::gNMI::StubInterface& gnmi_stub) {
  auto alarms = pins_test::GetAlarms(gnmi_stub);
  if (!alarms.ok() || !alarms->empty()) {
    return true;
  }
  return false;
}

}  // namespace

void WatchPortTestFixture::SetUp() {
  GetParam().testbed->SetUp();
  thinkit::MirrorTestbed& testbed = GetParam().testbed->GetMirrorTestbed();

  // Push gnmi config to the sut and control switch.
  const std::string& gnmi_config = GetParam().gnmi_config;
  ASSERT_OK(
      testbed.Environment().StoreTestArtifact("gnmi_config.txt", gnmi_config));
  ASSERT_OK(pins_test::PushGnmiConfig(testbed.Sut(), gnmi_config));
  ASSERT_OK(pins_test::PushGnmiConfig(testbed.ControlSwitch(), gnmi_config));

  // Wait for the gnmi port config to converge.
  ASSERT_OK(
      pins_test::WaitForGnmiPortIdConvergence(testbed.Sut(), gnmi_config,
                                              /*timeout=*/absl::Minutes(3)));
  ASSERT_OK(pins_test::WaitForGnmiPortIdConvergence(
      testbed.ControlSwitch(), gnmi_config,
      /*timeout=*/absl::Minutes(3)));

  ASSERT_OK(testbed.Environment().StoreTestArtifact("p4info.pb.txt",
                                                    GetP4Info().DebugString()));

  // Setup SUT & control switch.

  ASSERT_OK_AND_ASSIGN(sut_p4_session_,
                       pdpi::P4RuntimeSession::CreateWithP4InfoAndClearTables(
                           testbed.Sut(), GetP4Info()));
  ASSERT_OK_AND_ASSIGN(control_p4_session_,
                       pdpi::P4RuntimeSession::CreateWithP4InfoAndClearTables(
                           testbed.ControlSwitch(), GetP4Info()));
  ASSERT_OK(SetUpSut(*sut_p4_session_, GetIrP4Info(), kVrfId));
  ASSERT_OK(SetUpControlSwitch(*control_p4_session_, GetIrP4Info()));

  // Create GNMI stub for admin operations.
  ASSERT_OK_AND_ASSIGN(sut_gnmi_stub_, testbed.Sut().CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(control_gnmi_stub_,
                       testbed.ControlSwitch().CreateGnmiStub());

  // Start the receiver thread for control switch to listen for packets from
  // SUT, this thread is terminated in the TearDown.
  receive_packet_thread_ = std::thread([&]() {
    p4::v1::StreamMessageResponse pi_response;
    while (control_p4_session_->StreamChannelRead(pi_response)) {
      absl::MutexLock lock(&test_data_.mutex);
      sai::StreamMessageResponse pd_response;
      ASSERT_OK(pdpi::PiStreamMessageResponseToPd(GetIrP4Info(), pi_response,
                                                  &pd_response))
          << " PacketIn PI to PD failed: ";
      ASSERT_TRUE(pd_response.has_packet())
          << " Received unexpected stream message for packet in: "
          << pd_response.DebugString();
      absl::string_view raw_packet = pd_response.packet().payload();
      dvaas::Packet packet;
      packet.set_port(pd_response.packet().metadata().ingress_port());
      packet.set_hex(absl::BytesToHexString(raw_packet));
      *packet.mutable_parsed() = packetlib::ParsePacket(raw_packet);
      std::string key = packet.parsed().payload();
      if (test_data_.input_output_per_packet.contains(key)) {
        test_data_.input_output_per_packet[key].output.push_back(packet);
        test_data_.total_packets_received += 1;
      } else {
        ASSERT_OK(testbed.Environment().AppendToTestArtifact(
            "control_unexpected_packet_ins.pb.txt",
            absl::StrCat(packet.DebugString(), "\n")));
        test_data_.total_invalid_packets_received += 1;
      }
    }
  });
}

void WatchPortTestFixture::TearDown() {
  thinkit::MirrorTestbedInterface& testbed = *GetParam().testbed;

  // Reboot the switch, if Sut is in critical state.
  if (sut_gnmi_stub_ && IsSwitchInCriticalState(*sut_gnmi_stub_)) {
    // Grab logs on the switches before the reboot.
    ASSERT_OK(testbed.SaveSwitchLogs("before_reboot_"));
    LOG(INFO) << "Switch is in critical state, rebooting the switch.";
    pins_test::TestGnoiSystemColdReboot(testbed.GetMirrorTestbed().Sut());
    pins_test::TestGnoiSystemColdReboot(
        testbed.GetMirrorTestbed().ControlSwitch());
    if (receive_packet_thread_.joinable()) {
      receive_packet_thread_.join();
    }
    testbed.TearDown();
    return;
  }

  // Clear table entries.
  if (sut_p4_session_ != nullptr) {
    EXPECT_OK(pdpi::ClearTableEntries(sut_p4_session_.get()));
    EXPECT_OK(sut_p4_session_->Finish());
  }
  // Stop RPC sessions.
  if (control_p4_session_ != nullptr) {
    EXPECT_OK(
        pdpi::ClearTableEntries(control_p4_session_.get()));
    EXPECT_OK(control_p4_session_->Finish());
  }
  if (receive_packet_thread_.joinable()) {
    receive_packet_thread_.join();
  }
  if (control_gnmi_stub_) {
    ASSERT_OK_AND_ASSIGN(const auto port_name_per_port_id,
                         GetPortNamePerPortId(*control_gnmi_stub_));
    // Restore the admin state to UP.
    for (const auto& [port_id, name] : port_name_per_port_id) {
      EXPECT_OK(
          SetInterfaceAdminState(*control_gnmi_stub_, name, AdminState::kUp));
    }
  }
  testbed.TearDown();
}

// TODO: Parameterize over the different instantiations like
// MiddleBlock, FBR400.
const p4::config::v1::P4Info& WatchPortTestFixture::GetP4Info() {
  return sai::GetP4Info(sai::Instantiation::kMiddleblock);
}
const pdpi::IrP4Info& WatchPortTestFixture::GetIrP4Info() {
  return sai::GetIrP4Info(sai::Instantiation::kMiddleblock);
}

namespace {

// Verifies basic WCMP behavior by programming a group with multiple members
// with random weights and ensuring that all members receive some part of
// the sent traffic.
TEST_P(WatchPortTestFixture, VerifyBasicWcmpPacketDistribution) {
  thinkit::TestEnvironment& environment =
      GetParam().testbed->GetMirrorTestbed().Environment();
  environment.SetTestCaseID("9a4c3dac-44bd-489e-9237-d396b66c85f5");

  absl::Span<const int> controller_port_ids = GetParam().port_ids;
  const int group_size = kNumWcmpMembersForTest;
  ASSERT_OK_AND_ASSIGN(std::vector<GroupMember> members,
                       CreateGroupMembers(group_size, controller_port_ids));

  const int input_port = controller_port_ids[kDefaultInputPortIndex];
  ASSERT_OK(SetUpInputPortForPacketReceive(*sut_p4_session_, GetIrP4Info(),
                                           input_port));

  // Programs the required router interfaces, nexthops for wcmp group.
  ASSERT_OK(pins::ProgramNextHops(environment, *sut_p4_session_, GetIrP4Info(),
                                   members));
  ASSERT_OK(pins::ProgramGroupWithMembers(environment, *sut_p4_session_,
                                           GetIrP4Info(), kGroupId, members,
                                           p4::v1::Update::INSERT))
      << "Failed to program WCMP group: ";

  // Program default routing for all packets on SUT.
  ASSERT_OK(ProgramDefaultRoutes(*sut_p4_session_, GetIrP4Info(), kVrfId,
                                 p4::v1::Update::INSERT));

  // Generate test configuration, pick any field (IP_SRC) used by hashing to
  // vary for every packet so that it gets sent to all the members.
  TestConfiguration test_config = {
      .field = PacketField::kIpSrc,
      .ipv4 = true,
      .encapped = false,
      .inner_ipv4 = false,
      .decap = false,
  };
  ASSERT_TRUE(IsValidTestConfiguration(test_config));

  // Create test data entry.
  std::string test_config_key = TestConfigurationToPayload(test_config);
  {
    absl::MutexLock lock(&test_data_.mutex);
    test_data_.input_output_per_packet[test_config_key] = TestInputOutput{
        .config = test_config,
    };
  }

  // Send 5000 packets and check for packet distribution.
  ASSERT_OK(SendNPacketsToSut(kNumTestPackets, test_config, members,
                              controller_port_ids, GetIrP4Info(),
                              *control_p4_session_, environment));
  test_data_.total_packets_sent = kNumTestPackets;

  // Wait for packets from the SUT to arrive.
  absl::SleepFor(kDurationToWaitForPackets);

  // For the test configuration, check the output distribution.
  {
    absl::MutexLock lock(&test_data_.mutex);
    const TestInputOutput& test =
        test_data_.input_output_per_packet[test_config_key];
    EXPECT_EQ(test.output.size(), test_data_.total_packets_sent)
        << "Mismatch in expected: " << test_data_.total_packets_sent
        << " and actual: " << test.output.size() << "packets received for "
        << DescribeTestConfig(test_config);

    ASSERT_OK_AND_ASSIGN(auto num_packets_per_port,
                         CountNumPacketsPerPort(test.output));
    absl::flat_hash_set<int> expected_member_ports =
        CreateExpectedMemberPorts(members);

    ASSERT_OK(VerifyGroupMembersFromP4Read(*sut_p4_session_, GetIrP4Info(),
                                           kGroupId, members));
    ASSERT_OK(VerifyGroupMembersFromReceiveTraffic(num_packets_per_port,
                                                   expected_member_ports));
    PrettyPrintDistribution(test_config, test, test_data_, members,
                            num_packets_per_port);
  }
}

// Bring down/up ActionProfileGroup member and verify traffic is distributed
// only to the up ports.
TEST_P(WatchPortTestFixture, VerifyBasicWatchPortAction) {
  thinkit::TestEnvironment& environment =
      GetParam().testbed->GetMirrorTestbed().Environment();
  environment.SetTestCaseID("992725de-2051-49bb-928f-7b089643a9bd");

  absl::Span<const int> controller_port_ids = GetParam().port_ids;
  const int group_size = kNumWcmpMembersForTest;
  ASSERT_OK_AND_ASSIGN(std::vector<GroupMember> members,
                       CreateGroupMembers(group_size, controller_port_ids));

  const int input_port = controller_port_ids[kDefaultInputPortIndex];
  ASSERT_OK(SetUpInputPortForPacketReceive(*sut_p4_session_, GetIrP4Info(),
                                           input_port));

  // Programs the required router interfaces, nexthops for wcmp group.
  ASSERT_OK(pins::ProgramNextHops(environment, *sut_p4_session_, GetIrP4Info(),
                                   members));
  ASSERT_OK(pins::ProgramGroupWithMembers(environment, *sut_p4_session_,
                                           GetIrP4Info(), kGroupId, members,
                                           p4::v1::Update::INSERT));
  // Program default routing for all packets on SUT.
  ASSERT_OK(ProgramDefaultRoutes(*sut_p4_session_, GetIrP4Info(), kVrfId,
                                 p4::v1::Update::INSERT));

  // Generate test configuration, pick any field used by hashing to vary for
  // every packet so that it gets sent to all the members.
  TestConfiguration test_config = {
      .field = PacketField::kIpDst,
      .ipv4 = true,
      .encapped = false,
      .inner_ipv4 = false,
      .decap = false,
  };
  ASSERT_TRUE(IsValidTestConfiguration(test_config));

  // Create test data entry.
  std::string test_config_key = TestConfigurationToPayload(test_config);
  {
    absl::MutexLock lock(&test_data_.mutex);
    test_data_.input_output_per_packet[test_config_key] = TestInputOutput{
        .config = test_config,
    };
  }

  absl::flat_hash_set<int> expected_member_ports =
      CreateExpectedMemberPorts(members);

  // Select one random member of the group to toggle.
  absl::BitGen gen;
  const int random_member_index =
      absl::Uniform<int>(absl::IntervalClosedOpen, gen, 0, members.size());
  const int selected_port_id = members[random_member_index].port;
  ASSERT_OK_AND_ASSIGN(const auto port_name_per_port_id,
                       GetPortNamePerPortId(*control_gnmi_stub_));
  for (auto operation : {AdminState::kDown, AdminState::kUp}) {
    ASSERT_OK_AND_ASSIGN(const auto& port_name,
                         gutil::FindOrStatus(port_name_per_port_id,
                                             absl::StrCat(selected_port_id)));
    ASSERT_OK(
        SetInterfaceAdminState(*control_gnmi_stub_, port_name, operation));

    // TODO: Adding watch port up action causes unexpected traffic
    // loss. Remove after the bug in OrchAgent is fixed.
    absl::SleepFor(absl::Seconds(5));

    // Clear the counters before the test.
    test_data_.ClearReceivedPackets();

    // Send 5000 packets and check for packet distribution.
    ASSERT_OK(SendNPacketsToSut(kNumTestPackets, test_config, members,
                                controller_port_ids, GetIrP4Info(),
                                *control_p4_session_, environment));
    test_data_.total_packets_sent = kNumTestPackets;

    // Wait for packets from the SUT to arrive.
    absl::SleepFor(kDurationToWaitForPackets);

    // For the test configuration, check the output distribution.
    {
      absl::MutexLock lock(&test_data_.mutex);
      TestInputOutput& test =
          test_data_.input_output_per_packet[test_config_key];
      EXPECT_EQ(test.output.size(), test_data_.total_packets_sent)
          << "Mismatch in expected: " << test_data_.total_packets_sent
          << " and actual: " << test.output.size() << "packets received for "
          << DescribeTestConfig(test_config);

      ASSERT_OK_AND_ASSIGN(auto num_packets_per_port,
                           CountNumPacketsPerPort(test.output));

      // Add/remove the selected member from expected_member_ports for admin
      // up/down case.
      if (operation == AdminState::kDown) {
        expected_member_ports.erase(selected_port_id);
      } else {
        expected_member_ports.insert(selected_port_id);
      }

      ASSERT_OK(VerifyGroupMembersFromP4Read(*sut_p4_session_, GetIrP4Info(),
                                             kGroupId, members));
      ASSERT_OK(VerifyGroupMembersFromReceiveTraffic(num_packets_per_port,
                                                     expected_member_ports));
      PrettyPrintDistribution(test_config, test, test_data_, members,
                              num_packets_per_port);
    }
  }
}

// TODO: Bring down APG member (when in critical state) and verify traffic is
// distributed only to the up ports.
TEST_P(WatchPortTestFixture, VerifyWatchPortActionInCriticalState) {
  // Validate that the function to raise critical state exists to run this test.
  if (!GetParam().set_critical_alarm.has_value()) {
    GTEST_SKIP() << "Critical state related test skipped because set critical "
                    "state function is not defined.";
  }
  thinkit::MirrorTestbed& testbed = GetParam().testbed->GetMirrorTestbed();
  thinkit::TestEnvironment& environment = testbed.Environment();
  environment.SetTestCaseID("964c7a38-b073-4296-85be-2bba1e33c6f9");

  absl::Span<const int> controller_port_ids = GetParam().port_ids;
  const int group_size = kNumWcmpMembersForTest;
  ASSERT_OK_AND_ASSIGN(std::vector<GroupMember> members,
                       CreateGroupMembers(group_size, controller_port_ids));

  const int input_port = controller_port_ids[kDefaultInputPortIndex];
  ASSERT_OK(SetUpInputPortForPacketReceive(*sut_p4_session_, GetIrP4Info(),
                                           input_port));

  // Program the required router interfaces, nexthops for wcmp group.
  ASSERT_OK(pins::ProgramNextHops(environment, *sut_p4_session_, GetIrP4Info(),
                                   members));
  ASSERT_OK(pins::ProgramGroupWithMembers(environment, *sut_p4_session_,
                                           GetIrP4Info(), kGroupId, members,
                                           p4::v1::Update::INSERT));
  // Program default routing for all packets on SUT.
  ASSERT_OK(ProgramDefaultRoutes(*sut_p4_session_, GetIrP4Info(), kVrfId,
                                 p4::v1::Update::INSERT));

  // Generate test configuration, pick any field used by hashing to vary for
  // every packet so that it gets sent to all the members.
  TestConfiguration test_config = {
      .field = PacketField::kIpDst,
      .ipv4 = true,
      .encapped = false,
      .inner_ipv4 = false,
      .decap = false,
  };
  ASSERT_TRUE(IsValidTestConfiguration(test_config));

  // Create test data entry.
  std::string test_config_key = TestConfigurationToPayload(test_config);
  {
    absl::MutexLock lock(&test_data_.mutex);
    test_data_.input_output_per_packet[test_config_key] = TestInputOutput{
        .config = test_config,
    };
  }

  // Select one random member of the group to bring down.
  absl::BitGen gen;
  const int random_member_index =
      absl::Uniform<int>(absl::IntervalClosedOpen, gen, 0, members.size());
  const int selected_port_id = members[random_member_index].port;
  ASSERT_OK_AND_ASSIGN(const auto port_name_per_port_id,
                       GetPortNamePerPortId(*control_gnmi_stub_));
  ASSERT_OK_AND_ASSIGN(const std::string port_name,
                       gutil::FindOrStatus(port_name_per_port_id,
                                           absl::StrCat(selected_port_id)));

  // Set the system in critical state by triggering a fake alarm in P4RT.
  ASSERT_TRUE(GetParam().set_critical_alarm.has_value());
  ASSERT_OK((*GetParam().set_critical_alarm)(testbed.Sut()));

  // Set admin down from control switch side (since sut is in critical state and
  // write operations are disabled) and verify watch port action kicks in.
  ASSERT_OK(SetInterfaceAdminState(*control_gnmi_stub_, port_name,
                                   AdminState::kDown));

  // TODO: Adding watch port action causes unexpected traffic
  // loss. Remove after the bug in OrchAgent is fixed.
  absl::SleepFor(absl::Seconds(5));

  // Clear the counters before the test.
  test_data_.ClearReceivedPackets();

  // Send 5000 packets and check for packet distribution.
  ASSERT_OK(SendNPacketsToSut(kNumTestPackets, test_config, members,
                              controller_port_ids, GetIrP4Info(),
                              *control_p4_session_, environment));
  test_data_.total_packets_sent = kNumTestPackets;

  // Wait for packets from the SUT to arrive.
  absl::SleepFor(kDurationToWaitForPackets);

  // For the test configuration, check the output distribution.
  {
    absl::MutexLock lock(&test_data_.mutex);
    TestInputOutput& test = test_data_.input_output_per_packet[test_config_key];
    EXPECT_EQ(test.output.size(), test_data_.total_packets_sent)
        << "Mismatch in expected: " << test_data_.total_packets_sent
        << " and actual: " << test.output.size() << "packets received for "
        << DescribeTestConfig(test_config);

    ASSERT_OK(VerifyGroupMembersFromP4Read(*sut_p4_session_, GetIrP4Info(),
                                           kGroupId, members));

    // Count the received packets and create the expected_member_ports for admin
    // down case to verify received packets.
    ASSERT_OK_AND_ASSIGN(auto num_packets_per_port,
                         CountNumPacketsPerPort(test.output));
    absl::flat_hash_set<int> expected_member_ports =
        CreateExpectedMemberPorts(members);
    expected_member_ports.erase(selected_port_id);
    ASSERT_OK(VerifyGroupMembersFromReceiveTraffic(num_packets_per_port,
                                                   expected_member_ports));

    PrettyPrintDistribution(test_config, test, test_data_, members,
                            num_packets_per_port);
  }
};

// Bring up/down the only ActionProfileGroup member and verify traffic is
// forwarded/dropped.
TEST_P(WatchPortTestFixture, VerifyWatchPortActionForSingleMember) {
  thinkit::TestEnvironment& environment =
      GetParam().testbed->GetMirrorTestbed().Environment();
  environment.SetTestCaseID("60da7a07-1217-4d63-9716-1219d62065ff");

  absl::Span<const int> controller_port_ids = GetParam().port_ids;
  const int group_size = 1;
  ASSERT_OK_AND_ASSIGN(std::vector<GroupMember> members,
                       CreateGroupMembers(group_size, controller_port_ids));

  const int input_port = controller_port_ids[kDefaultInputPortIndex];
  ASSERT_OK(SetUpInputPortForPacketReceive(*sut_p4_session_, GetIrP4Info(),
                                           input_port));

  // Programs the required router interfaces, nexthops for wcmp group.
  ASSERT_OK(pins::ProgramNextHops(environment, *sut_p4_session_, GetIrP4Info(),
                                   members));
  ASSERT_OK(pins::ProgramGroupWithMembers(environment, *sut_p4_session_,
                                           GetIrP4Info(), kGroupId, members,
                                           p4::v1::Update::INSERT));
  // Program default routing for all packets on SUT.
  ASSERT_OK(ProgramDefaultRoutes(*sut_p4_session_, GetIrP4Info(), kVrfId,
                                 p4::v1::Update::INSERT));

  // Generate test configuration, pick any field used by hashing to vary for
  // every packet so that it gets sent to all the members.
  TestConfiguration test_config = {
      .field = PacketField::kL4SrcPort,
      .ipv4 = true,
      .encapped = false,
      .inner_ipv4 = false,
      .decap = false,
  };
  ASSERT_TRUE(IsValidTestConfiguration(test_config));

  // Create test data entry.
  std::string test_config_key = TestConfigurationToPayload(test_config);
  {
    absl::MutexLock lock(&test_data_.mutex);
    test_data_.input_output_per_packet[test_config_key] = TestInputOutput{
        .config = test_config,
    };
  }

  absl::flat_hash_set<int> expected_member_ports =
      CreateExpectedMemberPorts(members);

  // Pickup the only member (index 0) in the group and toggle down/up and verify
  // traffic distribution.
  ASSERT_THAT(members, testing::SizeIs(1))
      << "Unexpected member size for single member group";
  const int single_member_port_id = members[0].port;
  ASSERT_OK_AND_ASSIGN(const auto port_name_per_port_id,
                       GetPortNamePerPortId(*control_gnmi_stub_));
  for (auto operation : {AdminState::kDown, AdminState::kUp}) {
    ASSERT_OK_AND_ASSIGN(
        const auto& port_name,
        gutil::FindOrStatus(port_name_per_port_id,
                            absl::StrCat(single_member_port_id)));
    ASSERT_OK(
        SetInterfaceAdminState(*control_gnmi_stub_, port_name, operation));

    // Clear the counters before the test.
    test_data_.ClearReceivedPackets();

    // TODO: Adding watch port up action causes unexpected traffic
    // loss. Remove after the bug in OrchAgent is fixed.
    absl::SleepFor(absl::Seconds(5));

    // Send 5000 packets and check for packet distribution.
    ASSERT_OK(SendNPacketsToSut(kNumTestPackets, test_config, members,
                                controller_port_ids, GetIrP4Info(),
                                *control_p4_session_, environment));
    test_data_.total_packets_sent = kNumTestPackets;

    // Wait for packets from the SUT to arrive.
    absl::SleepFor(kDurationToWaitForPackets);

    // For the test configuration, check the output distribution.
    {
      absl::MutexLock lock(&test_data_.mutex);
      TestInputOutput& test =
          test_data_.input_output_per_packet[test_config_key];
      if (operation == AdminState::kDown) {
        // Expect all packets to be lost for single member group watch port down
        // action.
        EXPECT_EQ(test.output.size(), 0)
            << "Expected all packets to be lost for single member group watch "
               "port down action, but received "
            << test.output.size() << " actual packets";
      } else {
        expected_member_ports.insert(single_member_port_id);
        EXPECT_EQ(test.output.size(), test_data_.total_packets_sent)
            << "Mismatch in expected: " << test_data_.total_packets_sent
            << " and actual: " << test.output.size() << " packets received for "
            << DescribeTestConfig(test_config);
      }
      ASSERT_OK_AND_ASSIGN(auto num_packets_per_port,
                           CountNumPacketsPerPort(test.output));

      ASSERT_OK(VerifyGroupMembersFromP4Read(*sut_p4_session_, GetIrP4Info(),
                                             kGroupId, members));
      ASSERT_OK(VerifyGroupMembersFromReceiveTraffic(num_packets_per_port,
                                                     expected_member_ports));
      PrettyPrintDistribution(test_config, test, test_data_, members,
                              num_packets_per_port);
    }
  }
};

// Modify ActionProfileGroup member and verify traffic is distributed
// accordingly.
TEST_P(WatchPortTestFixture, VerifyWatchPortActionForMemberModify) {
  thinkit::TestEnvironment& environment =
      GetParam().testbed->GetMirrorTestbed().Environment();
  environment.SetTestCaseID("e93160fb-be64-495b-bb4d-f06a92c51e76");

  absl::Span<const int> controller_port_ids = GetParam().port_ids;
  const int group_size = kNumWcmpMembersForTest;
  ASSERT_OK_AND_ASSIGN(std::vector<GroupMember> members,
                       CreateGroupMembers(group_size, controller_port_ids));

  const int input_port = controller_port_ids[kDefaultInputPortIndex];
  ASSERT_OK(SetUpInputPortForPacketReceive(*sut_p4_session_, GetIrP4Info(),
                                           input_port));

  // Programs the required router interfaces, nexthops for wcmp group.
  ASSERT_OK(pins::ProgramNextHops(environment, *sut_p4_session_, GetIrP4Info(),
                                   members));
  ASSERT_OK(pins::ProgramGroupWithMembers(environment, *sut_p4_session_,
                                           GetIrP4Info(), kGroupId, members,
                                           p4::v1::Update::INSERT));
  // Program default routing for all packets on SUT.
  ASSERT_OK(ProgramDefaultRoutes(*sut_p4_session_, GetIrP4Info(), kVrfId,
                                 p4::v1::Update::INSERT));

  // Generate test configuration, pick any field used by hashing to vary for
  // every packet so that it gets sent to all the members.
  TestConfiguration test_config = {
      .field = PacketField::kIpDst,
      .ipv4 = true,
      .encapped = false,
      .inner_ipv4 = false,
      .decap = false,
  };
  ASSERT_TRUE(IsValidTestConfiguration(test_config));

  // Create test data entry.
  std::string test_config_key = TestConfigurationToPayload(test_config);
  {
    absl::MutexLock lock(&test_data_.mutex);
    test_data_.input_output_per_packet[test_config_key] = TestInputOutput{
        .config = test_config,
    };
  }

  // Select one random member of the group to be brought down.
  absl::BitGen gen;
  const int random_member_index =
      absl::Uniform<int>(absl::IntervalClosedOpen, gen, 0, members.size());
  const int selected_port_id = members[random_member_index].port;
  ASSERT_OK_AND_ASSIGN(const auto port_name_per_port_id,
                       GetPortNamePerPortId(*control_gnmi_stub_));
  ASSERT_OK_AND_ASSIGN(const auto& selected_port_name,
                       gutil::FindOrStatus(port_name_per_port_id,
                                           absl::StrCat(selected_port_id)));
  ASSERT_OK(SetInterfaceAdminState(*control_gnmi_stub_, selected_port_name,
                                   AdminState::kDown));

  // Send Modify request to remove the down member from the group.
  members.erase(members.begin() + random_member_index);
  ASSERT_OK(pins::ProgramGroupWithMembers(environment, *sut_p4_session_,
                                           GetIrP4Info(), kGroupId, members,
                                           p4::v1::Update::MODIFY));
  // Bring the down member watch port up.
  ASSERT_OK(SetInterfaceAdminState(*control_gnmi_stub_, selected_port_name,
                                   AdminState::kUp));

  // TODO: Adding watch port up action causes unexpected traffic
  // loss. Remove after the bug in OrchAgent is fixed.
  absl::SleepFor(absl::Seconds(5));

  // Send 5000 packets and check for packet distribution.
  ASSERT_OK(SendNPacketsToSut(kNumTestPackets, test_config, members,
                              controller_port_ids, GetIrP4Info(),
                              *control_p4_session_, environment));
  test_data_.total_packets_sent = kNumTestPackets;

  // Wait for packets from the SUT to arrive.
  absl::SleepFor(kDurationToWaitForPackets);

  // For the test configuration, check the output distribution.
  {
    absl::MutexLock lock(&test_data_.mutex);
    TestInputOutput& test = test_data_.input_output_per_packet[test_config_key];
    EXPECT_EQ(test.output.size(), test_data_.total_packets_sent)
        << "Mismatch in expected: " << test_data_.total_packets_sent
        << " and actual: " << test.output.size() << "packets received for "
        << DescribeTestConfig(test_config);

    ASSERT_OK_AND_ASSIGN(auto num_packets_per_port,
                         CountNumPacketsPerPort(test.output));

    absl::flat_hash_set<int> expected_member_ports =
        CreateExpectedMemberPorts(members);

    ASSERT_OK(VerifyGroupMembersFromP4Read(*sut_p4_session_, GetIrP4Info(),
                                           kGroupId, members));
    ASSERT_OK(VerifyGroupMembersFromReceiveTraffic(num_packets_per_port,
                                                   expected_member_ports));
    PrettyPrintDistribution(test_config, test, test_data_, members,
                            num_packets_per_port);
  }

  // Delete default routes to prepare for delete group.
  ASSERT_OK(ProgramDefaultRoutes(*sut_p4_session_, GetIrP4Info(), kVrfId,
                                 p4::v1::Update::DELETE));

  // Delete group and verify no errors.
  ASSERT_OK(DeleteGroup(*sut_p4_session_, GetIrP4Info(), kGroupId));
};

// Add ActionProfileGroup member whose watch port is down (during create) and
// verify traffic distribution when port is down/up.
TEST_P(WatchPortTestFixture, VerifyWatchPortActionForDownPortMemberInsert) {
  thinkit::TestEnvironment& environment =
      GetParam().testbed->GetMirrorTestbed().Environment();
  environment.SetTestCaseID("e54da480-d2cc-42c6-bced-0354b5ab3329");
  absl::Span<const int> controller_port_ids = GetParam().port_ids;
  const int input_port = controller_port_ids[kDefaultInputPortIndex];
  ASSERT_OK(SetUpInputPortForPacketReceive(*sut_p4_session_, GetIrP4Info(),
                                           input_port));

  const int group_size = kNumWcmpMembersForTest;
  ASSERT_OK_AND_ASSIGN(std::vector<GroupMember> members,
                       CreateGroupMembers(group_size, controller_port_ids));
  // Select one random port from the member port ids to be brought down/up.
  absl::BitGen gen;
  const int random_member_index =
      absl::Uniform<int>(absl::IntervalClosedOpen, gen, 0, members.size());
  const int selected_port_id = members[random_member_index].port;
  ASSERT_OK_AND_ASSIGN(const auto port_name_per_port_id,
                       GetPortNamePerPortId(*control_gnmi_stub_));
  ASSERT_OK_AND_ASSIGN(const auto& selected_port_name,
                       gutil::FindOrStatus(port_name_per_port_id,
                                           absl::StrCat(selected_port_id)));
  // Bring the port down before the group and members are created.
  ASSERT_OK(SetInterfaceAdminState(*control_gnmi_stub_, selected_port_name,
                                   AdminState::kDown));

  // Programs the required router interfaces, nexthops for wcmp group.
  ASSERT_OK(pins::ProgramNextHops(environment, *sut_p4_session_, GetIrP4Info(),
                                   members));
  ASSERT_OK(pins::ProgramGroupWithMembers(environment, *sut_p4_session_,
                                           GetIrP4Info(), kGroupId, members,
                                           p4::v1::Update::INSERT));
  // Program default routing for all packets on SUT.
  ASSERT_OK(ProgramDefaultRoutes(*sut_p4_session_, GetIrP4Info(), kVrfId,
                                 p4::v1::Update::INSERT));

  // Generate test configuration, pick any field used by hashing to vary for
  // every packet so that it gets sent to all the members.
  TestConfiguration test_config = {
      .field = PacketField::kL4DstPort,
      .ipv4 = true,
      .encapped = false,
      .inner_ipv4 = false,
      .decap = false,
  };
  ASSERT_TRUE(IsValidTestConfiguration(test_config));

  // Create test data entry.
  std::string test_config_key = TestConfigurationToPayload(test_config);
  {
    absl::MutexLock lock(&test_data_.mutex);
    test_data_.input_output_per_packet[test_config_key] = TestInputOutput{
        .config = test_config,
    };
  }

  for (auto operation : {AdminState::kDown, AdminState::kUp}) {
    // Down operation is a no-op here since the port is already down.
    ASSERT_OK(SetInterfaceAdminState(*control_gnmi_stub_, selected_port_name,
                                     operation));

    // Clear the counters before the test.
    test_data_.ClearReceivedPackets();

    // TODO: Adding watch port up action causes unexpected traffic
    // loss. Remove after the bug in OrchAgent is fixed.
    absl::SleepFor(absl::Seconds(5));

    // Send 5000 packets and check for packet distribution.
    ASSERT_OK(SendNPacketsToSut(kNumTestPackets, test_config, members,
                                controller_port_ids, GetIrP4Info(),
                                *control_p4_session_, environment));
    test_data_.total_packets_sent = kNumTestPackets;

    // Wait for packets from the SUT to arrive.
    absl::SleepFor(kDurationToWaitForPackets);

    // For the test configuration, check the output distribution.
    {
      absl::MutexLock lock(&test_data_.mutex);
      TestInputOutput& test =
          test_data_.input_output_per_packet[test_config_key];
      EXPECT_EQ(test.output.size(), test_data_.total_packets_sent)
          << "Mismatch in expected: " << test_data_.total_packets_sent
          << " and actual: " << test.output.size() << "packets received for "
          << DescribeTestConfig(test_config);

      absl::flat_hash_set<int> expected_member_ports =
          CreateExpectedMemberPorts(members);
      // Remove the selected member from expected_member_ports for admin
      // down case.
      if (operation == AdminState::kDown) {
        expected_member_ports.erase(selected_port_id);
      }
      ASSERT_OK_AND_ASSIGN(auto num_packets_per_port,
                           CountNumPacketsPerPort(test.output));

      ASSERT_OK(VerifyGroupMembersFromP4Read(*sut_p4_session_, GetIrP4Info(),
                                             kGroupId, members));
      ASSERT_OK(VerifyGroupMembersFromReceiveTraffic(num_packets_per_port,
                                                     expected_member_ports));
      PrettyPrintDistribution(test_config, test, test_data_, members,
                              num_packets_per_port);
    }
  }
}

}  // namespace
}  // namespace pins
