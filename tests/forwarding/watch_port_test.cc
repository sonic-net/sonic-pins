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
#include <optional>
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
#include "gutil/collections.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/p4rt/p4rt_port.h"
#include "lib/validator/validator_lib.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_pdpi/pd.h"
#include "p4_pdpi/string_encodings/decimal_string.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "re2/re2.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "tests/forwarding/group_programming_util.h"
#include "tests/forwarding/packet_test_util.h"
#include "tests/forwarding/util.h"
#include "tests/lib/p4rt_fixed_table_programming_helper.h"
#include "tests/thinkit_sanity_tests.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/mirror_testbed_fixture.h"
#include "thinkit/switch.h"
#include "thinkit/test_environment.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
// Tests for the watchport functionality in Action Profile Group operation.

namespace pins {

namespace {

using ::testing::UnorderedPointwise;

MATCHER(KeyEq, "") {
  return ::testing::get<0>(arg).first == ::testing::get<1>(arg);
}

// Admin down/up state used for interfaces.
enum class InterfaceState {
  kDown,
  kUp,
};

// Admin status path (partial match) string in the form of "admin-status":"UP".
constexpr LazyRE2 kAdminStatusPathMatch = {R"("admin-status":\"(\w+)\")"};

// Oper status path (partial match) string in the form of "oper-status":"UP".
constexpr LazyRE2 kOperStatusPathMatch = {R"("oper-status":\"(\w+)\")"};

// Group id used in this test.
constexpr absl::string_view kGroupId = "group-1";

// Vrf used in the test.
constexpr absl::string_view kVrfId = "vrf-1";

// Time to wait for membership updates after link event triggers.
constexpr absl::Duration kDurationToWaitForMembershipUpdates = absl::Seconds(2);

// Time to wait after which received packets are processed.
constexpr absl::Duration kDurationToWaitForPackets = absl::Seconds(5);

// Number of members used in the test.
constexpr int kNumWcmpMembersForTest = 5;

// Number of packets used in the test.
constexpr int kNumTestPackets = 5000;

// Default input port index of the group members vector, on which packets
// arrive.
constexpr int kDefaultInputPortIndex = 0;

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
    int group_size,
    absl::Span<const pins_test::P4rtPortId> controller_port_ids) {
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
      members.push_back(pins::GroupMember{
          .weight = 0,
          .port = static_cast<int>(
              controller_port_ids[i].GetOpenConfigEncoding())});
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

// Program L3 Admit table for the given mac-address.
absl::Status ProgramL3Admit(pdpi::P4RuntimeSession& p4_session,
                            const pdpi::IrP4Info& ir_p4info,
                            const L3AdmitOptions& options) {
  p4::v1::WriteRequest write_request;
  ASSIGN_OR_RETURN(
      *write_request.add_updates(),
      L3AdmitTableUpdate(ir_p4info, p4::v1::Update::INSERT, options));
  return pdpi::SetMetadataAndSendPiWriteRequest(&p4_session, write_request);
}

// Sends N packets from the control switch to sut at a rate of 500 packets/sec.
absl::Status SendNPacketsToSut(int num_packets,
                               const TestConfiguration &test_config,
                               absl::Span<const GroupMember> members,
                               absl::Span<const pins_test::P4rtPortId> port_ids,
                               const pdpi::IrP4Info &ir_p4info,
                               pdpi::P4RuntimeSession &p4_session,
                               thinkit::TestEnvironment &test_environment) {
  const absl::Time start_time = absl::Now();
  for (int i = 0; i < num_packets; i++) {
    // Rate limit to 500 packets per second.
    auto earliest_send_time = start_time + (i * absl::Seconds(1) / 500);
    absl::SleepFor(earliest_send_time - absl::Now());

    // Vary the port on which to send the packet if the hash field selected is
    // input port.
    pins_test::P4rtPortId port = port_ids[kDefaultInputPortIndex];
    if (test_config.field == PacketField::kInputPort) {
      port = port_ids[i % members.size()];
    }

    ASSIGN_OR_RETURN(packetlib::Packet packet,
                     pins::GenerateIthPacket(test_config, i));
    ASSIGN_OR_RETURN(std::string raw_packet, SerializePacket(packet));
    RETURN_IF_ERROR(InjectEgressPacket(port.GetP4rtEncoding(), raw_packet,
                                       ir_p4info, &p4_session,
                                       /*packet_delay=*/std::nullopt));

    dvaas::Packet p;
    p.set_port(port.GetP4rtEncoding());
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

// Returns the current admin state of the interface.
absl::StatusOr<InterfaceState> GetInterfaceState(
    gnmi::gNMI::StubInterface& gnmi_stub, const LazyRE2& state_path_match,
    absl::string_view if_name) {
  const std::string if_state_path =
      absl::StrCat("interfaces/interface[name=", if_name, "]/state");
  ASSIGN_OR_RETURN(const std::string state_path_response,
                   pins_test::GetGnmiStatePathInfo(
                       &gnmi_stub, if_state_path,
                       /*resp_parse_str=*/"openconfig-interfaces:state"));

  // Status is part of the overall interface state path response.
  // Extract out the admin or oper status, for example, "admin-status":"UP"
  // tuple.
  std::string status_str;
  if (RE2::PartialMatch(state_path_response, *state_path_match, &status_str)) {
    if (status_str == "UP") {
      return InterfaceState::kUp;
    } else if (status_str == "DOWN") {
      return InterfaceState::kDown;
    }
  }
  return absl::UnknownError(absl::Substitute(
      "Unable to get the status path: $0 for interface: $1, state path "
      "response: $2",
      state_path_match->pattern(), if_name, state_path_response));
}
// Verifies the admin or oper status of the interface is the same as
// "desired_state" in the state verification path.
absl::Status VerifyInterfaceState(gnmi::gNMI::StubInterface& gnmi_stub,
                                  absl::string_view if_name,
                                  const LazyRE2& state_path_match,
                                  InterfaceState desired_state) {
  // Poll with a delay for the oper state to take effect.
  absl::Time timeout = absl::Now() + absl::Seconds(15);
  InterfaceState current_state;
  do {
    if (absl::Now() > timeout) {
      return absl::DeadlineExceededError(absl::Substitute(
          "Unable to validate interface: $0 to state: $1", if_name,
          desired_state == InterfaceState::kDown ? "DOWN" : "UP"));
    }
    absl::SleepFor(absl::Seconds(1));
    ASSIGN_OR_RETURN(current_state,
                     GetInterfaceState(gnmi_stub, state_path_match, if_name));
  } while (current_state != desired_state);
  return absl::OkStatus();
}

// Verifies the given interface's desired admin status is reflected in the
// state path.
absl::Status VerifyInterfaceAdminState(gnmi::gNMI::StubInterface& gnmi_stub,
                                       absl::string_view if_name,
                                       InterfaceState desired_state) {
  return VerifyInterfaceState(gnmi_stub, if_name, kAdminStatusPathMatch,
                              desired_state);
}

// Verifies the given interface's desired oper status is reflected in the
// state path and collects port debug data for failed UP state.
absl::Status VerifyInterfaceOperState(gnmi::gNMI::StubInterface& gnmi_stub,
                                      thinkit::MirrorTestbed& testbed,
                                      absl::string_view if_name,
                                      InterfaceState desired_state) {
  absl::Status oper_status = VerifyInterfaceState(
      gnmi_stub, if_name, kOperStatusPathMatch, desired_state);
  // Collect port debug data if interface did not come UP.
  if (!oper_status.ok() && desired_state == InterfaceState::kUp) {
    const std::vector<std::string> interface = {std::string(if_name)};
    absl::Status sut_port_up = pins_test::PortsUp(testbed.Sut(), interface);
    LOG_IF(WARNING, !sut_port_up.ok()) << sut_port_up;
    absl::Status control_port_up =
        pins_test::PortsUp(testbed.ControlSwitch(), interface);
    LOG_IF(WARNING, !control_port_up.ok()) << control_port_up;
  }
  return oper_status;
}

// Sets the admin state of the interface to UP/DOWN using GNMI config path.
// Queries the  state path to verify if the desired state is achieved or not.
absl::Status SetInterfaceAdminState(gnmi::gNMI::StubInterface& gnmi_stub,
                                    absl::string_view if_name,
                                    InterfaceState admin_state) {
  ASSIGN_OR_RETURN(
      InterfaceState current_admin_state,
      GetInterfaceState(gnmi_stub, kAdminStatusPathMatch, if_name));
      if (current_admin_state == admin_state) {
    return absl::OkStatus();
  }

  const std::string config_value =
      admin_state == InterfaceState::kDown ? "false" : "true";
  const std::string if_admin_config_path =
      absl::StrCat("interfaces/interface[name=", if_name, "]/config/enabled");
  const std::string if_status =
      admin_state == InterfaceState::kDown ? "DOWN" : "UP";
  LOG(INFO) << "Setting interface " << if_name << " to admin " << if_status;
  RETURN_IF_ERROR(SetGnmiConfigPath(
      &gnmi_stub, if_admin_config_path, pins_test::GnmiSetType::kUpdate,
      absl::Substitute("{\"enabled\":$0}", config_value)));
  return VerifyInterfaceAdminState(gnmi_stub, if_name, admin_state);
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

  ASSERT_OK(testbed.Environment().StoreTestArtifact(
      "p4info.pb.txt", GetParam().p4_info.DebugString()));

  // Setup SUT & control switch.

  ASSERT_OK_AND_ASSIGN(sut_p4_session_,
                       pdpi::P4RuntimeSession::CreateWithP4InfoAndClearTables(
                           testbed.Sut(), GetParam().p4_info));
  ASSERT_OK_AND_ASSIGN(control_p4_session_,
                       pdpi::P4RuntimeSession::CreateWithP4InfoAndClearTables(
                           testbed.ControlSwitch(), GetParam().p4_info));
  ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(GetParam().p4_info));
  ASSERT_OK(SetUpSut(*sut_p4_session_, ir_p4info, kVrfId));
  ASSERT_OK(SetUpControlSwitch(*control_p4_session_, ir_p4info));

  // Create GNMI stub for admin operations.
  ASSERT_OK_AND_ASSIGN(sut_gnmi_stub_, testbed.Sut().CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(control_gnmi_stub_,
                       testbed.ControlSwitch().CreateGnmiStub());

  // Start the receiver thread for control switch to listen for packets from
  // SUT, this thread is terminated in the TearDown.
  receive_packet_thread_ = std::thread([&, ir_p4info]() {
    p4::v1::StreamMessageResponse pi_response;
    while (control_p4_session_->StreamChannelRead(pi_response)) {
      absl::MutexLock lock(&test_data_.mutex);
      sai::StreamMessageResponse pd_response;
      ASSERT_OK(pdpi::PiStreamMessageResponseToPd(ir_p4info, pi_response,
                                                  &pd_response))
          << " PacketIn PI to PD failed: ";
      if (!pd_response.has_packet()) {
        LOG(WARNING)
            << " Received unexpected stream message (expected packet in): "
            << pd_response.DebugString();
        continue;
      }
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

  // Do some general cleanup for control switch.
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
      EXPECT_OK(SetInterfaceAdminState(*control_gnmi_stub_, name,
                                       InterfaceState::kUp));
    }
  }

  // Reboot the switch, if Sut is in critical state.
  if (sut_gnmi_stub_ && IsSwitchInCriticalState(*sut_gnmi_stub_)) {
    // Grab logs on the switches before the reboot.
    ASSERT_OK(testbed.SaveSwitchLogs("before_reboot_"));
    LOG(INFO) << "Switch is in critical state, rebooting the switch.";
    pins_test::TestGnoiSystemColdReboot(testbed.GetMirrorTestbed().Sut());
    pins_test::TestGnoiSystemColdReboot(
        testbed.GetMirrorTestbed().ControlSwitch());

    testbed.TearDown();
    return;
  }

  // Clear SUT table entries.
  if (sut_p4_session_ != nullptr) {
    EXPECT_OK(pdpi::ClearTableEntries(sut_p4_session_.get()));
    EXPECT_OK(sut_p4_session_->Finish());
  }

  testbed.TearDown();
}

namespace {

// Verifies basic WCMP behavior by programming a group with multiple members
// with random weights and ensuring that all members receive some part of
// the sent traffic.
TEST_P(WatchPortTestFixture, VerifyBasicWcmpPacketDistribution) {
  thinkit::TestEnvironment& environment =
      GetParam().testbed->GetMirrorTestbed().Environment();

  ASSERT_OK_AND_ASSIGN(
      std::vector<pins_test::P4rtPortId> controller_port_ids,
      pins_test::GetMatchingP4rtPortIds(*sut_gnmi_stub_,
                                        pins_test::IsEnabledEthernetInterface));
  const int group_size = kNumWcmpMembersForTest;
  ASSERT_OK_AND_ASSIGN(std::vector<GroupMember> members,
                       CreateGroupMembers(group_size, controller_port_ids));
  ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(GetParam().p4_info));

  // Programs the required router interfaces, nexthops for wcmp group.
  ASSERT_OK(pins::ProgramNextHops(environment, *sut_p4_session_, ir_p4info,
                                   members));
  ASSERT_OK(pins::ProgramGroupWithMembers(environment, *sut_p4_session_,
					   ir_p4info, kGroupId, members,
                                           p4::v1::Update::INSERT))
      << "Failed to program WCMP group: ";

  // Allow the destination mac address to L3.
  ASSERT_OK(ProgramL3Admit(
      *sut_p4_session_, ir_p4info,
      L3AdmitOptions{
          .priority = 2070,
          .dst_mac = std ::make_pair(pins::GetIthDstMac(0).ToString(),
                                     "FF:FF:FF:FF:FF:FF"),
      }));

  // Program default routing for all packets on SUT.
  ASSERT_OK(ProgramDefaultRoutes(*sut_p4_session_, ir_p4info, kVrfId,
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
                              controller_port_ids, ir_p4info,
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

    ASSERT_OK(VerifyGroupMembersFromP4Read(*sut_p4_session_, ir_p4info,
                                           kGroupId, members));

    // Verifies the actual members inferred from receive traffic matches the
    // expected members.
    ASSERT_THAT(num_packets_per_port,
                UnorderedPointwise(KeyEq(), expected_member_ports));
    PrettyPrintDistribution(test_config, test, test_data_, members,
                            num_packets_per_port);
  }
}

// Bring down/up ActionProfileGroup member and verify traffic is distributed
// only to the up ports.
TEST_P(WatchPortTestFixture, VerifyBasicWatchPortAction) {
  thinkit::TestEnvironment& environment =
      GetParam().testbed->GetMirrorTestbed().Environment();

  ASSERT_OK_AND_ASSIGN(
      std::vector<pins_test::P4rtPortId> controller_port_ids,
      pins_test::GetMatchingP4rtPortIds(*sut_gnmi_stub_,
                                        pins_test::IsEnabledEthernetInterface));
  const int group_size = kNumWcmpMembersForTest;
  ASSERT_OK_AND_ASSIGN(std::vector<GroupMember> members,
                       CreateGroupMembers(group_size, controller_port_ids));
  ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(GetParam().p4_info));

  // Programs the required router interfaces, nexthops for wcmp group.
  ASSERT_OK(pins::ProgramNextHops(environment, *sut_p4_session_, ir_p4info,
                                   members));
  ASSERT_OK(pins::ProgramGroupWithMembers(environment, *sut_p4_session_,
                                           ir_p4info, kGroupId, members,
                                           p4::v1::Update::INSERT));

  // Allow the destination mac address to L3.
  ASSERT_OK(ProgramL3Admit(
      *sut_p4_session_, ir_p4info,
      L3AdmitOptions{
          .priority = 2070,
          .dst_mac = std ::make_pair(pins::GetIthDstMac(0).ToString(),
                                     "FF:FF:FF:FF:FF:FF"),
      }));

  // Program default routing for all packets on SUT.
  ASSERT_OK(ProgramDefaultRoutes(*sut_p4_session_, ir_p4info, kVrfId,
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
  for (auto operation : {InterfaceState::kDown, InterfaceState::kUp}) {  
    ASSERT_OK_AND_ASSIGN(const auto& port_name,
                         gutil::FindOrStatus(port_name_per_port_id,
                                             absl::StrCat(selected_port_id)));
    ASSERT_OK(
        SetInterfaceAdminState(*control_gnmi_stub_, port_name, operation));

    // Verify the oper status is reflected on the SUT.
    ASSERT_OK(VerifyInterfaceOperState(*sut_gnmi_stub_,
                                       GetParam().testbed->GetMirrorTestbed(),
                                       port_name, operation));

    // Wait for the membership changes to be processed.
    absl::SleepFor(kDurationToWaitForMembershipUpdates);

    // Clear the counters before the test.
    test_data_.ClearReceivedPackets();

    // Send 5000 packets and check for packet distribution.
    ASSERT_OK(SendNPacketsToSut(kNumTestPackets, test_config, members,
                                controller_port_ids, ir_p4info,
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
      if (operation == InterfaceState::kDown) {
        expected_member_ports.erase(selected_port_id);
      } else {
        expected_member_ports.insert(selected_port_id);
      }

      ASSERT_OK(VerifyGroupMembersFromP4Read(*sut_p4_session_, ir_p4info,
                                             kGroupId, members));
      // Verifies the actual members inferred from receive traffic matches the
      // expected members.
      ASSERT_THAT(num_packets_per_port,
                  UnorderedPointwise(KeyEq(), expected_member_ports));
      PrettyPrintDistribution(test_config, test, test_data_, members,
                              num_packets_per_port);
    }
  }
}

// Bring down APG member (when in critical state) and verify traffic is
// distributed only to the up ports.
TEST_P(WatchPortTestFixture, VerifyWatchPortActionInCriticalState) {
  // Validate that the function to raise critical state exists to run this test.
  if (!GetParam().set_critical_alarm.has_value()) {
    GTEST_SKIP() << "Critical state related test skipped because set critical "
                    "state function is not defined.";
  }
  thinkit::MirrorTestbed& testbed = GetParam().testbed->GetMirrorTestbed();
  thinkit::TestEnvironment& environment = testbed.Environment();

  ASSERT_OK_AND_ASSIGN(
      std::vector<pins_test::P4rtPortId> controller_port_ids,
      pins_test::GetMatchingP4rtPortIds(*sut_gnmi_stub_,
                                        pins_test::IsEnabledEthernetInterface));
  const int group_size = kNumWcmpMembersForTest;
  ASSERT_OK_AND_ASSIGN(std::vector<GroupMember> members,
                       CreateGroupMembers(group_size, controller_port_ids));
  ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(GetParam().p4_info));

  // Program the required router interfaces, nexthops for wcmp group.
  ASSERT_OK(pins::ProgramNextHops(environment, *sut_p4_session_, ir_p4info,
                                   members));
  ASSERT_OK(pins::ProgramGroupWithMembers(environment, *sut_p4_session_,
                                           ir_p4info, kGroupId, members,
                                           p4::v1::Update::INSERT));

  // Allow the destination mac address to L3.
  ASSERT_OK(ProgramL3Admit(
      *sut_p4_session_, ir_p4info,
      L3AdmitOptions{
          .priority = 2070,
          .dst_mac = std ::make_pair(pins::GetIthDstMac(0).ToString(),
                                     "FF:FF:FF:FF:FF:FF"),
      }));

  // Program default routing for all packets on SUT.
  ASSERT_OK(ProgramDefaultRoutes(*sut_p4_session_, ir_p4info, kVrfId,
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
                                   InterfaceState::kDown));
  // Verify the oper status is reflected on the SUT.
  ASSERT_OK(VerifyInterfaceOperState(*sut_gnmi_stub_,
                                     GetParam().testbed->GetMirrorTestbed(),
                                     port_name, InterfaceState::kDown));

  // Wait for the membership changes to be processed.
  absl::SleepFor(kDurationToWaitForMembershipUpdates);

  // Clear the counters before the test.
  test_data_.ClearReceivedPackets();

  // Send 5000 packets and check for packet distribution.
  ASSERT_OK(SendNPacketsToSut(kNumTestPackets, test_config, members,
                              controller_port_ids, ir_p4info,
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

    ASSERT_OK(VerifyGroupMembersFromP4Read(*sut_p4_session_, ir_p4info,
                                           kGroupId, members));

    // Count the received packets and create the expected_member_ports for admin
    // down case to verify received packets.
    ASSERT_OK_AND_ASSIGN(auto num_packets_per_port,
                         CountNumPacketsPerPort(test.output));
    absl::flat_hash_set<int> expected_member_ports =
        CreateExpectedMemberPorts(members);
    expected_member_ports.erase(selected_port_id);

    // Verifies the actual members inferred from receive traffic matches the
    // expected members.
    ASSERT_THAT(num_packets_per_port,
                UnorderedPointwise(KeyEq(), expected_member_ports));
    PrettyPrintDistribution(test_config, test, test_data_, members,
                            num_packets_per_port);
  }
};

// Bring up/down the only ActionProfileGroup member and verify traffic is
// forwarded/dropped.
TEST_P(WatchPortTestFixture, VerifyWatchPortActionForSingleMember) {
  thinkit::TestEnvironment& environment =
      GetParam().testbed->GetMirrorTestbed().Environment();

  ASSERT_OK_AND_ASSIGN(
      std::vector<pins_test::P4rtPortId> controller_port_ids,
      pins_test::GetMatchingP4rtPortIds(*sut_gnmi_stub_,
                                        pins_test::IsEnabledEthernetInterface));
  const int group_size = 1;
  ASSERT_OK_AND_ASSIGN(std::vector<GroupMember> members,
                       CreateGroupMembers(group_size, controller_port_ids));
  ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(GetParam().p4_info));

  // Programs the required router interfaces, nexthops for wcmp group.
  ASSERT_OK(pins::ProgramNextHops(environment, *sut_p4_session_, ir_p4info,
                                   members));
  ASSERT_OK(pins::ProgramGroupWithMembers(environment, *sut_p4_session_,
                                           ir_p4info, kGroupId, members,
                                           p4::v1::Update::INSERT));

  // Allow the destination mac address to L3.
  ASSERT_OK(ProgramL3Admit(
      *sut_p4_session_, ir_p4info,
      L3AdmitOptions{
          .priority = 2070,
          .dst_mac = std ::make_pair(pins::GetIthDstMac(0).ToString(),
                                     "FF:FF:FF:FF:FF:FF"),
      }));

  // Program default routing for all packets on SUT.
  ASSERT_OK(ProgramDefaultRoutes(*sut_p4_session_, ir_p4info, kVrfId,
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
  for (auto operation : {InterfaceState::kDown, InterfaceState::kUp}) {
    ASSERT_OK_AND_ASSIGN(
        const auto& port_name,
        gutil::FindOrStatus(port_name_per_port_id,
                            absl::StrCat(single_member_port_id)));
    ASSERT_OK(
        SetInterfaceAdminState(*control_gnmi_stub_, port_name, operation));

    // Verify the oper status is reflected on the SUT.
    ASSERT_OK(VerifyInterfaceOperState(*sut_gnmi_stub_,
                                       GetParam().testbed->GetMirrorTestbed(),
                                       port_name, operation));

    // Wait for the membership changes to be processed.
    absl::SleepFor(kDurationToWaitForMembershipUpdates);

    // Clear the counters before the test.
    test_data_.ClearReceivedPackets();

    // Send 5000 packets and check for packet distribution.
    ASSERT_OK(SendNPacketsToSut(kNumTestPackets, test_config, members,
                                controller_port_ids, ir_p4info,
                                *control_p4_session_, environment));
    test_data_.total_packets_sent = kNumTestPackets;

    // Wait for packets from the SUT to arrive.
    absl::SleepFor(kDurationToWaitForPackets);

    // For the test configuration, check the output distribution.
    {
      absl::MutexLock lock(&test_data_.mutex);
      TestInputOutput& test =
          test_data_.input_output_per_packet[test_config_key];
      if (operation == InterfaceState::kDown) {
        // Expect all packets to be lost for single member group watch port down
        // action.
        EXPECT_EQ(test.output.size(), 0)
            << "Expected all packets to be lost for single member group watch "
               "port down action, but received "
            << test.output.size() << " actual packets";
        expected_member_ports.erase(single_member_port_id);
      } else {
        expected_member_ports.insert(single_member_port_id);
        EXPECT_EQ(test.output.size(), test_data_.total_packets_sent)
            << "Mismatch in expected: " << test_data_.total_packets_sent
            << " and actual: " << test.output.size() << " packets received for "
            << DescribeTestConfig(test_config);
      }
      ASSERT_OK_AND_ASSIGN(auto num_packets_per_port,
                           CountNumPacketsPerPort(test.output));

      ASSERT_OK(VerifyGroupMembersFromP4Read(*sut_p4_session_, ir_p4info,
                                             kGroupId, members));

      // Verifies the actual members inferred from receive traffic matches the
      // expected members.
      ASSERT_THAT(num_packets_per_port,
                  UnorderedPointwise(KeyEq(), expected_member_ports));
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

  ASSERT_OK_AND_ASSIGN(
      std::vector<pins_test::P4rtPortId> controller_port_ids,
      pins_test::GetMatchingP4rtPortIds(*sut_gnmi_stub_,
                                        pins_test::IsEnabledEthernetInterface));
  const int group_size = kNumWcmpMembersForTest;
  ASSERT_OK_AND_ASSIGN(std::vector<GroupMember> members,
                       CreateGroupMembers(group_size, controller_port_ids));
  ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(GetParam().p4_info));

  // Programs the required router interfaces, nexthops for wcmp group.
  ASSERT_OK(pins::ProgramNextHops(environment, *sut_p4_session_, ir_p4info,
                                   members));
  ASSERT_OK(pins::ProgramGroupWithMembers(environment, *sut_p4_session_,
                                           ir_p4info, kGroupId, members,
                                           p4::v1::Update::INSERT));

  // Allow the destination mac address to L3.
  ASSERT_OK(ProgramL3Admit(
      *sut_p4_session_, ir_p4info,
      L3AdmitOptions{
          .priority = 2070,
          .dst_mac = std ::make_pair(pins::GetIthDstMac(0).ToString(),
                                     "FF:FF:FF:FF:FF:FF"),
      }));

  // Program default routing for all packets on SUT.
  ASSERT_OK(ProgramDefaultRoutes(*sut_p4_session_, ir_p4info, kVrfId,
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
                                   InterfaceState::kDown));
  // Verify the oper status is reflected on the SUT.
  ASSERT_OK(VerifyInterfaceOperState(
      *sut_gnmi_stub_, GetParam().testbed->GetMirrorTestbed(),
      selected_port_name, InterfaceState::kDown));

  // Send Modify request to remove the down member from the group.
  members.erase(members.begin() + random_member_index);
  ASSERT_OK(pins::ProgramGroupWithMembers(environment, *sut_p4_session_,
                                           ir_p4info, kGroupId, members,
                                           p4::v1::Update::MODIFY));
  // Bring the down member watch port up.
  ASSERT_OK(SetInterfaceAdminState(*control_gnmi_stub_, selected_port_name,
                                   InterfaceState::kUp));
  // Verify the oper status is reflected on the SUT.
  ASSERT_OK(VerifyInterfaceOperState(*sut_gnmi_stub_,
                                     GetParam().testbed->GetMirrorTestbed(),
                                     selected_port_name, InterfaceState::kUp));

  // Wait for the membership changes to be processed.
  absl::SleepFor(kDurationToWaitForMembershipUpdates);

  // Send 5000 packets and check for packet distribution.
  ASSERT_OK(SendNPacketsToSut(kNumTestPackets, test_config, members,
                              controller_port_ids, ir_p4info,
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

    ASSERT_OK(VerifyGroupMembersFromP4Read(*sut_p4_session_, ir_p4info,
                                           kGroupId, members));

    // Verifies the actual members inferred from receive traffic matches the
    // expected members.
    ASSERT_THAT(num_packets_per_port,
                UnorderedPointwise(KeyEq(), expected_member_ports));
    PrettyPrintDistribution(test_config, test, test_data_, members,
                            num_packets_per_port);
  }

  // Delete default routes to prepare for delete group.
  ASSERT_OK(ProgramDefaultRoutes(*sut_p4_session_, ir_p4info, kVrfId,
                                 p4::v1::Update::DELETE));

  // Delete group and verify no errors.
  ASSERT_OK(DeleteGroup(*sut_p4_session_, ir_p4info, kGroupId));
};

// Add ActionProfileGroup member whose watch port is down (during create) and
// verify traffic distribution when port is down/up.
TEST_P(WatchPortTestFixture, VerifyWatchPortActionForDownPortMemberInsert) {
  thinkit::TestEnvironment& environment =
      GetParam().testbed->GetMirrorTestbed().Environment();

  ASSERT_OK_AND_ASSIGN(
      std::vector<pins_test::P4rtPortId> controller_port_ids,
      pins_test::GetMatchingP4rtPortIds(*sut_gnmi_stub_,
                                        pins_test::IsEnabledEthernetInterface));
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
                                   InterfaceState::kDown));
  // Verify the oper status is reflected on the SUT.
  ASSERT_OK(VerifyInterfaceOperState(
      *sut_gnmi_stub_, GetParam().testbed->GetMirrorTestbed(),
      selected_port_name, InterfaceState::kDown));

  // Programs the required router interfaces, nexthops for wcmp group.
  ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(GetParam().p4_info));
  ASSERT_OK(pins::ProgramNextHops(environment, *sut_p4_session_, ir_p4info,
                                   members));
  ASSERT_OK(pins::ProgramGroupWithMembers(environment, *sut_p4_session_,
                                           ir_p4info, kGroupId, members,
                                           p4::v1::Update::INSERT));

  // Allow the destination mac address to L3.
  ASSERT_OK(ProgramL3Admit(
      *sut_p4_session_, ir_p4info,
      L3AdmitOptions{
          .priority = 2070,
          .dst_mac = std ::make_pair(pins::GetIthDstMac(0).ToString(),
                                     "FF:FF:FF:FF:FF:FF"),
      }));

  // Program default routing for all packets on SUT.
  ASSERT_OK(ProgramDefaultRoutes(*sut_p4_session_, ir_p4info, kVrfId,
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

  for (auto operation : {InterfaceState::kDown, InterfaceState::kUp}) {
    // Down operation is a no-op here since the port is already down.
    ASSERT_OK(SetInterfaceAdminState(*control_gnmi_stub_, selected_port_name,
                                     operation));

    // Verify the oper status is reflected on the SUT.
    ASSERT_OK(VerifyInterfaceOperState(*sut_gnmi_stub_,
                                       GetParam().testbed->GetMirrorTestbed(),
                                       selected_port_name, operation));

    // Wait for the membership changes to be processed.
    absl::SleepFor(kDurationToWaitForMembershipUpdates);

    // Clear the counters before the test.
    test_data_.ClearReceivedPackets();

    // Send 5000 packets and check for packet distribution.
    ASSERT_OK(SendNPacketsToSut(kNumTestPackets, test_config, members,
                                controller_port_ids, ir_p4info,
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
      if (operation == InterfaceState::kDown) {
        expected_member_ports.erase(selected_port_id);
      }
      ASSERT_OK_AND_ASSIGN(auto num_packets_per_port,
                           CountNumPacketsPerPort(test.output));

      ASSERT_OK(VerifyGroupMembersFromP4Read(*sut_p4_session_, ir_p4info,
                                             kGroupId, members));
      // Verifies the actual members inferred from receive traffic matches the
      // expected members.
      ASSERT_THAT(num_packets_per_port,
                  UnorderedPointwise(KeyEq(), expected_member_ports));
      PrettyPrintDistribution(test_config, test, test_data_, members,
                              num_packets_per_port);
    }
  }
}

}  // namespace
}  // namespace pins
