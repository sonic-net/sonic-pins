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

#include "tests/sflow/sflow_test.h"

#include <algorithm>
#include <bitset>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <thread>  // NOLINT: Need threads (instead of fiber) for upstream code.
#include <utility>
#include <vector>

#include "absl/cleanup/cleanup.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/ascii.h"
#include "absl/strings/match.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/synchronization/notification.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "artifacts/otg.grpc.pb.h"
#include "artifacts/otg.pb.h"
#include "gmock/gmock.h"
#include "grpcpp/client_context.h"
#include "gtest/gtest.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/otg_helper.h"
#include "lib/utils/json_utils.h"
#include "lib/validator/validator_lib.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/netaddr/ipv4_address.h"
#include "p4_infra/netaddr/mac_address.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4_infra/p4_pdpi/p4_runtime_session_extras.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_infra/p4_pdpi/pd.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "tests/forwarding/group_programming_util.h"
#include "tests/forwarding/util.h"
#include "tests/integration/system/nsf/compare_p4flows.h"
#include "tests/integration/system/nsf/interfaces/image_config_params.h"
#include "tests/integration/system/nsf/util.h"
#include "tests/lib/p4rt_fixed_table_programming_helper.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "tests/qos/gnmi_parsers.h"
#include "tests/qos/qos_test_util.h"
#include "tests/sflow/sflow_breakout_test.h"
#include "tests/sflow/sflow_util.h"
#include "tests/thinkit_sanity_tests.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/proto/generic_testbed.pb.h"
#include "thinkit/ssh_client.h"
#include "thinkit/switch.h"
#include "thinkit/test_environment.h"

namespace pins {

namespace {

using ::gutil::IsOkAndHolds;
using ::testing::Eq;
using ::testing::Gt;
using ::testing::HasSubstr;
using ::testing::UnorderedElementsAreArray;

using ::grpc::ClientContext;
using ::otg::GetConfigResponse;
using ::otg::Openapi;
using ::otg::SetConfigRequest;
using ::otg::SetConfigResponse;
using ::otg::StateTrafficFlowTransmit;

using ::pins_test::otg_helper::AddEthernetHeader;
using ::pins_test::otg_helper::AddIPv4Header;
using ::pins_test::otg_helper::AddPorts;
using ::pins_test::otg_helper::CreateFlow;
using ::pins_test::otg_helper::SetFlowDuration;
using ::pins_test::otg_helper::SetFlowRatePps;
using ::pins_test::otg_helper::SetFlowSize;
using ::pins_test::otg_helper::SetTrafficTransmissionState;

// Number of packets sent to one port.
constexpr int kPacketsNum = 1000000;

// Number of packets sent per second.
constexpr int kPacketsPerSecond = 16000;

// The maximum number of bytes that should be copied from a sampled packet to
// the sFlow datagram.
constexpr int kSampleHeaderSize = 512;

// Some fixed port numbers.
constexpr int kCpuPort = 0x3FFFFFFF;
constexpr int kDropPort = 256;

// The constants defined for SONIC
NosParameters nos_param_sonic = {
    "",                            // kRedisExecPrefix
    "docker exec sflow bash -c ",  // kSflowContainerExecPrefix
    "sudo ",                       // kSudoCmdPrefix
    "INBAND_PRIORITY_3",           // kCpuQueueName
    "/usr/bin/",                   // kRedisCliPath
    true                           // kIsSonicDebianLinux
};

// Sflowtool binary name in the collector.
constexpr absl::string_view kSflowToolName = "sflowtool";

constexpr absl::string_view kSflowtoolLineFormatTemplate =
    "'$0 -l -p $1 & pid=$$!; sleep $2; kill -SIGTERM $$pid;'";

constexpr absl::string_view kSflowtoolLineFormatNonStopTemplate =
    "'$0 -l -p $1' || true";

constexpr absl::string_view kSflowtoolFullFormatTemplate =
    "'$0 -p $1 & pid=$$!; sleep $2; kill -SIGTERM $$pid;'";

constexpr absl::string_view kTcpdumpForTos =
    "tcpdump -c $0 -i lo -vv -eX udp and port $1";

constexpr absl::Duration kCommandTimeout = absl::Seconds(5);
constexpr absl::Duration kFreezeTimeout = absl::Seconds(30);
constexpr absl::Duration kDelayTimeForIxia = absl::Seconds(5);

constexpr char kFreeze[] =
    R"(/usr/tools/bin/redis-cli -n 1 "PUBLISH" "NSF_MANAGER_COMMON_NOTIFICATION_CHANNEL" "[\"freeze\",\"freeze\"]")";
constexpr char kUnfreeze[] =
    R"(/usr/tools/bin/redis-cli -n 1 "PUBLISH" "NSF_MANAGER_COMMON_NOTIFICATION_CHANNEL" "[\"unfreeze\",\"unfreeze\"]")";

constexpr int kNsfTrafficTestDurationSecs = 10;

// IpV4 address for filtering the sFlow packet.
constexpr auto kIpv4Src = netaddr::Ipv4Address(192, 168, 10, 1);
constexpr uint32_t kIpv4Dst = 0x01020304;  // 1.2.3.4
// Ixia flow details.
constexpr auto kDstMac =
    netaddr::MacAddress(0x00, 0x1a, 0x11, 0x17, 0x5f, 0x80);
constexpr auto kSourceMac = netaddr::MacAddress(00, 01, 02, 03, 04, 05);

constexpr int kSamplingRateInterval = 4000;

// Buffering and software bottlenecks can cause some amount of variance in rate
// measured end to end.
// Level of tolerance for packet rate verification.
// This could be parameterized in future if this is platform dependent.
constexpr double kTolerance = 0.20;

// Thredshold percentage of packets punted to CPU to be considered passing
constexpr int kPassingPercentageCpuPunted = 75;
// Thredshold percentage of packets received out of total packets sent
constexpr int kPassingPercentagePktRecv = 98;
// Thredshold percentage of packets punted out of total packets sent
constexpr int kPassingPercentagePktPunt = 98;

// Vrf prefix used in the test.
constexpr absl::string_view kVrfIdPrefix = "vrf-";

// Used for sFLow collector.
constexpr char kLocalLoopbackIpv6[] = "::1";

// sFlow needs 800 samples/sec for 3 secs to trigger this back off. Use 1000
// samples/sec and 10 secs to make sure backoff could be triggered.
constexpr int kBackOffThresholdSamples = 1000;
constexpr int kBackoffTrafficDurationSecs = 10;

constexpr int kSflowOutPacketsTos = 0x80;
constexpr absl::string_view kEtherTypeIpv4 = "0x0800";
constexpr absl::string_view kEtherTypeIpv6 = "0x86dd";

std::string SflowContainerExecCmdStr(const NosParameters& nos_param,
                                     std::string cmd_name) {
  return nos_param.kSflowContainerExecPrefix + cmd_name;
}

std::string SflowContainerExecCmdStr(const NosParameters& nos_param,
                                     absl::string_view cmd_name) {
  return SflowContainerExecCmdStr(nos_param, std::string(cmd_name));
}

absl::StatusOr<std::string> GetSflowQueueName(
    gnmi::gNMI::StubInterface* gnmi_stub, const std::string& cpu_queue_name) {
  ASSIGN_OR_RETURN(auto cpu_queues,
                   pins_test::GetQueuesByEgressPort("CPU", *gnmi_stub));
  for (const auto& queue_name : cpu_queues) {
    if (queue_name == cpu_queue_name) {
      return cpu_queue_name;
    }
  }
  return "BE1";
}

absl::StatusOr<std::string>
GetP4rtQueueName(gnmi::gNMI::StubInterface *gnmi_stub) {
  ASSIGN_OR_RETURN(auto cpu_queues,
                   pins_test::GetQueuesByEgressPort("CPU", *gnmi_stub));
  for (const auto &queue_name : cpu_queues) {
    if (queue_name == "INBAND_PRIORITY_8") {
      return "INBAND_PRIORITY_8";
    }
  }
  return "NC1";
}

// Returns IP address in dot-decimal notation, e.g. "192.168.2.1".
std::string GetDstIpv4AddrByPortId(const int port_id) {
  return netaddr::Ipv4Address(std::bitset<32>(kIpv4Dst + port_id)).ToString();
}

// Sets ACL punt rule according to `port_id`.
absl::Status SetUpAclPunt(pdpi::P4RuntimeSession& p4_session,
                          const pdpi::IrP4Info& ir_p4info, int port_id) {
  ASSIGN_OR_RETURN(
      p4::v1::TableEntry pi_entry,
      pdpi::PartialPdTableEntryToPiTableEntry(
          ir_p4info,
          gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
              R"pb(
                acl_ingress_table_entry {
                  match {
                    dst_mac { value: "$0" mask: "ff:ff:ff:ff:ff:ff" }
                    is_ipv4 { value: "0x1" }
                    dst_ip { value: "$1" mask: "255.255.255.255" }
                  }
                  action { acl_trap { qos_queue: "0x7" } }
                  priority: 1
                }
              )pb",
              kDstMac.ToString(), GetDstIpv4AddrByPortId(port_id)))));
  return pdpi::InstallPiTableEntry(&p4_session, pi_entry);
}

// Sets ACL drop rule according to `port_id`.
absl::Status SetUpAclDrop(pdpi::P4RuntimeSession& p4_session,
                          const pdpi::IrP4Info& ir_p4info, int port_id) {
  ASSIGN_OR_RETURN(
      p4::v1::TableEntry pi_entry,
      pdpi::PartialPdTableEntryToPiTableEntry(
          ir_p4info,
          gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
              R"pb(
                acl_ingress_table_entry {
                  match {
                    dst_mac { value: "$0" mask: "ff:ff:ff:ff:ff:ff" }
                    is_ipv4 { value: "0x1" }
                    dst_ip { value: "$1" mask: "255.255.255.255" }
                  }
                  action { acl_drop {} }
                  priority: 1
                }
              )pb",
              kDstMac.ToString(), GetDstIpv4AddrByPortId(port_id)))));
  return pdpi::InstallPiTableEntry(&p4_session, pi_entry);
}

// Sets VRF according to port number. The pattern would be vrf-x (x=port id).
absl::Status SetSutVrf(pdpi::P4RuntimeSession& p4_session,
                       const p4::config::v1::P4Info& p4info,
                       const pdpi::IrP4Info& ir_p4info,
                       absl::Span<const int> port_ids) {
  for (int i = 0; i < port_ids.size(); ++i) {
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
                           absl::StrCat(kVrfIdPrefix, port_ids[i])))));
    RETURN_IF_ERROR(pdpi::InstallPiTableEntry(&p4_session, pi_entry));

    ASSIGN_OR_RETURN(
        pi_entry,
        pdpi::PartialPdTableEntryToPiTableEntry(
            ir_p4info,
            gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
                R"pb(
                  acl_pre_ingress_table_entry {
                    match { in_port { value: "$0" } }  # Match in port
                    action { set_vrf { vrf_id: "$1" } }
                    priority: 1
                  })pb",
                port_ids[i], absl::StrCat(kVrfIdPrefix, port_ids[i])))));
    RETURN_IF_ERROR(pdpi::InstallPiTableEntry(&p4_session, pi_entry));
  }

  return absl::OkStatus();
}

// Creates members by filling in the controller port ids.
absl::StatusOr<std::vector<GroupMember>> CreateGroupMembers(
    int group_size, absl::Span<const int> controller_port_ids) {
  if (group_size > controller_port_ids.size()) {
    return absl::InvalidArgumentError(
        absl::StrCat("Not enough members: ", controller_port_ids.size(),
                     " to create the group with size: ", group_size));
  }
  std::vector<GroupMember> members(group_size);
  for (int i = 0; i < group_size; i++) {
    // Skip weight since we don't need it in this test.
    members[i] = pins::GroupMember{.port = controller_port_ids[i]};
    LOG(INFO) << "member-" << i << " port: " << members[i].port;
  }
  return members;
}

// Program route entries using vrf_id.
absl::Status ProgramRoutes(pdpi::P4RuntimeSession& p4_session,
                           const pdpi::IrP4Info& ir_p4info, const int port_id,
                           absl::string_view next_hop_id) {
  const std::string vrf_id = absl::StrCat(kVrfIdPrefix, port_id);
  // Add set of flows to allow forwarding.
  auto ipv4_entry = gutil::ParseProtoOrDie<sai::Update>(absl::Substitute(
      R"pb(
        type: INSERT
        table_entry {
          ipv4_table_entry {
            match { vrf_id: "$0" }
            action { set_nexthop_id { nexthop_id: "$1" } }
          }
        })pb",
      vrf_id, next_hop_id));
  p4::v1::WriteRequest write_request;
  ASSIGN_OR_RETURN(
      p4::v1::Update pi_entry, pdpi::PdUpdateToPi(ir_p4info, ipv4_entry),
      _.SetPrepend() << "Failed in PD table conversion to PI, entry: "
                     << ipv4_entry.DebugString() << " error: ");
  *write_request.add_updates() = pi_entry;
  return pdpi::SetMetadataAndSendPiWriteRequest(&p4_session, write_request);
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

// These are the counters we track in these tests.
struct Counters {
  uint64_t in_pkts;
  uint64_t out_pkts;
  uint64_t in_octets;
  uint64_t out_octets;
  uint64_t in_discards;
  uint64_t out_discards;
};

absl::StatusOr<uint64_t> GetGnmiStat(std::string stat_name,
                                     absl::string_view iface,
                                     gnmi::gNMI::StubInterface* gnmi_stub) {
  std::string ops_state_path;
  std::string ops_parse_str;

  if (absl::StartsWith(stat_name, "ipv4-")) {
    std::string name = stat_name.substr(5);
    ops_state_path = absl::StrCat(
        "interfaces/interface[name=", iface,
        "]subinterfaces/subinterface[index=0]/ipv4/state/counters/", name);
    ops_parse_str = "openconfig-if-ip:" + name;
  } else if (absl::StartsWith(stat_name, "ipv6-")) {
    std::string name = stat_name.substr(5);
    ops_state_path = absl::StrCat(
        "interfaces/interface[name=", iface,
        "]subinterfaces/subinterface[index=0]/ipv6/state/counters/", name);
    ops_parse_str = "openconfig-if-ip:" + name;
  } else {
    ops_state_path = absl::StrCat("interfaces/interface[name=", iface,
                                  "]/state/counters/", stat_name);
    ops_parse_str = "openconfig-interfaces:" + stat_name;
  }

  ASSIGN_OR_RETURN(std::string ops_response,
                   pins_test::GetGnmiStatePathInfo(gnmi_stub, ops_state_path,
                                                   ops_parse_str));

  uint64_t stat;
  // skip over the initial quote '"'
  (void)absl::SimpleAtoi(ops_response.substr(1), &stat);
  return stat;
}

void ShowCounters(const Counters& cnt) {
  LOG(INFO) << "in-pkts " << cnt.in_pkts;
  LOG(INFO) << "out-pkts " << cnt.out_pkts;
  LOG(INFO) << "in-octets " << cnt.in_octets;
  LOG(INFO) << "out-octets " << cnt.out_octets;
  LOG(INFO) << "in-discards " << cnt.in_discards;
  LOG(INFO) << "out_discards " << cnt.out_discards;
}

// DeltaCounters - computer delta as change from initial to final counters
Counters DeltaCounters(const Counters& initial, const Counters& final) {
  Counters delta = {};

  delta.in_pkts = final.in_pkts - initial.in_pkts;
  delta.out_pkts = final.out_pkts - initial.out_pkts;
  delta.in_octets = final.in_octets - initial.in_octets;
  delta.out_octets = final.out_octets - initial.out_octets;
  delta.in_discards = final.in_discards - initial.in_discards;
  delta.out_discards = final.out_discards - initial.out_discards;
  return delta;
}

absl::StatusOr<Counters> ReadCounters(std::string iface,
                                      gnmi::gNMI::StubInterface* gnmi_stub) {
  Counters cnt = {};

  ASSIGN_OR_RETURN(cnt.in_pkts, GetGnmiStat("in-pkts", iface, gnmi_stub));
  ASSIGN_OR_RETURN(cnt.out_pkts, GetGnmiStat("out-pkts", iface, gnmi_stub));
  ASSIGN_OR_RETURN(cnt.in_octets, GetGnmiStat("in-octets", iface, gnmi_stub));
  ASSIGN_OR_RETURN(cnt.out_octets, GetGnmiStat("out-octets", iface, gnmi_stub));
  ASSIGN_OR_RETURN(cnt.in_discards,
                   GetGnmiStat("in-discards", iface, gnmi_stub));
  ASSIGN_OR_RETURN(cnt.out_discards,
                   GetGnmiStat("out-discards", iface, gnmi_stub));
  return cnt;
}

struct IxiaTrafficSettings {
  Openapi::StubInterface& traffic_client;
  int64_t traffic_rate;
  int sampling_rate;
};

// The packets are all same for one port. Use port_id as the index for
// generating packets.
absl::Status SendNPacketsToSut(Openapi::StubInterface& traffic_client,
                               absl::Duration runtime) {
  // Send Ixia traffic.
  RETURN_IF_ERROR(SetTrafficTransmissionState(
      traffic_client, StateTrafficFlowTransmit::State::start));

  // Wait for Traffic to be sent. Add a little extra time kDelayTimeForIxia (5
  // sec)
  absl::SleepFor(runtime + kDelayTimeForIxia);

  // Stop Ixia traffic.
  return SetTrafficTransmissionState(traffic_client,
                                     StateTrafficFlowTransmit::State::stop);
}

// Set up Ixia traffic with given parameters and return the traffic_client.
absl::StatusOr<Openapi::StubInterface*> SetUpIxiaTraffic(
    absl::Span<const IxiaLink> ixia_links, thinkit::GenericTestbed& testbed,
    const int64_t pkt_count, const int64_t pkt_rate,
    gnmi::gNMI::StubInterface& gnmi_stub, const int frame_size = 1000) {
  const IxiaLink& tx_link = ixia_links[0];
  const IxiaLink& rx_link = ixia_links[1];

  // Create config.
  SetConfigRequest set_config_request;
  otg::Config* config = set_config_request.mutable_config();

  AddPorts(*config, tx_link.ixia_interface, rx_link.ixia_interface,
           tx_link.ixia_location, rx_link.ixia_location);

  otg::Flow& flow = CreateFlow(*config, tx_link.ixia_interface,
                               rx_link.ixia_interface, "sflow");
  SetFlowSize(flow, frame_size);
  SetFlowDuration(flow, pkt_count);
  SetFlowRatePps(flow, pkt_rate);

  AddEthernetHeader(flow, kSourceMac.ToString(), kDstMac.ToString());
  AddIPv4Header(flow, kIpv4Src.ToString(),
                GetDstIpv4AddrByPortId(tx_link.port_id));

  // Set the config.
  SetConfigResponse set_config_response;
  ClientContext set_config_context;
  ASSIGN_OR_RETURN(Openapi::StubInterface * traffic_client,
                   testbed.GetTrafficClient());
  LOG(INFO) << "Set Config Request: " << set_config_request;
  RETURN_IF_ERROR(gutil::GrpcStatusToAbslStatus(traffic_client->SetConfig(
      &set_config_context, set_config_request, &set_config_response)));
  LOG(INFO) << "Set Config Response: " << absl::StrCat(set_config_response);

  return traffic_client;
}

// Get the packet counters on SUT interface connected to Ixia.
absl::StatusOr<std::vector<Counters>> GetIxiaInterfaceCounters(
    absl::Span<const IxiaLink> ixia_links,
    gnmi::gNMI::StubInterface* gnmi_stub) {
  std::vector<Counters> counters;
  for (const IxiaLink& ixia_link : ixia_links) {
    ASSIGN_OR_RETURN(auto initial_in_counter,
                     ReadCounters(ixia_link.sut_interface, gnmi_stub));
    LOG(INFO) << "Ingress Counters (" << ixia_link.sut_interface << "):\n";
    ShowCounters(initial_in_counter);
    LOG(INFO) << "\n";
    counters.push_back(initial_in_counter);
  }
  // Reads CPU counter.
  ASSIGN_OR_RETURN(auto initial_in_counter, ReadCounters("CPU", gnmi_stub));
  LOG(INFO) << "Ingress Counters (\"CPU\"):\n";
  ShowCounters(initial_in_counter);
  LOG(INFO) << "\n";
  counters.push_back(initial_in_counter);
  return counters;
}

void SetIxiaTrafficParams(otg::Flow& flow, int64_t pkts_num,
                          int64_t traffic_rate) {
  SetFlowDuration(flow, pkts_num);
  SetFlowRatePps(flow, traffic_rate);
}

// Run sflowtool on SUT in a new thread. Returns the thread to let caller to
// wait for the finish.
absl::StatusOr<std::thread> RunSflowCollectorForNSecs(
    thinkit::SSHClient& ssh_client, absl::string_view device_name,
    absl::string_view sflow_template, int collector_port,
    const int sflowtool_runtime, std::string& sflow_tool_result) {
  std::thread sflow_tool_thread =
      std::thread([&sflow_tool_result, &ssh_client, device_name, sflow_template,
                   collector_port, sflowtool_runtime]() {
        const std::string ssh_command = absl::Substitute(
            sflow_template, kSflowToolName, collector_port, sflowtool_runtime);
        LOG(INFO) << "ssh command:" << ssh_command;
        ASSERT_OK_AND_ASSIGN(
            sflow_tool_result,
            ssh_client.RunCommand(
                device_name, ssh_command,
                /*timeout=*/absl::Seconds(sflowtool_runtime + 20)));
      });
  // Sleep to wait sflowtool to start.
  absl::SleepFor(absl::Seconds(5));
  return sflow_tool_thread;
}

// Run sflowtool on SUT in a new thread. Returns the thread to let caller to
// wait for the finish.
absl::StatusOr<std::thread> RunSflowCollectorNonStop(
    thinkit::SSHClient& ssh_client, absl::string_view device_name,
    absl::string_view sflow_template, int collector_port,
    std::string& sflow_tool_result) {
  std::thread sflow_tool_thread = std::thread([&sflow_tool_result, &ssh_client,
                                               device_name, sflow_template,
                                               collector_port]() {
    const std::string ssh_command =
        absl::Substitute(sflow_template, kSflowToolName, collector_port);
    LOG(INFO) << "ssh command:" << ssh_command;
    ASSERT_OK_AND_ASSIGN(sflow_tool_result,
                         ssh_client.RunCommand(device_name, ssh_command,
                                               /*timeout=*/absl::Minutes(60)));
  });
  // Sleep to wait sflowtool to start.
  absl::SleepFor(absl::Seconds(5));
  return sflow_tool_thread;
}

void StopSflowtool(thinkit::SSHClient &ssh_client,
                   absl::string_view device_name,
                   absl::string_view sflowtool_name) {
  const std::string ssh_command =
      absl::Substitute("kill -SIGTERM $$(pidof $0)", sflowtool_name);
  LOG(INFO) << "ssh command:" << ssh_command;
  ASSERT_OK_AND_ASSIGN(std::string kill_result,
                       ssh_client.RunCommand(device_name, ssh_command,
                                             /*timeout=*/absl::Seconds(5)));
}

// Needs to find out the pid of sFlow on switch manually.
absl::StatusOr<std::thread> RunTopCommandForSflow(
    thinkit::SSHClient& ssh_client, absl::string_view device_name, int run_time,
    std::string& result) {
  std::thread thread = std::thread([&result, &ssh_client, run_time,
                                    device_name]() {
    const int interval = 30;
    int times = run_time / interval;
    LOG(INFO) << "RunTopCommandForSflow run_time: " << run_time
              << " times: " << times;
    // Run top command every interval. Whole times = run_time/interval.
    const std::string ssh_command =
        absl::StrCat("top -b -d ", interval, " -p $(pidof hsflowd) -n ", times);
    LOG(INFO) << "RunTopCommandForSflow ssh command: " << ssh_command;
    ASSERT_OK_AND_ASSIGN(result, ssh_client.RunCommand(
                                     device_name, ssh_command,
                                     /*timeout=*/absl::Seconds(run_time + 20)));
  });
  return thread;
}

// start_time=$(date +%s)

// while [ $(date +%s) -lt $(($start_time + 36000)) ]; do
//   mpstat
//   sleep 130
// done
absl::StatusOr<std::thread> ShowCpuIdle(thinkit::SSHClient& ssh_client,
                                        absl::string_view device_name,
                                        const int run_time,
                                        std::string& result) {
  std::thread thread =
      std::thread([&result, &ssh_client, run_time, device_name]() {
        absl::Time cur_time = absl::Now();
        while (absl::Now() <= cur_time + absl::Seconds(run_time)) {
          const std::string ssh_command = "mpstat";
          // LOG(INFO) << "ShowCpuIdle ssh command:" << ssh_command;
          ASSERT_OK_AND_ASSIGN(
              std::string cur_result,
              ssh_client.RunCommand(device_name, ssh_command,
                                    /*timeout=*/absl::Seconds(10)));
          LOG(INFO) << "ShowCpuIdle result:" << cur_result;
          result += cur_result;
          absl::SleepFor(absl::Seconds(100));
        }
      });
  return thread;
}

// #!/bin/bash

// start_time=$(date +%s)

// while [ $(date +%s) -lt $(($start_time + 36000)) ]; do
//   pmap $(pidof hsflowd) | tail -n 1 | awk '/[0-9]K/{print $2}'
//   sleep 60
// done
absl::StatusOr<std::thread> ShowMemory(thinkit::SSHClient& ssh_client,
                                       absl::string_view device_name,
                                       const int run_time,
                                       std::string& result) {
  std::thread thread =
      std::thread([&result, &ssh_client, run_time, device_name]() {
        absl::Time cur_time = absl::Now();
        while (absl::Now() <= cur_time + absl::Seconds(run_time)) {
          const std::string ssh_command =
              "pmap $(pidof hsflowd) | tail -n 1 | awk '/[0-9]K/{print $2}'";
          // LOG(INFO) << "ShowMemory ssh command:" << ssh_command;
          ASSERT_OK_AND_ASSIGN(
              std::string cur_result,
              ssh_client.RunCommand(device_name, ssh_command,
                                    /*timeout=*/absl::Seconds(10)));
          LOG(INFO) << "ShowMemory result:" << cur_result;
          result += cur_result;
          absl::SleepFor(absl::Seconds(100));
        }
      });
  return thread;
}

// Run tcpdump on SUT in a new thread. Returns the thread to let caller to
// wait for the finish.
absl::StatusOr<std::thread> CaptureTcpdumpForNPackets(
    thinkit::SSHClient& ssh_client, absl::string_view device_name,
    int packets_count, int port, const int runtime,
    const NosParameters& nos_param, std::string& result) {
  std::string ssh_command =
      absl::Substitute(nos_param.kSudoCmdPrefix + std::string(kTcpdumpForTos),
                       packets_count, port);
  LOG(INFO) << "ssh command:" << ssh_command;
  std::thread thread = std::thread([device_name, runtime, &ssh_client,
                                    ssh_command, &result]() {
    LOG(INFO) << "ssh command:" << ssh_command;
    ASSERT_OK_AND_ASSIGN(
        result, ssh_client.RunCommand(device_name, ssh_command,
                                      /*timeout=*/absl::Seconds(runtime + 10)));
  });
  return thread;
}

// Get pid of hsflowd on `device_name`.
absl::StatusOr<std::string> GetHsflowdPid(thinkit::SSHClient& ssh_client,
                                          absl::string_view device_name) {
  std::string ssh_command = "echo $(pidof hsflowd)";
  LOG(INFO) << "ssh command:" << ssh_command;
  ASSIGN_OR_RETURN(std::string result,
                   ssh_client.RunCommand(device_name, ssh_command,
                                         /*timeout=*/absl::Seconds(5)));
  result = absl::StripAsciiWhitespace(result);
  return result;
}

// Send packets to SUT and validate packet counters via gNMI. This function
// expects no drops on CPU queue.
absl::Status SendSflowTraffic(Openapi::StubInterface& traffic_client,
                              absl::Span<const IxiaLink> ixia_links,
                              thinkit::GenericTestbed& testbed,
                              gnmi::gNMI::StubInterface* gnmi_stub,
                              const int64_t pkt_count, const int64_t pkt_rate,
                              const std::string& cpu_queue_name) {
  // Read initial counters via GNMI from the SUT
  LOG(INFO) << "Read initial packet counters.";
  ASSIGN_OR_RETURN(std::vector<Counters> initial_in_counters,
                   GetIxiaInterfaceCounters(ixia_links, gnmi_stub));
  ASSIGN_OR_RETURN(std::string sflow_queue_name,
                   GetSflowQueueName(gnmi_stub, cpu_queue_name));
  ASSIGN_OR_RETURN(
      auto initial_queue_counter,
      pins_test::GetGnmiQueueCounters("CPU", sflow_queue_name, *gnmi_stub));
  absl::Time start_time = absl::Now();

  RETURN_IF_ERROR(SendNPacketsToSut(
      traffic_client,
      /*runtime=*/absl::Seconds(std::ceil(1.0f * pkt_count / pkt_rate))));

  // Sleep to wait for the counters to be reflected.
  absl::SleepFor(absl::Seconds(10));

  LOG(INFO) << "Read final packet counters.";
  // Read final counters via GNMI from the SUT
  ASSIGN_OR_RETURN(std::vector<Counters> final_in_counters,
                   GetIxiaInterfaceCounters(ixia_links, gnmi_stub));
  for (size_t i = 0; i < ixia_links.size(); ++i) {
    auto delta = DeltaCounters(initial_in_counters[i], final_in_counters[i]);
    // Display the difference in the counters for now (during test dev)
    LOG(INFO) << "\nIngress Deltas (" << ixia_links[i].sut_interface << "):\n";
    ShowCounters(delta);
    EXPECT_GE(delta.in_pkts, pkt_count / 100 * kPassingPercentagePktRecv)
        << "Received packets count is fewer than " << kPassingPercentagePktRecv
        << "% of sent packets count: "
        << ". Interface: " << ixia_links[i].sut_interface << ". Sent "
        << pkt_count << ". Received " << delta.in_pkts << ".";
  }
  ASSIGN_OR_RETURN(
      auto final_queue_counter,
      pins_test::GetGnmiQueueCounters("CPU", sflow_queue_name, *gnmi_stub));

  // Show CPU counter data.
  auto delta =
      DeltaCounters(initial_in_counters.back(), final_in_counters.back());
  LOG(INFO) << "\nIngress Deltas (\"CPU\"):\n";
  ShowCounters(delta);
  auto queue_delta = final_queue_counter - initial_queue_counter;
  LOG(INFO) << "CPU " << sflow_queue_name << " queue counter delta:\n"
            << queue_delta << " \n total time: " << (absl::Now() - start_time);
  EXPECT_EQ(queue_delta.num_packets_dropped, 0)
      << sflow_queue_name
      << " queue dropped packets: " << queue_delta.num_packets_dropped << ". "
      << sflow_queue_name
      << " queue transimitted pkts: " << queue_delta.num_packets_transmitted
      << ". Expected 0 drops for " << sflow_queue_name << " queue.";
  return absl::OkStatus();
}

// Track statistics for Ixia traffic.
struct IxiaCounterStats {
  std::vector<Counters> initial_in_counters;
  std::string sflow_queue_name;
  pins_test::QueueCounters initial_queue_counter;
  const int64_t pkt_count;
  absl::Time start_time;
};

absl::StatusOr<IxiaCounterStats> GetIxiaCounterStats(
    absl::Span<const IxiaLink> ixia_links, gnmi::gNMI::StubInterface* gnmi_stub,
    const int64_t pkt_count, const std::string& cpu_queue_name) {
  // Read initial counters via GNMI from the SUT
  LOG(INFO) << "Read initial packet counters.";
  ASSIGN_OR_RETURN(std::vector<Counters> initial_in_counters,
                   GetIxiaInterfaceCounters(ixia_links, gnmi_stub));
  ASSIGN_OR_RETURN(std::string sflow_queue_name,
                   GetSflowQueueName(gnmi_stub, cpu_queue_name));
  ASSIGN_OR_RETURN(
      auto initial_queue_counter,
      pins_test::GetGnmiQueueCounters("CPU", sflow_queue_name, *gnmi_stub));
  absl::Time start_time = absl::Now();
  return IxiaCounterStats{
      .initial_in_counters = initial_in_counters,
      .sflow_queue_name = sflow_queue_name,
      .initial_queue_counter = initial_queue_counter,
      .pkt_count = pkt_count,
      .start_time = start_time,
  };
}

absl::Status ValidateIxiaInterfaceCounters(
    absl::Span<const IxiaLink> ixia_links, gnmi::gNMI::StubInterface* gnmi_stub,
    const IxiaCounterStats& sflow_ixia_counter_data) {
  const IxiaLink& ingress_link = ixia_links[0];

  LOG(INFO) << "Read final packet counters.";
  // Read final counters via GNMI from the SUT
  ASSIGN_OR_RETURN(std::vector<Counters> final_in_counters,
                   GetIxiaInterfaceCounters(ixia_links, gnmi_stub));
  for (size_t i = 0; i < ixia_links.size(); ++i) {
    Counters delta = DeltaCounters(
        sflow_ixia_counter_data.initial_in_counters[i], final_in_counters[i]);
    LOG(INFO) << "\nIngress Deltas (" << ixia_links[i].sut_interface << "):\n";
    ShowCounters(delta);

    // If the interface is the ingress link, the expected packet count is the
    // same as the sent packet count. Otherwise, the expected packet count is 0.
    uint64_t expected_pkt_count = 0;
    if (ixia_links[i].sut_interface == ingress_link.sut_interface) {
      expected_pkt_count = sflow_ixia_counter_data.pkt_count;
    }

    EXPECT_EQ(delta.in_pkts, expected_pkt_count)
        << "Received packets count is not equal to sent packets count: "
        << ". Interface: " << ixia_links[i].sut_interface << ". Sent "
        << expected_pkt_count << ". Received " << delta.in_pkts << ".";
  }

  ASSIGN_OR_RETURN(
      pins_test::QueueCounters final_queue_counter,
      pins_test::GetGnmiQueueCounters(
          "CPU", sflow_ixia_counter_data.sflow_queue_name, *gnmi_stub));

  // Show CPU counter data.
  Counters delta =
      DeltaCounters(sflow_ixia_counter_data.initial_in_counters.back(),
                    final_in_counters.back());
  LOG(INFO) << "\nIngress Deltas (\"CPU\"):\n";
ShowCounters(delta);
  pins_test::QueueCounters queue_delta =
      final_queue_counter - sflow_ixia_counter_data.initial_queue_counter;
  LOG(INFO) << "CPU " << sflow_ixia_counter_data.sflow_queue_name
            << " queue counter delta:\n"
            << queue_delta << " \n total time: "
            << (absl::Now() - sflow_ixia_counter_data.start_time);
  EXPECT_EQ(queue_delta.num_packets_dropped, 0)
      << sflow_ixia_counter_data.sflow_queue_name
      << " queue dropped packets: " << queue_delta.num_packets_dropped << ". "
      << sflow_ixia_counter_data.sflow_queue_name
      << " queue transimitted pkts: " << queue_delta.num_packets_transmitted
      << ". Expected 0 drops for " << sflow_ixia_counter_data.sflow_queue_name
      << " queue.";
  return absl::OkStatus();
}

int GetSflowSamplesOnSut(const std::string& sflowtool_output,
                         const int port_id) {
  constexpr int kFieldSize = 20, kDstIpIdx = 10;
  int count = 0;
  // Each line indicates one sFlow sample.
  for (absl::string_view sflow : absl::StrSplit(sflowtool_output, '\n')) {
    // Split by column.
    std::vector<absl::string_view> fields = absl::StrSplit(sflow, ',');
    if (fields.size() < kFieldSize) {
      continue;
    }
    // Filter dst ip.
    if (fields[kDstIpIdx] == GetDstIpv4AddrByPortId(port_id)) {
      count++;
    }
  }
  return count;
}

// Check interface/state/oper-status value to validate if link is up.
absl::StatusOr<bool> CheckLinkUp(absl::string_view interface,
                                 gnmi::gNMI::StubInterface& gnmi_stub) {
  std::string oper_status_state_path = absl::StrCat(
      "interfaces/interface[name=", interface, "]/state/oper-status");

  std::string parse_str = "openconfig-interfaces:oper-status";
  ASSIGN_OR_RETURN(std::string ops_response,
                   pins_test::GetGnmiStatePathInfo(
                       &gnmi_stub, oper_status_state_path, parse_str));

  return ops_response == "\"UP\"";
}

// Returns an available port which is UP and different from `used_port`.
// Returns an error if failed.
absl::StatusOr<Port> GetUnusedUpPort(gnmi::gNMI::StubInterface& gnmi_stub,
                                     absl::string_view used_port) {
  absl::flat_hash_map<std::string, std::string> port_id_per_port_name;
  ASSIGN_OR_RETURN(port_id_per_port_name,
                   pins_test::GetAllUpInterfacePortIdsByName(gnmi_stub));
  for (const auto& [interface, port_id_str] : port_id_per_port_name) {
    int port_id;
    if (interface != used_port && absl::SimpleAtoi(port_id_str, &port_id)) {
      LOG(INFO) << "Picked port " << port_id << " interface: " << interface;
      return Port{
          .interface_name = interface,
          .port_id = port_id,
      };
    }
  }
  return absl::FailedPreconditionError("No more usable port ids.");
}

// Returns a vector of SUT interfaces that are connected to Ixia and up.
absl::StatusOr<std::vector<IxiaLink>> GetIxiaConnectedUpLinks(
    thinkit::GenericTestbed& generic_testbed,
    gnmi::gNMI::StubInterface& gnmi_stub) {
  std::vector<IxiaLink> ixia_links;

  absl::flat_hash_map<std::string, thinkit::InterfaceInfo> interface_info =
      generic_testbed.GetSutInterfaceInfo();
  absl::flat_hash_map<std::string, std::string> port_id_per_port_name;
  ASSIGN_OR_RETURN(port_id_per_port_name,
                   pins_test::GetAllInterfaceNameToPortId(gnmi_stub));
  // Loop through the interface_info looking for Ixia/SUT interface pairs,
  // checking if the link is up.  Add the pair to connections.
  for (const auto& [interface, info] : interface_info) {
    if (info.interface_modes.contains(thinkit::TRAFFIC_GENERATOR)) {
      ASSIGN_OR_RETURN(bool sut_link_up, CheckLinkUp(interface, gnmi_stub));
      auto port_id = gutil::FindOrNull(port_id_per_port_name, interface);
      EXPECT_NE(port_id, nullptr) << absl::Substitute(
          "No corresponding p4rt id for interface $0", interface);
      if (sut_link_up) {
        LOG(INFO) << "Ixia interface:" << info.peer_interface_name
                  << ". Sut interface:" << interface << ". Port id:"
                  << *port_id;
        ixia_links.push_back(IxiaLink{
            .ixia_interface = info.peer_interface_name,
            .ixia_location = info.peer_traffic_location,
            .sut_interface = interface,
            .port_id = std::stoi(*port_id),
        });
      }
    }
  }

  return ixia_links;
}

// Used for printing result.
struct SflowResult {
  std::string rule;
  std::string sut_interface;
  int64_t packets;
  int sampling_rate;
  int expected_samples;
  int actual_samples;

  std::string DebugString() {
    return absl::Substitute(
        "Rule: $0\n"
        "Ingress interface: $1\n"
        "Total packets input: $2\n"
        "Sampling rate: 1 in $3\n"
        "Expected samples: $4\n"
        "Actual samples: $5",
        rule, sut_interface, packets, sampling_rate, expected_samples,
        actual_samples);
  }
};

// Extracts loopback ipv6 addr from gNMI config. Returns a
// FailedPreconditionError if `gnmi_config` does not have a loopback ip.
absl::StatusOr<std::string> GetLoopbackAddrIpv6FromConfig(
    const std::string& gnmi_config) {
  ASSIGN_OR_RETURN(auto loopback_ipv6,
                   pins_test::ParseLoopbackIpv6s(gnmi_config));

  if (loopback_ipv6.empty()) {
    return absl::FailedPreconditionError(
        absl::Substitute("No loopback IP found from gNMI config."));
  }
  return loopback_ipv6[0].ToString();
}

// Returns a set of interface names which should enable sFlow from testbed info.
// By default this would enable all interface.
absl::StatusOr<absl::flat_hash_map<std::string, bool>>
GetSflowInterfacesFromSut(thinkit::GenericTestbed& testbed) {
  absl::flat_hash_map<std::string, thinkit::InterfaceInfo> interface_info =
      testbed.GetSutInterfaceInfo();
  absl::flat_hash_map<std::string, bool> sflow_interfaces;
  for (const auto& [interface, info] : interface_info) {
    if (info.interface_modes.contains(thinkit::CONTROL_INTERFACE) ||
        info.interface_modes.contains(thinkit::TRAFFIC_GENERATOR)) {
      sflow_interfaces[interface] = true;
    }
  }
  return sflow_interfaces;
}

absl::StatusOr<std::string> FetchPlatformJsonContents(
    thinkit::SSHClient& ssh_client, thinkit::Switch& sut,
    const std::string& platform_json_path) {
  const std::string ssh_command = absl::StrCat("cat ", platform_json_path);
  LOG(INFO) << "Fetching contents from switch path: " << platform_json_path;
  ASSIGN_OR_RETURN(std::string platform_json_contents,
                   ssh_client.RunCommand(sut.ChassisName(), ssh_command,
                                         absl::ZeroDuration()));
  return platform_json_contents;
}

// Returns the value of `key` in `sflow_datagram`. Returns an error if not
// found.
absl::StatusOr<absl::string_view> ExtractValueByKey(
    absl::string_view sflow_datagram, absl::string_view key) {
  int idx = sflow_datagram.find(key);
  if (idx == std::string::npos) {
    return absl::NotFoundError(
        absl::Substitute("Cannot find $0 in $1", key, sflow_datagram));
  }
  return absl::StripAsciiWhitespace(sflow_datagram.substr(
      idx + key.size(), sflow_datagram.find('\n', idx) - idx - key.size()));
}

// Returns the headerLen from `sflowtool_output`. Also stores datagram into test
// artifact with `file_name`. Returns -1 if any error occurs.
absl::StatusOr<int> GetHeaderLenFromSflowOutput(
    absl::string_view sflowtool_output, int port_id,
    absl::string_view file_name, thinkit::TestEnvironment& test_environment) {
  // Every "startDatagram" indicates an sFlow datagram.
  constexpr char kPattern[] = "startDatagram";
  size_t pos = sflowtool_output.rfind(kPattern);
  if (pos == std::string::npos) {
    return absl::NotFoundError(
        absl::Substitute("Cound not find $0 in sflowtool_output", kPattern));
  }
  absl::string_view sflow_datagram = sflowtool_output.substr(pos);
  LOG(INFO) << "sFlow datagram:\n" << sflow_datagram;

  // Example dump:
  // startDatagram =================================
  // ...
  // startSample ----------------------
  // ...
  // headerLen 128
  // ...
  // srcIP 192.168.10.1
  // dstIP 1.2.5.12
  // ...
  // endSample   ----------------------
  // endDatagram   =================================
  EXPECT_OK(test_environment.StoreTestArtifact(file_name, sflow_datagram));

  // Verifies this datagram is generated from specific traffic. We use dstIP
  // value for specific in port so we use it to validate as well.
  ASSIGN_OR_RETURN(absl::string_view dst_ip,
                   ExtractValueByKey(sflow_datagram, "dstIP"));
  if (dst_ip != GetDstIpv4AddrByPortId(port_id)) {
    return absl::FailedPreconditionError(
        absl::Substitute("dstIP field in sflow sample is not as expected: "
                         "expected: $0, actual: $1.",
                         GetDstIpv4AddrByPortId(port_id), dst_ip));
  }
  // Header length would be after `headerLen` field.
  ASSIGN_OR_RETURN(absl::string_view header_len_str,
                   ExtractValueByKey(sflow_datagram, "headerLen"));
  int header_len;
  (void)absl::SimpleAtoi(header_len_str, &header_len);

  // `decodedVLAN` field should not exist since vlan tag is stripped.
  EXPECT_THAT(ExtractValueByKey(sflow_datagram, "decodedVLAN"),
              gutil::StatusIs(absl::StatusCode::kNotFound,
                              HasSubstr("Cannot find decodedVLAN")));

  return header_len;
}

// Verifies sflow result format is as expected:
// sFlow sample dump:
// FLOW,2607:f001:0aa4:0000:0000:0000:0000:0000,15,0,000102030405,020202020203,0x0800,4095,0,1.2.3.6,192.168.10.1,61,0x00,64,0,0,0x00,500,478,1048576
// Samples are supposed to be in following format:
// "FLOW", agent address ,inputPort, outputPort ,src_MAC, dst_MAC,
// ethernet_type, in_vlan, out_vlan, src_IP, dst_IP, IP_protocol, ip_tos,
// ip_ttl, udp_src_port OR tcp_src_port OR icmp_type, udp_dst_port OR
// tcp_dst_port OR icmp_code, tcp_flags, packet_size, IP_size, sampling_rate
void VerifySflowResult(absl::string_view sflowtool_output,
                       std::optional<int> input_port,
                       std::optional<int> output_port,
                       absl::string_view src_mac, absl::string_view dst_mac,
                       absl::string_view ethernet_type,
                       absl::string_view src_ip, absl::string_view dst_ip,
                       std::optional<int> packet_size, int sampling_rate) {
  constexpr int kFieldSize = 20, kInputPortIdx = 2, kOutputPortIdx = 3,
                kSrcMacIdx = 4, kDstMacIdx = 5, kEthTypeIdx = 6, kSrcIpIdx = 9,
                kDstIpIdx = 10, kPktSizeIdx = 17, kSamplingRateIdx = 19;
  int interesting_samples = 0;
  // Each line indicates one sFlow sample.
  std::vector<std::string> sflow_samples =
      absl::StrSplit(sflowtool_output, '\n');
  for (const std::string& sflow_sample : sflow_samples) {
    // Split by column.
    std::vector<std::string> fields = absl::StrSplit(sflow_sample, ',');
    if (fields.size() < kFieldSize) {
      continue;
    }
    // Skip irrelevant samples.
    if (fields[kDstIpIdx] == "-") {
      continue;
    }
    // Filter dst ip.
    if (auto same_dst_ip =
            IsSameIpAddressStr(fields[kDstIpIdx], std::string(dst_ip));
        same_dst_ip.ok() && *same_dst_ip) {
      interesting_samples++;
      if (input_port.has_value()) {
        EXPECT_EQ(fields[kInputPortIdx], absl::StrCat(*input_port))
            << "Expected input port: " << absl::StrCat(*input_port)
            << ". Actual input port: " << fields[kInputPortIdx];
      }
      if (output_port.has_value()) {
        EXPECT_EQ(fields[kOutputPortIdx], absl::StrCat(*output_port))
            << "Expected output port: " << absl::StrCat(*output_port)
            << ". Actual output port: " << fields[kOutputPortIdx];
      }
      // The sample mac address does not have the "0x" prefix
      EXPECT_EQ(fields[kSrcMacIdx], src_mac.substr(2));
      EXPECT_EQ(fields[kDstMacIdx], dst_mac.substr(2));
      EXPECT_EQ(fields[kEthTypeIdx], ethernet_type);
      EXPECT_THAT(IsSameIpAddressStr(fields[kSrcIpIdx], std::string(src_ip)),
                  IsOkAndHolds(true))
          << "Expected src ip: " << src_ip
          << ". Actual src ip: " << fields[kSrcIpIdx];
      // TODO: check if maximum packet size is 1028. If so,
      // replace with absl::StrCat(std::min(*packet_size, 1028))
      if (packet_size.has_value()) {
        EXPECT_EQ(fields[kPktSizeIdx], absl::StrCat(*packet_size))
            << "Expected packet size: " << absl::StrCat(*packet_size)
            << ". Actual packet size: " << fields[kPktSizeIdx];
      }
      EXPECT_EQ(fields[kSamplingRateIdx], absl::StrCat(sampling_rate));
    }
  }
  EXPECT_GT(interesting_samples, 0) << "No samples for dst_ip: " << dst_ip;
}

void CollectDriverDebugs(thinkit::SSHClient* ssh_client,
                         absl::string_view device_name,
                         absl::string_view prefix,
                         thinkit::TestEnvironment& environment) {}

// Save output for:
// sflow container /etc/hsflowd.auto
// db contents
void CollectSflowDebugs(thinkit::SSHClient* ssh_client,
                        absl::string_view device_name, absl::string_view prefix,
                        thinkit::TestEnvironment& environment,
                        const NosParameters& nos_param) {
  // TODO: make this a param of instantiation
  if (!nos_param.kIsSonicDebianLinux) {
    CollectDriverDebugs(ssh_client, device_name, prefix, environment);
  }

  // /etc/hsflowd.auto might not exist on the switch if no collector config.
  auto result_or = ssh_client->RunCommand(
      device_name,
      /*command=*/
      SflowContainerExecCmdStr(nos_param,
                               std::string("'cat /etc/hsflowd.auto'")),
       absl::Seconds(20));
  if (result_or.ok()) {
    EXPECT_OK(environment.StoreTestArtifact(
        absl::StrCat(prefix, "sflow_container_hsflowd_auto.txt"), *result_or));
  }
  result_or = ssh_client->RunCommand(device_name,
                                     /*command=*/
                                     SflowContainerExecCmdStr(nos_param, std::string("'ps -ef'")),
                                     absl::Seconds(20));
  if (result_or.ok()) {
    EXPECT_OK(environment.StoreTestArtifact(
        absl::StrCat(prefix, "sflow_container_ps_ef.txt"), *result_or));
  }
  ASSERT_OK_AND_ASSIGN(auto result, ssh_client->RunCommand(device_name,
                                                           /*command=*/
                                                           "ip -6 route show",
                                                           absl::Seconds(20)));
  EXPECT_OK(environment.StoreTestArtifact(
      absl::StrCat(prefix, "ipv6_route_show.txt"), result));
  ASSERT_OK_AND_ASSIGN(
      result, ssh_client->RunCommand(device_name,
                                     /*command=*/
                                     "ip -6 neigh show", absl::Seconds(20)));
  EXPECT_OK(environment.StoreTestArtifact(
      absl::StrCat(prefix, "ipv6_neigh_show.txt"), result));

  // APPL_DB
  ASSERT_OK_AND_ASSIGN(
      result,
      ssh_client->RunCommand(device_name,
                             /*command=*/
                             nos_param.kRedisExecPrefix +
                                 "redis-dump -H 127.0.0.1 -p 6379 -d 0 -y",
                             absl::Seconds(20)));
  EXPECT_OK(environment.StoreTestArtifact(
      absl::StrCat(prefix, "sut_appl_db.txt"), result));

  // ASIC_DB
  ASSERT_OK_AND_ASSIGN(
      result,
      ssh_client->RunCommand(device_name,
                             /*command=*/
                             nos_param.kRedisExecPrefix +
                                 "redis-dump -H 127.0.0.1 -p 6379 -d 1 -y",
                             absl::Seconds(20)));
  EXPECT_OK(environment.StoreTestArtifact(
      absl::StrCat(prefix, "sut_asic_db.txt"), result));

  // CONFIG_DB
  ASSERT_OK_AND_ASSIGN(
      result,
      ssh_client->RunCommand(device_name,
                             /*command=*/
                             nos_param.kRedisExecPrefix +
                                 "redis-dump -H 127.0.0.1 -p 6379 -d 4 -y",
                             absl::Seconds(20)));
  EXPECT_OK(environment.StoreTestArtifact(
      absl::StrCat(prefix, "sut_config_db.txt"), result));

  // STATE_DB
  ASSERT_OK_AND_ASSIGN(
      result,
      ssh_client->RunCommand(device_name,
                             /*command=*/
                             nos_param.kRedisExecPrefix +
                                 "redis-dump -H 127.0.0.1 -p 6379 -d 6 -y",
                             absl::Seconds(20)));
  EXPECT_OK(environment.StoreTestArtifact(
      absl::StrCat(prefix, "sut_state_db.txt"), result));

  // APPL_STATE_DB
  ASSERT_OK_AND_ASSIGN(
      result,
      ssh_client->RunCommand(device_name,
                             /*command=*/
                             nos_param.kRedisExecPrefix +
                                 "redis-dump -H 127.0.0.1 -p 6379 -d 14 -y",
                             absl::Seconds(20)));
  EXPECT_OK(environment.StoreTestArtifact(
      absl::StrCat(prefix, "sut_appl_state_db.txt"), result));
}

// Returns OK if `sflowtool_output` has samples with `sample_rate`. Returns an
// InternalError if something goes wrong.
absl::Status IsExpectedSampleRateFromSamples(absl::string_view sflowtool_output,
                                             int sample_rate) {
  std::vector<std::string> sflow_samples =
      absl::StrSplit(sflowtool_output, '\n');
  if (sflow_samples.empty()) {
    return absl::InternalError(absl::Substitute(
        "No sflow samples found in sflowtool result. The result is: $0",
        sflowtool_output));
  }
  constexpr int kSamplingRateIdx = 19;
  std::string actual_sample_rate_str;

  // Check from latest to oldest sample.
  for (int i = sflow_samples.size() - 1; i >= 0; --i) {
    // Split by column.
    std::vector<absl::string_view> fields =
        absl::StrSplit(sflow_samples[i], ',');
    if (fields.size() <= kSamplingRateIdx) {
      continue;
    }
    LOG(INFO) << "Verifying sample flow: " << sflow_samples[i];
    actual_sample_rate_str = fields[kSamplingRateIdx];
    break;
  }
  int actual_sample_rate;
  if (!absl::SimpleAtoi(actual_sample_rate_str, &actual_sample_rate)) {
    return absl::InternalError(absl::Substitute(
        "$0 is not a valid sample rate.", actual_sample_rate_str));
  }
  if (actual_sample_rate != sample_rate) {
    return absl::InternalError(
        absl::Substitute("Expect sample rate : $0. Actual sample rate: $1.",
                         sample_rate, actual_sample_rate));
  }
  return absl::OkStatus();
}

// Verify that sample rate of interface in `sflow_enabled_interfaces` is equal
// to `multiple` * initial_interfaces_to_sample_rate[interface] .
absl::Status IsExpectedSamplingRateFromGnmi(
    gnmi::gNMI::StubInterface* gnmi_stub,
    const absl::flat_hash_set<std::string>& sflow_enabled_interfaces,
    const absl::flat_hash_map<std::string, int>&
        initial_interfaces_to_sample_rate,
    int multiple) {
  // Verify that sample rate on all interfaces is as expected.
  absl::flat_hash_map<std::string, int>
      current_interfaces_to_actual_sample_rate;
  ASSIGN_OR_RETURN(current_interfaces_to_actual_sample_rate,
                   GetSflowActualSamplingRateForInterfaces(
                       gnmi_stub, sflow_enabled_interfaces));
  for (const auto& [interface, sample_rate] :
       current_interfaces_to_actual_sample_rate) {
    const int* initial_sample_rate =
        gutil::FindOrNull(initial_interfaces_to_sample_rate, interface);
    if (initial_sample_rate == nullptr) {
      return absl::FailedPreconditionError(absl::Substitute(
          "Interface $0 does not have a initial samplerate.", interface));
    }
    const int expected_sample_rate = multiple * (*initial_sample_rate);
    if (sample_rate != expected_sample_rate) {
      return absl::InternalError(
          absl::Substitute("Interface $0 sample rate is not as expected. "
                           "Expected sample rate: $1. Actual sample rate: $2.",
                           interface, expected_sample_rate, sample_rate));
    }
  }
  return absl::OkStatus();
}

absl::Status OutputTableEntriesToArtifact(pdpi::P4RuntimeSession& p4_session,
                                          thinkit::TestEnvironment& environment,
                                          absl::string_view artifact_name) {
  // Read entries back and store in an artifact.
  ASSIGN_OR_RETURN(pdpi::IrTableEntries entries,
                   pdpi::ReadIrTableEntries(p4_session));
  return environment.AppendToTestArtifact(artifact_name, entries.DebugString());

}

absl::StatusOr<int> GetPortIdFromInterfaceName(
    const absl::flat_hash_map<std::string, std::string>& port_id_per_port_name,
    const std::string& port_name) {
  const std::string* port_id_str =
      gutil::FindOrNull(port_id_per_port_name, port_name);
  if (port_id_str == nullptr) {
    return absl::NotFoundError(
        absl::Substitute("$0 not found in port_id_per_port_name", port_name));
  }
  int port_id;
  if (!absl::SimpleAtoi(*port_id_str, &port_id)) {
    return absl::InternalError(
        absl::Substitute("$0 is not a valid port id.", port_id_str));
  }
  return port_id;
}

absl::StatusOr<IxiaTrafficSettings> SetUpIxiaTrafficForSflowNsf(
    absl::Span<const IxiaLink> ixia_links,
    const absl::flat_hash_set<std::string>& sflow_enabled_interfaces,
    thinkit::GenericTestbed* testbed, gnmi::gNMI::StubInterface* gnmi_stub) {
  absl::flat_hash_map<std::string, int> initial_interfaces_to_sample_rate;
  ASSIGN_OR_RETURN(initial_interfaces_to_sample_rate,
                   GetSflowActualSamplingRateForInterfaces(
                       gnmi_stub, sflow_enabled_interfaces));

  const int interface_sample_rate =
      initial_interfaces_to_sample_rate.begin()->second;

  // Generate 10 samples/sec.
  int64_t traffic_rate = 10 * interface_sample_rate;

  // Set up Ixia traffic.
  ASSIGN_OR_RETURN(
      Openapi::StubInterface * traffic_client,
      SetUpIxiaTraffic(ixia_links, *testbed,
                       /*pkt_count=*/traffic_rate * kNsfTrafficTestDurationSecs,
                       /*pkt_rate=*/traffic_rate, *gnmi_stub));

  return IxiaTrafficSettings{
      .traffic_client = *traffic_client,
      .traffic_rate = traffic_rate,
      .sampling_rate = interface_sample_rate,
  };
}

absl::StatusOr<int> GetSflowSamplesAfterSendingIxiaTraffic(
    thinkit::GenericTestbed* testbed, thinkit::SSHClient* ssh_client,
    const IxiaLink& ingress_link,
    const IxiaTrafficSettings& ixia_traffic_settings, const int collector_port,
    const NosParameters& nos_param) {
  // Start sflowtool on SUT.
  std::string sflow_result;
  {
    ASSIGN_OR_RETURN(
        std::thread sflow_tool_thread,
        RunSflowCollectorForNSecs(
            *ssh_client, testbed->Sut().ChassisName(),
            SflowContainerExecCmdStr(nos_param, kSflowtoolLineFormatTemplate),
            collector_port,
            /*sflowtool_runtime=*/kNsfTrafficTestDurationSecs + 30,
            sflow_result));

    // Wait for sflowtool to finish.
    absl::Cleanup clean_up([&sflow_tool_thread] {
      if (sflow_tool_thread.joinable()) {
        sflow_tool_thread.join();
      }
    });

    RETURN_IF_ERROR(SendNPacketsToSut(
        ixia_traffic_settings.traffic_client,
        /*runtime=*/
        absl::Seconds(std::ceil(1.0f * kNsfTrafficTestDurationSecs))));

    // Sleep to wait for the counters to be reflected.
    absl::SleepFor(absl::Seconds(10));
  }

  RETURN_IF_ERROR(testbed->Environment().StoreTestArtifact(
      absl::StrCat(
          "sflow_result_",
          absl::FormatTime("%H_%M_%S", absl::Now(), absl::LocalTimeZone()),
          "_.txt"),
      sflow_result));

  return GetSflowSamplesOnSut(sflow_result, ingress_link.port_id);
}

void PerformBackoffTest(
    thinkit::GenericTestbed* testbed, gnmi::gNMI::StubInterface* gnmi_stub,
    thinkit::SSHClient* ssh_client, absl::Span<const IxiaLink> ixia_links,
    const std::string& sut_gnmi_config,
    const absl::flat_hash_set<std::string>& sflow_enabled_interfaces,
    const int collector_port, const NosParameters& nos_param) {
  // Read initial sample rate from testbed.
  absl::flat_hash_map<std::string, int> initial_interfaces_to_sample_rate;
  ASSERT_OK_AND_ASSIGN(initial_interfaces_to_sample_rate,
                       GetSflowActualSamplingRateForInterfaces(
                           gnmi_stub, sflow_enabled_interfaces));
  ASSERT_FALSE(initial_interfaces_to_sample_rate.empty());

  const int interface_sample_rate =
      initial_interfaces_to_sample_rate.begin()->second;

  const IxiaLink& ingress_link = ixia_links[0];

  int64_t traffic_rate = 10 * interface_sample_rate;

  ASSERT_OK_AND_ASSIGN(
      Openapi::StubInterface * traffic_client,
      SetUpIxiaTraffic(ixia_links, *testbed,
                       traffic_rate * kBackoffTrafficDurationSecs, traffic_rate,
                       *gnmi_stub));

  // Start sflowtool on SUT.
  std::string sflow_result;
  {
    ASSERT_OK_AND_ASSIGN(
        std::thread sflow_tool_thread,
        RunSflowCollectorForNSecs(
            *ssh_client, testbed->Sut().ChassisName(),
            SflowContainerExecCmdStr(nos_param, kSflowtoolLineFormatTemplate),
            collector_port,
            /*sflowtool_runtime=*/kBackoffTrafficDurationSecs + 30,
            sflow_result));

    // Wait for sflowtool to finish.
    absl::Cleanup clean_up([&sflow_tool_thread] {
      if (sflow_tool_thread.joinable()) {
        sflow_tool_thread.join();
      }
    });

    // Send packets from Ixia to SUT.
    ASSERT_OK(SendSflowTraffic(
        *traffic_client, {ingress_link}, *testbed, gnmi_stub,
        /*pkt_count=*/traffic_rate * kBackoffTrafficDurationSecs, traffic_rate,
        nos_param.kCpuQueueName));
  }

  ASSERT_OK(testbed->Environment().StoreTestArtifact(
      absl::StrCat("sFlow_samples_traffic_rate_", traffic_rate,
                   "_before_backoff.txt"),
      sflow_result));

  // Verify that sample rate on all interfaces is still the initial value.
  ASSERT_OK(IsExpectedSamplingRateFromGnmi(gnmi_stub, sflow_enabled_interfaces,
                                           initial_interfaces_to_sample_rate,
                                           /*multiple=*/1));
  // Verify that sample rate from sflowtool result is the same as initial.
  ASSERT_OK(
      IsExpectedSampleRateFromSamples(sflow_result, interface_sample_rate));

  // Setup Ixia for higher traffic speed to trigger sFlow backoff - it would
  // generate kBackOffThresholdSamples per sec.
  traffic_rate = kBackOffThresholdSamples * interface_sample_rate;
  int64_t packets_num = traffic_rate * kBackoffTrafficDurationSecs;

  GetConfigResponse get_config_response;
  ClientContext get_config_context;

  ASSERT_OK(
      traffic_client->GetConfig(&get_config_context, {}, &get_config_response));

  SetConfigRequest set_config_request;

  otg::Config* config = set_config_request.mutable_config();
  *config = get_config_response.config();
  otg::Flow* flow = config->mutable_flows(0);
  SetIxiaTrafficParams(*flow, packets_num, traffic_rate);

  {
    SetConfigResponse set_config_response;
    ClientContext set_config_context;
    LOG(INFO) << "Set Config Request: " << absl::StrCat(set_config_request);
    ASSERT_OK(traffic_client->SetConfig(&set_config_context, set_config_request,
                                        &set_config_response));
    LOG(INFO) << "Set Config Response: " << absl::StrCat(set_config_response);
  }

  // Start sflowtool on SUT.
  {
    ASSERT_OK_AND_ASSIGN(
        std::thread sflow_tool_thread,
        RunSflowCollectorForNSecs(
            *ssh_client, testbed->Sut().ChassisName(),
            SflowContainerExecCmdStr(nos_param, kSflowtoolLineFormatTemplate),
            collector_port,
            /*sflowtool_runtime=*/kBackoffTrafficDurationSecs + 30,
            sflow_result));

    // Wait for sflowtool to finish.
    absl::Cleanup clean_up([&sflow_tool_thread] {
      if (sflow_tool_thread.joinable()) {
        sflow_tool_thread.join();
      }
    });

    // Send packets from Ixia to SUT. We set the `expected_drop_ratio` to 0.05
    // since Ixia traffic unavoidably causes some drops on BE1 queue.
    ASSERT_OK(SendSflowTraffic(
        *traffic_client, {ingress_link}, *testbed, gnmi_stub,
        /*pkt_count=*/traffic_rate * kBackoffTrafficDurationSecs, traffic_rate,
        nos_param.kCpuQueueName));
  }

  ASSERT_OK(testbed->Environment().StoreTestArtifact(
      absl::StrCat("sFlow_samples_traffic_rate_", traffic_rate,
                   "_triggering_backoff.txt"),
      sflow_result));

  // Verify that sample rate on all interfaces is doubled.
  auto status = IsExpectedSamplingRateFromGnmi(
      gnmi_stub, sflow_enabled_interfaces, initial_interfaces_to_sample_rate,
      /*multiple=*/2);
  if (!status.ok()) {
    // Verify sflowtool result when backoff did not happen.
    const int sample_count =
        GetSflowSamplesOnSut(sflow_result, ingress_link.port_id);
    const double expected_count =
        static_cast<double>(packets_num) / interface_sample_rate;

    SflowResult result = SflowResult{
        .rule = "Backoff traffic",
        .sut_interface = ingress_link.sut_interface,
        .packets = packets_num,
        .sampling_rate = interface_sample_rate,
        .expected_samples = static_cast<int>(expected_count),
        .actual_samples = sample_count,
    };
    LOG(INFO) << "------ Test result ------\n" << result.DebugString();
    EXPECT_GE(sample_count, expected_count * (1 - kTolerance))
        << "Not enough samples on " << ingress_link.sut_interface;
    EXPECT_LE(sample_count, expected_count * (1 + kTolerance));
    GTEST_FAIL() << "backoff did not happen. Status:" << status.message();
  }

  // Use a normal traffic speed, sample rate should remain as doubled.
  traffic_rate = 10 * interface_sample_rate;
  packets_num = traffic_rate * kBackoffTrafficDurationSecs;

  SetIxiaTrafficParams(*flow, packets_num, traffic_rate);

  {
    SetConfigResponse set_config_response;
    ClientContext set_config_context;
    LOG(INFO) << "Set Config Request: " << absl::StrCat(set_config_request);
    ASSERT_OK(traffic_client->SetConfig(&set_config_context, set_config_request,
                                        &set_config_response));
    LOG(INFO) << "Set Config Response: " << absl::StrCat(set_config_response);
  }

  {
    // Start sflowtool on SUT.
    ASSERT_OK_AND_ASSIGN(
        std::thread sflow_tool_thread,
        RunSflowCollectorForNSecs(
            *ssh_client, testbed->Sut().ChassisName(),
            SflowContainerExecCmdStr(nos_param, kSflowtoolLineFormatTemplate),
            collector_port,
            /*sflowtool_runtime=*/kBackoffTrafficDurationSecs + 30,
            sflow_result));

    // Wait for sflowtool to finish.
    absl::Cleanup clean_up([&sflow_tool_thread] {
      if (sflow_tool_thread.joinable()) {
        sflow_tool_thread.join();
      }
    });

    // Send packets from Ixia to SUT.
    ASSERT_OK(SendSflowTraffic(
        *traffic_client, {ingress_link}, *testbed, gnmi_stub,
        /*pkt_count=*/traffic_rate * kBackoffTrafficDurationSecs, traffic_rate,
        nos_param.kCpuQueueName));
  }

  ASSERT_OK(testbed->Environment().StoreTestArtifact(
      absl::StrCat("sFlow_samples_traffic_rate_", traffic_rate,
                   "_after_backoff.txt"),
      sflow_result));

  // Verify that sample rate on all interfaces is still doubled.
  ASSERT_OK(IsExpectedSamplingRateFromGnmi(gnmi_stub, sflow_enabled_interfaces,
                                           initial_interfaces_to_sample_rate,
                                           /*multiple=*/2));
  // Verify that sample rate from sflowtool result is still doubled.
  EXPECT_OK(
      IsExpectedSampleRateFromSamples(sflow_result, 2 * interface_sample_rate));

  // Push initial config again, expect the sample rate is still doubled than
  // initial value.
  ASSERT_OK(pins_test::PushGnmiConfig(testbed->Sut(), sut_gnmi_config));
  ASSERT_OK(IsExpectedSamplingRateFromGnmi(gnmi_stub, sflow_enabled_interfaces,
                                           initial_interfaces_to_sample_rate,
                                           /*multiple=*/2));

  // Use a normal traffic speed, sample rate should remain as doubled.
  traffic_rate = 10 * interface_sample_rate;
  packets_num = traffic_rate * kBackoffTrafficDurationSecs;

  SetIxiaTrafficParams(*flow, packets_num, traffic_rate);

  {
    SetConfigResponse set_config_response;
    ClientContext set_config_context;
    LOG(INFO) << "Set Config Request: " << absl::StrCat(set_config_request);
    ASSERT_OK(traffic_client->SetConfig(&set_config_context, set_config_request,
                                        &set_config_response));
    LOG(INFO) << "Set Config Response: " << absl::StrCat(set_config_response);
  }

  {
    // Start sflowtool on SUT.
    ASSERT_OK_AND_ASSIGN(
        std::thread sflow_tool_thread,
        RunSflowCollectorForNSecs(
            *ssh_client, testbed->Sut().ChassisName(),
            SflowContainerExecCmdStr(nos_param, kSflowtoolLineFormatTemplate),
            collector_port,
            /*sflowtool_runtime=*/kBackoffTrafficDurationSecs + 30,
            sflow_result));

    // Wait for sflowtool to finish.
    absl::Cleanup clean_up([&sflow_tool_thread] {
      if (sflow_tool_thread.joinable()) {
        sflow_tool_thread.join();
      }
    });

    // Send packets from Ixia to SUT.
    ASSERT_OK(SendSflowTraffic(
        *traffic_client, {ingress_link}, *testbed, gnmi_stub,
        /*pkt_count=*/traffic_rate * kBackoffTrafficDurationSecs, traffic_rate,
        nos_param.kCpuQueueName));
  }

  ASSERT_OK(testbed->Environment().StoreTestArtifact(
      absl::StrCat("sFlow_samples_traffic_rate_", traffic_rate,
                   "_config_push_after_backoff.txt"),
      sflow_result));

  // Verify that sample rate is still doubled.
  ASSERT_OK(IsExpectedSamplingRateFromGnmi(gnmi_stub, sflow_enabled_interfaces,
                                           initial_interfaces_to_sample_rate,
                                           /*multiple=*/2));
  EXPECT_OK(
      IsExpectedSampleRateFromSamples(sflow_result, 2 * interface_sample_rate));
}

}  // namespace

void SflowTestFixture::SetUp() {
  GetParam().testbed_interface->SetUp();
  ASSERT_NE(ssh_client_, nullptr);
  // Pick a testbed with an Ixia Traffic Generator.
  auto requirements =
      gutil::ParseProtoOrDie<thinkit::TestRequirements>(
          R"pb(interface_requirements {
                 count: 1
                 interface_modes: TRAFFIC_GENERATOR
               })pb");

  ASSERT_OK_AND_ASSIGN(
      testbed_,
      GetParam().testbed_interface->GetTestbedWithRequirements(requirements));
  
  nos_param_ = GetParam().nos_is_sonic ? nos_param_sonic : GetParam().nos_param; 
  CollectSflowDebugs(ssh_client_, testbed_->Sut().ChassisName(),
                     /*prefix=*/"preconfig_", testbed_->Environment(),
                     nos_param_);

  ASSERT_OK(GetParam().ssh_client->RunCommand(
      testbed_->Sut().ChassisName(),
      /*command=*/
      nos_param_.kRedisExecPrefix +
          "redis-cli -n 14 hset \"PORT_TABLE:CPU\" \"NULL\" \"NULL\"",
      absl::Seconds(20)));

  std::vector<std::pair<std::string, int>> collector_address_and_port;
  const std::string& gnmi_config = GetParam().gnmi_config;
  ASSERT_OK(testbed_->Environment().StoreTestArtifact("gnmi_config.txt",
                                                      gnmi_config));
  int sampling_size = kSampleHeaderSize;
  int sampling_rate = kSamplingRateInterval;
  // Used for setting collector. It would be set to 6344.
  collector_port_ = GetSflowCollectorPort();

  // Set to localhost ip by default.
  collector_address_and_port.push_back({kLocalLoopbackIpv6, collector_port_});
  ASSERT_OK_AND_ASSIGN(std::string agent_addr_ipv6,
                       GetLoopbackAddrIpv6FromConfig(gnmi_config));
  absl::flat_hash_map<std::string, bool> sflow_enabled_interfaces;
  ASSERT_OK_AND_ASSIGN(sflow_enabled_interfaces,
                       GetSflowInterfacesFromSut(*testbed_));

  ASSERT_OK_AND_ASSIGN(
      gnmi_config_with_sflow_,
      UpdateSflowConfig(gnmi_config, agent_addr_ipv6,
                        collector_address_and_port, sflow_enabled_interfaces,
                        sampling_rate, sampling_size));
  ASSERT_OK(testbed_->Environment().StoreTestArtifact(
      "gnmi_config_with_sflow.txt",
      json_yang::FormatJsonBestEffort(gnmi_config_with_sflow_)));
  ASSERT_OK(testbed_->Environment().StoreTestArtifact(
      "p4info.pb.txt", GetP4Info().DebugString()));
  ASSERT_OK_AND_ASSIGN(
      sut_p4_session_,
      pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
          testbed_->Sut(), gnmi_config_with_sflow_, GetP4Info()));
  ASSERT_OK_AND_ASSIGN(ir_p4_info_, pdpi::CreateIrP4Info(GetP4Info()));
  ASSERT_OK_AND_ASSIGN(gnmi_stub_, testbed_->Sut().CreateGnmiStub());

  // Wait until all sFLow gNMI states are converged.
  ASSERT_OK(pins_test::WaitForCondition(
      VerifySflowStatesConverged, absl::Seconds(30), gnmi_stub_.get(),
      agent_addr_ipv6, sampling_rate, sampling_size, collector_address_and_port,
      sflow_enabled_interfaces));

  ASSERT_OK_AND_ASSIGN(ready_links_,
                       GetIxiaConnectedUpLinks(*testbed_, *gnmi_stub_));
  ASSERT_GE(ready_links_.size(), 2) << "Ixia links are not ready";

  CollectSflowDebugs(ssh_client_, testbed_->Sut().ChassisName(),
                     /*prefix=*/"pretest_", testbed_->Environment(),
                     nos_param_);
}

void SflowTestFixture::TearDown() {
  LOG(INFO) << "\n------ TearDown START ------\n";
  ASSERT_NE(testbed_, nullptr);
  
  CollectSflowDebugs(ssh_client_, testbed_->Sut().ChassisName(),
                     /*prefix=*/"posttest_", testbed_->Environment(),
                     nos_param_);

  if (sut_p4_session_ != nullptr) {
    EXPECT_OK(OutputTableEntriesToArtifact(
        *sut_p4_session_, testbed_->Environment(),
        /*artifact_name=*/"posttest_SUT_table_entries.txt"));
  }

  // Restore gNMI config, clear table entries and stop RPC sessions.
  ASSERT_OK_AND_ASSIGN(auto sflow_enabled,
                       IsSflowConfigEnabled(GetParam().gnmi_config));
  ASSERT_OK_AND_ASSIGN(auto stub, testbed_->Sut().CreateGnmiStub());
  ASSERT_OK(SetSflowConfigEnabled(stub.get(), sflow_enabled));
  ASSERT_OK(pins_test::PushGnmiConfig(testbed_->Sut(), GetParam().gnmi_config));
  if (sut_p4_session_ != nullptr) {
    EXPECT_OK(pdpi::ClearTableEntries(sut_p4_session_.get()));
    EXPECT_OK(sut_p4_session_->Finish());
  }
  GetParam().testbed_interface->TearDown();
  if (ssh_client_ != nullptr) {
    delete ssh_client_;
    ssh_client_ = nullptr;
  }
  if (GetParam().testbed_interface != nullptr) {
    delete GetParam().testbed_interface;
  }

  LOG(INFO) << "\n------ TearDown END ------\n";
}

// This test checks sFlow works as expected with no rules.
// 1. Set up Ixia traffic and send packets to SUT via Ixia.
// 2. Collect sFlow samples via sflowtool on SUT.
// 3. Validate the result is as expected.
TEST_P(SflowTestFixture, VerifyIngressSamplingForNoMatchPackets) {

  const IxiaLink& ingress_link = ready_links_[0];
  Port ingress_port = Port{
      .interface_name = ingress_link.sut_interface,
      .port_id = ingress_link.port_id,
  };
  const int pkt_size = 500;

  // Set up Ixia traffic.
  ASSERT_OK_AND_ASSIGN(
      Openapi::StubInterface * traffic_client,
      SetUpIxiaTraffic({ready_links_[0], ready_links_[1]}, *testbed_,
                       kPacketsNum, kPacketsPerSecond, *gnmi_stub_, pkt_size));

  std::string sflow_result;
  {
    // Start sflowtool on SUT.
    ASSERT_OK_AND_ASSIGN(
        std::thread sflow_tool_thread,
        RunSflowCollectorForNSecs(
            *ssh_client_, testbed_->Sut().ChassisName(),
            SflowContainerExecCmdStr(nos_param_, kSflowtoolLineFormatTemplate),
            collector_port_,
            /*sflowtool_runtime=*/kPacketsNum / kPacketsPerSecond + 30,
            sflow_result));

    // Wait for sflowtool to finish.
    absl::Cleanup clean_up([&sflow_tool_thread] {
      if (sflow_tool_thread.joinable()) {
        sflow_tool_thread.join();
      }
    });

    // Send packets from Ixia to SUT.
    ASSERT_OK(SendSflowTraffic(*traffic_client, {ingress_link}, *testbed_,
                               gnmi_stub_.get(), kPacketsNum, kPacketsPerSecond,
                               nos_param_.kCpuQueueName));
  }

  LOG(INFO) << "sFlow samples:\n" << sflow_result;
  EXPECT_OK(testbed_->Environment().StoreTestArtifact("sflow_result.txt",
                                                      sflow_result));
  VerifySflowResult(sflow_result, ingress_port.port_id,
                    !nos_param_.kIsSonicDebianLinux ? kDropPort : kCpuPort,
                    kSourceMac.ToHexString(), kDstMac.ToHexString(),
                    kEtherTypeIpv4, kIpv4Src.ToString(),
                    GetDstIpv4AddrByPortId(ingress_link.port_id), pkt_size,
                    kSamplingRateInterval);

  // Verify sflowtool result. Since we use port id to generate packets, we use
  // port id to filter sFlow packets.
  const int sample_count =
      GetSflowSamplesOnSut(sflow_result, ingress_port.port_id);
  const double expected_count = 1.0 * kPacketsNum / kSamplingRateInterval;
  SflowResult result = SflowResult{
      .sut_interface = ingress_port.interface_name,
      .packets = kPacketsNum,
      .sampling_rate = kSamplingRateInterval,
      .expected_samples = static_cast<int>(expected_count),
      .actual_samples = sample_count,
  };
  LOG(INFO) << "------ Test result ------\n" << result.DebugString();
  EXPECT_GE(sample_count, expected_count * (1 - kTolerance))
      << "Not enough samples on " << ingress_port.interface_name;
  EXPECT_LE(sample_count, expected_count * (1 + kTolerance));
}

// Verifies ingress sampling could work when forwarding traffic.
TEST_P(SflowTestFixture, VerifyIngressSamplingForForwardedPackets) {
  const IxiaLink& ingress_link = ready_links_[0];
  Port ingress_port = Port{
      .interface_name = ingress_link.sut_interface,
      .port_id = ingress_link.port_id,
  };
  ASSERT_OK_AND_ASSIGN(
      Port egress_port,
      GetUnusedUpPort(*gnmi_stub_, ingress_port.interface_name));
  // Programs forwarding rule.
  ASSERT_OK_AND_ASSIGN(std::vector<GroupMember> members,
                       CreateGroupMembers(1, {egress_port.port_id}));
  ASSERT_OK(pins::ProgramNextHops(testbed_->Environment(), *sut_p4_session_,
                                   GetIrP4Info(), members));
  const std::string& egress_next_hop_id = members[0].nexthop;
  ASSERT_OK(SetSutVrf(*sut_p4_session_, GetP4Info(), GetIrP4Info(),
                      {ingress_port.port_id}));

  // Allow the destination mac address to L3.
  ASSERT_OK(ProgramL3Admit(
      *sut_p4_session_, ir_p4_info_,
      L3AdmitOptions{
          .priority = 2070,
          .dst_mac = std::make_pair(kDstMac.ToString(), "FF:FF:FF:FF:FF:FF"),
      }));
  ASSERT_OK(ProgramRoutes(*sut_p4_session_, GetIrP4Info(), ingress_port.port_id,
                          egress_next_hop_id));

  const int pkt_size = 500;

  ASSERT_OK_AND_ASSIGN(
      Openapi::StubInterface * traffic_client,
      SetUpIxiaTraffic({ready_links_[0], ready_links_[1]}, *testbed_,
                       kPacketsNum, kPacketsPerSecond, *gnmi_stub_, pkt_size));

  std::string sflow_result;
  {
    // Start sflowtool on SUT.
    ASSERT_OK_AND_ASSIGN(
        std::thread sflow_tool_thread,
        RunSflowCollectorForNSecs(
            *ssh_client_, testbed_->Sut().ChassisName(),
            SflowContainerExecCmdStr(nos_param_, kSflowtoolLineFormatTemplate),
            collector_port_,
            /*sflowtool_runtime=*/kPacketsNum / kPacketsPerSecond + 30,
            sflow_result));

    // Wait for sflowtool to finish.
    absl::Cleanup clean_up([&sflow_tool_thread] {
      if (sflow_tool_thread.joinable()) {
        sflow_tool_thread.join();
      }
    });

    // Send packets from Ixia to SUT.
    ASSERT_OK(SendSflowTraffic(*traffic_client, {ingress_link}, *testbed_,
                               gnmi_stub_.get(), kPacketsNum, kPacketsPerSecond,
                               nos_param_.kCpuQueueName));
  }

  LOG(INFO) << "sFlow samples:\n" << sflow_result;
  EXPECT_OK(testbed_->Environment().StoreTestArtifact("sflow_result.txt",
                                                      sflow_result));
  VerifySflowResult(sflow_result, ingress_port.port_id, egress_port.port_id,
                    kSourceMac.ToHexString(), kDstMac.ToHexString(),
                    kEtherTypeIpv4, kIpv4Src.ToString(),
                    GetDstIpv4AddrByPortId(ingress_link.port_id), pkt_size,
                    kSamplingRateInterval);

  // Verify sflowtool result. Since we use port id to generate packets, we use
  // port id to filter sFlow packets.
  const int sample_count =
      GetSflowSamplesOnSut(sflow_result, ingress_port.port_id);
  const double expected_count = 1.0 * kPacketsNum / kSamplingRateInterval;
  EXPECT_GE(sample_count, expected_count * (1 - kTolerance))
      << "Not enough samples on " << ingress_port.interface_name;
  EXPECT_LE(sample_count, expected_count * (1 + kTolerance));
  SflowResult result = SflowResult{
      .rule = "Forward traffic",
      .sut_interface = ingress_port.interface_name,
      .packets = kPacketsNum,
      .sampling_rate = kSamplingRateInterval,
      .expected_samples = static_cast<int>(expected_count),
      .actual_samples = sample_count,
  };
  LOG(INFO) << "------ Test result ------\n" << result.DebugString();
}

// Verifies ingress sampling could work when dropping packets.
TEST_P(SflowTestFixture, VerifyIngressSamplesForDropPackets) {
  const IxiaLink& ingress_link = ready_links_[0];
  Port ingress_port = Port{
      .interface_name = ingress_link.sut_interface,
      .port_id = ingress_link.port_id,
  };
  ASSERT_OK(
      SetUpAclDrop(*sut_p4_session_, GetIrP4Info(), ingress_port.port_id));
  const int pkt_size = 500;

  ASSERT_OK_AND_ASSIGN(
      Openapi::StubInterface * traffic_client,
      SetUpIxiaTraffic({ready_links_[0], ready_links_[1]}, *testbed_,
                       kPacketsNum, kPacketsPerSecond, *gnmi_stub_, pkt_size));

  std::string sflow_result;
  {
    // Start sflowtool on SUT.
    ASSERT_OK_AND_ASSIGN(
        std::thread sflow_tool_thread,
        RunSflowCollectorForNSecs(
            *ssh_client_, testbed_->Sut().ChassisName(),
            SflowContainerExecCmdStr(nos_param_, kSflowtoolLineFormatTemplate),
            collector_port_,
            /*sflowtool_runtime=*/kPacketsNum / kPacketsPerSecond + 30,
            sflow_result));

    // Wait for sflowtool to finish.
    absl::Cleanup clean_up([&sflow_tool_thread] {
      if (sflow_tool_thread.joinable()) {
        sflow_tool_thread.join();
      }
    });

    // Send packets from Ixia to SUT.
    ASSERT_OK(SendSflowTraffic(*traffic_client, {ingress_link}, *testbed_,
                               gnmi_stub_.get(), kPacketsNum, kPacketsPerSecond,
                               nos_param_.kCpuQueueName));
  }

  LOG(INFO) << "sFlow samples:\n" << sflow_result;
  EXPECT_OK(testbed_->Environment().StoreTestArtifact("sflow_result.txt",
                                                      sflow_result));
  VerifySflowResult(sflow_result, ingress_port.port_id,
                    !nos_param_.kIsSonicDebianLinux ? kDropPort : kCpuPort,
                    kSourceMac.ToHexString(), kDstMac.ToHexString(),
                    kEtherTypeIpv4, kIpv4Src.ToString(),
                    GetDstIpv4AddrByPortId(ingress_link.port_id), pkt_size,
                    kSamplingRateInterval);

  // Verify sflowtool result. Since we use port id to generate packets, we use
  // port id to filter sFlow packets.
  const int sample_count =
      GetSflowSamplesOnSut(sflow_result, ingress_port.port_id);
  const double expected_count = 1.0 * kPacketsNum / kSamplingRateInterval;
  EXPECT_GE(sample_count, expected_count * (1 - kTolerance))
      << "Not enough samples on " << ingress_port.interface_name;
  EXPECT_LE(sample_count, expected_count * (1 + kTolerance));
  SflowResult result = SflowResult{
      .rule = "Drop traffic",
      .sut_interface = ingress_port.interface_name,
      .packets = kPacketsNum,
      .sampling_rate = kSamplingRateInterval,
      .expected_samples = static_cast<int>(expected_count),
      .actual_samples = sample_count,
  };
  LOG(INFO) << "------ Test result ------\n" << result.DebugString();
}

// Verify ingress sampling could work when punting traffic.
// 1. Set sFlow config on SUT with kLocalLoopbackIpv6 as collector address.
// 2. Set P4 punt rule on SUT to punt received packets.
// 3. Send traffic from Ixia.
// 4. Validate the packets are all get punted and sFlowtool has expected result.
TEST_P(SflowTestFixture, VerifyIngressSamplesForP4rtPuntTraffic) {
  const IxiaLink& ingress_link = ready_links_[0];
  Port ingress_port = Port{
      .interface_name = ingress_link.sut_interface,
      .port_id = ingress_link.port_id,
  };

  ASSERT_OK(
      SetUpAclPunt(*sut_p4_session_, GetIrP4Info(), ingress_link.port_id));
  EXPECT_OK(
      OutputTableEntriesToArtifact(*sut_p4_session_, testbed_->Environment(),
                                   /*artifact_name=*/"SUT_table_entries.txt"));

  // Use a smaller packets num and traffic speed since we need to check punt
  // packets data.
  const int packets_num = 100000;
  const int traffic_speed = 400;
  const int packet_size = 1000;

  ASSERT_OK_AND_ASSIGN(
      Openapi::StubInterface * traffic_client,
      SetUpIxiaTraffic({ready_links_[0], ready_links_[1]}, *testbed_,
                       packets_num, traffic_speed, *gnmi_stub_, packet_size));
  std::string sflow_result;

  absl::Time start_time;
  ASSERT_OK_AND_ASSIGN(auto initial_cpu_counter,
                       ReadCounters("CPU", gnmi_stub_.get()));
  ASSERT_OK_AND_ASSIGN(auto p4rt_queue_name,
                       GetP4rtQueueName(gnmi_stub_.get()));
  ASSERT_OK_AND_ASSIGN(
      auto initial_queue_counter,
      pins_test::GetGnmiQueueCounters("CPU", p4rt_queue_name, *gnmi_stub_));

  // 1. Start sflowtool on SUT.
  // 2. Send packets from Ixia to SUT.
  // 3. Wait for sflowtool to finish.
  {
    ASSERT_OK_AND_ASSIGN(
        std::thread sflow_tool_thread,
        RunSflowCollectorForNSecs(
            *GetParam().ssh_client, testbed_->Sut().ChassisName(),
            SflowContainerExecCmdStr(nos_param_, kSflowtoolLineFormatTemplate),
            collector_port_,
            /*sflowtool_runtime=*/
            packets_num / traffic_speed + 30, sflow_result));

    absl::Cleanup clean_up([&sflow_tool_thread] {
      if (sflow_tool_thread.joinable()) {
        sflow_tool_thread.join();
      }
    });

    start_time = absl::Now();
    ASSERT_OK(SendSflowTraffic(*traffic_client, {ingress_link}, *testbed_,
                               gnmi_stub_.get(), packets_num, traffic_speed,
                               nos_param_.kCpuQueueName));
  }
  EXPECT_OK(testbed_->Environment().StoreTestArtifact("sflow_result.txt",
                                                      sflow_result));
  VerifySflowResult(sflow_result, ingress_port.port_id, kCpuPort,
                    kSourceMac.ToHexString(), kDstMac.ToHexString(),
                    kEtherTypeIpv4, kIpv4Src.ToString(),
                    GetDstIpv4AddrByPortId(ingress_link.port_id), packet_size,
                    kSamplingRateInterval);

  // Display the difference for CPU counter during test dev.
  ASSERT_OK_AND_ASSIGN(auto final_cpu_counter,
                       ReadCounters("CPU", gnmi_stub_.get()));
  auto delta = DeltaCounters(initial_cpu_counter, final_cpu_counter);
  // TODO: Enable this after CPU in/out pkts are supported.
  // EXPECT_GE(delta.in_pkts, packets_num);
  LOG(INFO) << "CPU counter delta during traffic.\n Total time: "
            << (absl::Now() - start_time);
  ShowCounters(delta);

  ASSERT_OK_AND_ASSIGN(
      auto final_queue_counter,
      pins_test::GetGnmiQueueCounters("CPU", p4rt_queue_name, *gnmi_stub_));
  auto delta_queue_counter = final_queue_counter - initial_queue_counter;
  LOG(INFO) << "CPU P4RT queue counter delta:\n"
            << delta_queue_counter
            << " \n total time: " << (absl::Now() - start_time);
  // TODO: Enable this after counter data is stable.
  // EXPECT_EQ(delta_queue_counter.num_packets_transmitted, packets_num);

  // Verify all packets have been punted.
  EXPECT_OK(pdpi::ClearTableEntries(sut_p4_session_.get()));
  ASSERT_OK_AND_ASSIGN(
      std::vector<p4::v1::StreamMessageResponse> control_packets_in,
      sut_p4_session_->ReadStreamChannelResponsesAndFinish());
  // Set to nullptr to avoid duplicate Finish() call during TearDown.
  sut_p4_session_ = nullptr;
  int num_packets_punted = 0;
  for (const auto& packet_in : control_packets_in) {
    if (packet_in.has_packet()) {
      num_packets_punted++;
    } else {
      LOG(WARNING) << "Unexpected message received in streamchannel: "
                   << packet_in.DebugString();
    }
  }
  // TODO: Remove the percentage check when optics clean are
  // scheduled regularly.
  EXPECT_GE(num_packets_punted, packets_num / 100 * kPassingPercentagePktPunt)
      << absl::StreamFormat(
             "Expected punted packets: %d. Actually punted packets: %d.",
             packets_num, num_packets_punted);

  // Verify sflowtool result. Since we use port id to generate packets, we use
  // port id to filter sFlow packets.
  const int sample_count =
      GetSflowSamplesOnSut(sflow_result, ingress_port.port_id);
  const double expected_count =
      static_cast<double>(packets_num) / kSamplingRateInterval;
  SflowResult result = SflowResult{
      .rule = "Punt traffic",
      .sut_interface = ingress_port.interface_name,
      .packets = packets_num,
      .sampling_rate = kSamplingRateInterval,
      .expected_samples = static_cast<int>(expected_count),
      .actual_samples = sample_count,
  };
  LOG(INFO) << "------ Test result ------\n" << result.DebugString();
  // Only validates sample count is not empty since traffic number is low in
  // this test case and the deviation is high.
  EXPECT_GT(sample_count, 0)
      << " No samples on " << ingress_port.interface_name;
}

// Verifies sampling size could work:
// Traffic packet size size_a, sFlow sampling size size_b: expects sample header
// size equals to min(size_a, size_b).
TEST_P(SampleSizeTest, VerifySamplingSizeWorks) {

  const int packet_size = GetParam().packet_size,
            sample_size = GetParam().sample_size;
  ASSERT_NE(packet_size, 0);
  ASSERT_NE(sample_size, 0);

  ASSERT_OK(SetSflowSamplingSize(gnmi_stub_.get(), sample_size));
  const IxiaLink& ingress_link = ready_links_[0];

  // Set up Ixia traffic.
  ASSERT_OK_AND_ASSIGN(
      Openapi::StubInterface * traffic_client,
      SetUpIxiaTraffic({ready_links_[0], ready_links_[1]}, *testbed_,
                       kPacketsNum, kPacketsPerSecond, *gnmi_stub_,
                       packet_size));

  // Start sflowtool on SUT.
  std::string sflow_result;
  {
    // Start sflowtool on SUT.
    ASSERT_OK_AND_ASSIGN(
        std::thread sflow_tool_thread,
        RunSflowCollectorForNSecs(
            *ssh_client_, testbed_->Sut().ChassisName(),
            SflowContainerExecCmdStr(nos_param_, kSflowtoolFullFormatTemplate),
            collector_port_,
            /*sflowtool_runtime=*/kPacketsNum / kPacketsPerSecond + 30,
            sflow_result));

    // Wait for sflowtool to finish.
    absl::Cleanup clean_up([&sflow_tool_thread] {
      if (sflow_tool_thread.joinable()) {
        sflow_tool_thread.join();
      }
    });

    // Send packets from Ixia to SUT.
    ASSERT_OK(SendSflowTraffic(*traffic_client, {ingress_link}, *testbed_,
                               gnmi_stub_.get(), kPacketsNum, kPacketsPerSecond,
                               nos_param_.kCpuQueueName));
  }

  LOG(INFO) << "sFlow samples with sampling size " << sample_size << ":\n"
            << sflow_result;
  EXPECT_OK(testbed_->Environment().StoreTestArtifact("sflow_result.txt",
                                                      sflow_result));
  EXPECT_THAT(
      GetHeaderLenFromSflowOutput(
          sflow_result, ingress_link.port_id,
          absl::Substitute("sFLow_datagram_packet_size_$0_sampling_size_$1.txt",
                           packet_size, sample_size),
          testbed_->Environment()),
      // sFlow would strip some bytes from each packet.
      IsOkAndHolds(std::min(sample_size, packet_size - 4)))
      << "Samples on " << ingress_link.sut_interface << " are not as expected.";
}

// Verifies sampling rate could work:
// send traffic to two interfaces with different sampling rate and verifies
// samples count.
TEST_P(SampleRateTest, VerifySamplingRateWorks) {

  const IxiaLink& ingress_link = ready_links_[0];
  const int sample_rate = GetParam().sample_rate;
  ASSERT_GT(sample_rate, 0);
  const int64_t traffic_rate = sample_rate * 2;
  // Run 300s.
  const int64_t packets_num = sample_rate * 600;
  const int pkt_size = 500;

  ASSERT_OK(SetSflowIngressSamplingRate(
      gnmi_stub_.get(), ingress_link.sut_interface, sample_rate));

  // Set up Ixia traffic.
  ASSERT_OK_AND_ASSIGN(
      Openapi::StubInterface * traffic_client,
      SetUpIxiaTraffic({ready_links_[0], ready_links_[1]}, *testbed_,
                       packets_num, traffic_rate, *gnmi_stub_, pkt_size));

  std::string sflow_result;
  {
    // Start sflowtool on SUT.
    ASSERT_OK_AND_ASSIGN(
        std::thread sflow_tool_thread,
        RunSflowCollectorForNSecs(
            *ssh_client_, testbed_->Sut().ChassisName(),
            SflowContainerExecCmdStr(nos_param_, kSflowtoolLineFormatTemplate),
            collector_port_,
            /*sflowtool_runtime=*/packets_num / traffic_rate + 30,
            sflow_result));

    // Wait for sflowtool to finish.
    absl::Cleanup clean_up([&sflow_tool_thread] {
      if (sflow_tool_thread.joinable()) {
        sflow_tool_thread.join();
      }
    });

    // Send packets from Ixia to SUT.
    ASSERT_OK(SendSflowTraffic(*traffic_client, {ingress_link}, *testbed_,
                               gnmi_stub_.get(), packets_num, traffic_rate,
                               nos_param_.kCpuQueueName));
  }

  EXPECT_OK(testbed_->Environment().StoreTestArtifact(
      absl::Substitute("sflow_result_sampling_rate_$0_result.txt", sample_rate),
      sflow_result));
  VerifySflowResult(sflow_result, ingress_link.port_id,
                    /*output_port=*/std::nullopt, kSourceMac.ToHexString(),
                    kDstMac.ToHexString(), kEtherTypeIpv4, kIpv4Src.ToString(),
                    GetDstIpv4AddrByPortId(ingress_link.port_id), pkt_size,
                    sample_rate);

  // Verify sflowtool result. Since we use port id to generate packets, we use
  // port id to filter sFlow packets.
  const int sample_count =
      GetSflowSamplesOnSut(sflow_result, ingress_link.port_id);
  const double expected_count =
      static_cast<double>(packets_num) / static_cast<double>(sample_rate);
  SflowResult result = SflowResult{
      .sut_interface = ingress_link.sut_interface,
      .packets = packets_num,
      .sampling_rate = sample_rate,
      .expected_samples = static_cast<int>(expected_count),
      .actual_samples = sample_count,
  };
  LOG(INFO) << "------ Test result ------\n" << result.DebugString();

  // TODO: tune the tolerance rate of sampling rate test
  // since sample count seems like to be more deviated when the sample rate
  // is high.
  EXPECT_GE(sample_count, expected_count * (1 - kTolerance))
      << "Not enough samples on " << ingress_link.sut_interface;
  EXPECT_LE(sample_count, expected_count * (1 + kTolerance));
}

// 1. Send traffic at a normal rate (not triggering sFLow backoff) and verify
// the sampling rate doesn't change.
// 2. Send traffic at a high rate to trigger sFlow backoff. Verify that sample
// rate is doubled on all interfaces and samples.
// 3. Send traffic at a normal rate which would not trigger sFlow backoff.
// Verify that sample rate is still doubled on all interfaces and samples.
TEST_P(BackoffTest, VerifyBackoffWorks) {
  if (GetParam().nsf_enabled) {
    GTEST_SKIP() << "NSF is enabled, skip VerifyBackoffWorks test.";
  }

  absl::flat_hash_map<std::string, bool> sflow_interfaces;
  ASSERT_OK_AND_ASSIGN(sflow_interfaces, GetSflowInterfacesFromSut(*testbed_));
  absl::flat_hash_set<std::string> sflow_enabled_interfaces;
  for (const auto& [name, enabled] : sflow_interfaces) {
    if (enabled) {
      sflow_enabled_interfaces.insert(name);
    }
  }
  PerformBackoffTest(testbed_.get(), gnmi_stub_.get(), ssh_client_,
                     {ready_links_[0], ready_links_[1]},
                     gnmi_config_with_sflow_, sflow_enabled_interfaces,
                     collector_port_, nos_param_);
}

// Sflow measurement test:
// Measure sflow sampling rate, CPU usage, mem usage
TEST_P(MeasurementTest, BasicMeasurementTest) {

  IxiaLink& ingress_link = ready_links_[0];
  IxiaLink& egress_link = ready_links_[1];
  for (int i = 0; i < ready_links_.size(); i++) {
    if (ready_links_[i].sut_interface == "Ethernet1/1/1") {
      ingress_link = ready_links_[i];
      if (i == 1) {
        egress_link = ready_links_[0];
      }
    }
  }

  const int sample_rate = GetParam().sample_rate;
  ASSERT_GT(sample_rate, 0);
  int run_time = GetParam().run_time;
  int pkt_size = GetParam().packet_size;
  int64_t traffic_speed = GetParam().traffic_speed;  // bandwidth in G
  int64_t packets_num = 1000000000 / 8 / pkt_size * run_time * traffic_speed;
  ASSERT_GT(packets_num, 0);

  const int64_t traffic_rate = packets_num / run_time;
  LOG(INFO) << "sflow measurement test parameters: packets num: " << packets_num
            << " run_time: " << run_time << " traffic rate: " << traffic_rate
            << " sample_rate: " << sample_rate << " pkt_size: " << pkt_size;
  LOG(INFO) << "sflow Measurement test: interface: "
            << ingress_link.sut_interface;

  ASSERT_OK(SetSflowIngressSamplingRate(
      gnmi_stub_.get(), ingress_link.sut_interface, sample_rate));
  LOG(INFO) << "Interface for sending traffic: " << ingress_link.sut_interface;

  ASSERT_OK_AND_ASSIGN(
      Openapi::StubInterface * traffic_client,
      SetUpIxiaTraffic({ingress_link, egress_link}, *testbed_, packets_num,
                       traffic_rate, *gnmi_stub_, pkt_size));

  std::vector<int> actual_result;
  int its = GetParam().iterations;
  for (int i = 0; i < its; ++i) {
    // Start sflowtool on SUT.
    LOG(INFO) << "Test_Step 1: Start sflowtool on SUT.";
    std::string sflow_result;

    ASSERT_OK_AND_ASSIGN(
        std::thread sflow_tool_thread,
        RunSflowCollectorForNSecs(
            *ssh_client_, testbed_->Sut().ChassisName(),
            SflowContainerExecCmdStr(nos_param_, kSflowtoolLineFormatTemplate),
            collector_port_,
            /*sflowtool_runtime=*/run_time + 60, sflow_result));

    std::string top_command_result;
    std::string cpu_idle_result;
    std::string memory_usage;
    std::thread top_thread;
    std::thread cpu_idle_thread;
    std::thread memory_usage_thread;
    bool measure_cpumem = GetParam().measure_cpumem;
    if (measure_cpumem) {
      ASSERT_OK_AND_ASSIGN(
          top_thread,
          RunTopCommandForSflow(*ssh_client_, testbed_->Sut().ChassisName(),
                                run_time, top_command_result));

      ASSERT_OK_AND_ASSIGN(
          cpu_idle_thread,
          ShowCpuIdle(*ssh_client_, testbed_->Sut().ChassisName(), run_time,
                      cpu_idle_result));

      ASSERT_OK_AND_ASSIGN(
          memory_usage_thread,
          ShowMemory(*ssh_client_, testbed_->Sut().ChassisName(), run_time,
                     memory_usage));
    }

    // Send packets from Ixia to SUT.
    ASSERT_OK(SendSflowTraffic(*traffic_client, {ingress_link}, *testbed_,
                               gnmi_stub_.get(), packets_num, traffic_rate,
                               nos_param_.kCpuQueueName));

    // Wait for sflowtool to finish.
    if (sflow_tool_thread.joinable()) {
      sflow_tool_thread.join();
    }

    if (measure_cpumem) {
      if (top_thread.joinable()) {
        top_thread.join();
      }
      if (cpu_idle_thread.joinable()) {
        cpu_idle_thread.join();
      }
      if (memory_usage_thread.joinable()) {
        memory_usage_thread.join();
      }
    }

    EXPECT_OK(testbed_->Environment().StoreTestArtifact(
        absl::Substitute("sflow_result_sampling_rate_$0_run_$1_result.txt",
                         sample_rate, i),
        sflow_result));

    if (measure_cpumem) {
      EXPECT_OK(testbed_->Environment().AppendToTestArtifact(
          "sflow_top_result.txt",
          absl::Substitute(
              "\n\n\n==================Test_run: $0==================\n\n\n",
              i)));
      EXPECT_OK(testbed_->Environment().AppendToTestArtifact(
          "sflow_top_result.txt", top_command_result));
      EXPECT_OK(testbed_->Environment().AppendToTestArtifact(
          "cpu_idle_rate.txt",
          absl::Substitute(
              "\n\n\n==================Test_run: $0==================\n\n\n",
              i)));
      EXPECT_OK(testbed_->Environment().AppendToTestArtifact(
          "cpu_idle_rate.txt", cpu_idle_result));
      EXPECT_OK(testbed_->Environment().AppendToTestArtifact(
          "memory_usage.txt",
          absl::Substitute(
              "\n\n\n==================Test_run: $0==================\n\n\n",
              i)));
      EXPECT_OK(testbed_->Environment().AppendToTestArtifact("memory_usage.txt",
                                                             memory_usage));
    }

    VerifySflowResult(
        sflow_result, ingress_link.port_id,
        /*output_port=*/std::nullopt, kSourceMac.ToHexString(),
        kDstMac.ToHexString(), kEtherTypeIpv4, kIpv4Src.ToString(),
        GetDstIpv4AddrByPortId(ingress_link.port_id), pkt_size, sample_rate);

    // Verify sflowtool result. Since we use port id to generate packets, we use
    // port id to filter sFlow packets.
    const int sample_count =
        GetSflowSamplesOnSut(sflow_result, ingress_link.port_id);
    LOG(INFO) << "Test start to verify sflowtool result, sample_count: "
              << sample_count;
    const double expected_count =
        static_cast<double>(packets_num) / static_cast<double>(sample_rate);
    SflowResult result = SflowResult{
        .sut_interface = ingress_link.sut_interface,
        .packets = packets_num,
        .sampling_rate = sample_rate,
        .expected_samples = static_cast<int>(expected_count),
        .actual_samples = sample_count,
    };
    LOG(INFO) << "------ Test result ------\n" << result.DebugString();
    actual_result.push_back(sample_count);

    // TODO: tune the tolerance rate of sampling rate test
    // since sample count seems like to be more deviated when the sample rate
    // is high.
    EXPECT_GE(sample_count, expected_count * (1 - kTolerance))
        << "Not enough samples on " << ingress_link.sut_interface;
    EXPECT_LE(sample_count, expected_count * (1 + kTolerance));
  }
  LOG(INFO) << "Test overall result saved";
  EXPECT_OK(testbed_->Environment().StoreTestArtifact(
      absl::Substitute(
          "sflow_result_sampling_rate_$0_pkt_size_$1_result_samples.txt",
          sample_rate, pkt_size),
      absl::StrJoin(actual_result, "\n")));
}

// 1. Perform backoff on a switch.
// 2. Verify sFlow state.
// 3. Perform NSF reboot on a switch and wait for NSF reconciliation.
// 4. Verify sFlow state.
// 5. Send traffic to switch to trigger backoff.
// 6. Verify sFlow states.
TEST_P(BackoffTest, VerifyBackOffWorksAfterNsf) {

  if (!GetParam().nsf_enabled) {
    GTEST_SKIP() << "NSF is disabled, skip VerifyBackOffWorksAfterNsf test.";
  }

  ASSERT_GE(ready_links_.size(), 4)
      << "Needs four ready ixia links for testing";
  absl::flat_hash_map<std::string, bool> sflow_interfaces;
  ASSERT_OK_AND_ASSIGN(sflow_interfaces, GetSflowInterfacesFromSut(*testbed_));
  absl::flat_hash_set<std::string> sflow_enabled_interfaces;
  for (const auto& [name, enabled] : sflow_interfaces) {
    if (enabled) {
      sflow_enabled_interfaces.insert(name);
    }
  }

  {
    SCOPED_TRACE("Backoff test before NSF");
    ASSERT_NO_FATAL_FAILURE(PerformBackoffTest(
        testbed_.get(), gnmi_stub_.get(), ssh_client_,
        {ready_links_[2], ready_links_[3]}, gnmi_config_with_sflow_,
        sflow_enabled_interfaces, collector_port_, nos_param_));
  }
  absl::flat_hash_map<std::string, int> interfaces_to_sample_rate;
  ASSERT_OK_AND_ASSIGN(interfaces_to_sample_rate,
                       GetSflowActualSamplingRateForInterfaces(
                           gnmi_stub_.get(), sflow_enabled_interfaces));

  // Perform NSF reboot.
  {
    LOG(INFO) << "Perform NSF reboot.";
    // Finish P4 session before NSF.
    if (sut_p4_session_ != nullptr) {
      EXPECT_OK(sut_p4_session_->Finish());
      sut_p4_session_.reset(nullptr);
    }
    pins_test::ImageConfigParams image_config_params{
        .gnmi_config = gnmi_config_with_sflow_,
    };
    ASSERT_OK(pins_test::DoNsfRebootAndWaitForSwitchReadyOrRecover(
        testbed_.get(), *ssh_client_, &image_config_params));
    LOG(INFO) << "NSF reboot finished.";
  }

  ASSERT_OK(pins_test::WaitForCondition(
      CheckStateDbPortIndexTableExists, absl::Minutes(2), *ssh_client_,
      testbed_->Sut().ChassisName(), nos_param_.kRedisCliPath,
      std::vector<std::string>{sflow_enabled_interfaces.begin(),
                               sflow_enabled_interfaces.end()}));

  // Verify that sample rate on all interfaces remains the same after NSF.
  ASSERT_OK(IsExpectedSamplingRateFromGnmi(
      gnmi_stub_.get(), sflow_enabled_interfaces, interfaces_to_sample_rate,
      /*multiple=*/1));

  {
    SCOPED_TRACE("Backoff test after NSF");
    ASSERT_NO_FATAL_FAILURE(PerformBackoffTest(
        testbed_.get(), gnmi_stub_.get(), ssh_client_,
        {ready_links_[0], ready_links_[1]}, gnmi_config_with_sflow_,
        sflow_enabled_interfaces, collector_port_, nos_param_));
  }
}


void SflowNsfTestFixture::TearDown() {
  // Cold reboot and restore after NSF test.
  ASSERT_OK(pins_test::Reboot(::gnoi::system::RebootMethod::COLD,
                              testbed_->Sut(), testbed_->Environment()));
  ASSERT_OK(pins_test::WaitForReboot(testbed_.get(), *ssh_client_,
                                     /*check_interfaces_up=*/false));

  // Restore P4 session after cold reboot.
  ASSERT_OK_AND_ASSIGN(
      sut_p4_session_,
      pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
          testbed_->Sut(), gnmi_config_with_sflow_, GetP4Info()));

  SflowTestFixture::TearDown();
}
 
TEST_P(SflowNsfTestFixture, VerifySflowAfterFreezeAndUnfreeze) {

  if (!GetParam().nsf_enabled) {
    GTEST_SKIP()
<< "NSF is not enabled, skip VerifySflowAfterFreezeAndUnfreeze test.";
  }
  absl::flat_hash_map<std::string, bool> sflow_interfaces;
  ASSERT_OK_AND_ASSIGN(sflow_interfaces, GetSflowInterfacesFromSut(*testbed_));
  absl::flat_hash_set<std::string> sflow_enabled_interfaces;
  for (const auto& [name, enabled] : sflow_interfaces) {
    if (enabled) {
      sflow_enabled_interfaces.insert(name);
    }
  }
  ASSERT_OK_AND_ASSIGN(
      IxiaTrafficSettings ixia_traffic_settings,
      SetUpIxiaTrafficForSflowNsf({ready_links_[0], ready_links_[1]},
                                  sflow_enabled_interfaces, testbed_.get(),
                                  gnmi_stub_.get()));
  const int64_t pkt_count =
      ixia_traffic_settings.traffic_rate * kNsfTrafficTestDurationSecs;
  // The minimum percentage of samples that should be recorded during the test.
  // This is a loose threshold to account for the fact that the test might not
  // be able to record exactly the expected number of samples.
  constexpr double kMinExpectedSamplesPct = 0.7;
  const int64_t expected_number_of_samples =
      pkt_count / ixia_traffic_settings.sampling_rate;

  // Record initial Ixia counters to verify that traffic is only sent on the
  // first interface and that the expected number of packets are sent. This
  // logic has to be performed outside of
  // `GetSflowSamplesAfterSendingIxiaTraffic` since that function might be
  // called while the switch is frozen, and the gNMI interface would be
  // unavailable.
  ASSERT_OK_AND_ASSIGN(
      IxiaCounterStats ixia_counters_before_nsf,
      GetIxiaCounterStats(ready_links_, gnmi_stub_.get(),
                          /*pkt_count=*/pkt_count, nos_param_.kCpuQueueName));
  // More than 0 samples are recorded before NSF.
  EXPECT_THAT(
      GetSflowSamplesAfterSendingIxiaTraffic(
          testbed_.get(), ssh_client_, ready_links_[0], ixia_traffic_settings,
          collector_port_, nos_param_),
      IsOkAndHolds(Gt(expected_number_of_samples * kMinExpectedSamplesPct)));
  // Validate counters after sending Ixia traffic.
  EXPECT_OK(ValidateIxiaInterfaceCounters(ready_links_, gnmi_stub_.get(),
                                          ixia_counters_before_nsf));
  constexpr int kNumNsfReboots = 2;
  for (int i = 0; i < kNumNsfReboots; i++) {
    ASSERT_OK_AND_ASSIGN(
        IxiaCounterStats ixia_counters_during_nsf,
        GetIxiaCounterStats(ready_links_, gnmi_stub_.get(),
                            /*pkt_count=*/pkt_count, nos_param_.kCpuQueueName));
    // Freeze the switch.
    ASSERT_OK(ssh_client_
                  ->RunCommand(testbed_.get()->Sut().ChassisName(), kFreeze,
                               kCommandTimeout)
                  .status());
    absl::SleepFor(kFreezeTimeout);
    // Flow sampling is disabled (0 samples recorded) during NSF.
    EXPECT_THAT(GetSflowSamplesAfterSendingIxiaTraffic(
                    testbed_.get(), ssh_client_, ready_links_[0],
                    ixia_traffic_settings, collector_port_, nos_param_),
                IsOkAndHolds(Eq(0)));
    // Unfreeze the switch.
    ASSERT_OK(ssh_client_
                  ->RunCommand(testbed_.get()->Sut().ChassisName(), kUnfreeze,
                               kCommandTimeout)
                  .status());
    absl::SleepFor(kFreezeTimeout);
    EXPECT_OK(ValidateIxiaInterfaceCounters(ready_links_, gnmi_stub_.get(),
                                            ixia_counters_during_nsf));
    ASSERT_OK_AND_ASSIGN(
        IxiaCounterStats ixia_counters_after_nsf,
        GetIxiaCounterStats(ready_links_, gnmi_stub_.get(),
                            /*pkt_count=*/pkt_count, nos_param_.kCpuQueueName));
    // More than 0 samples are recorded after switch is unfrozen.
    EXPECT_THAT(
        GetSflowSamplesAfterSendingIxiaTraffic(
            testbed_.get(), ssh_client_, ready_links_[0], ixia_traffic_settings,
            collector_port_, nos_param_),
        IsOkAndHolds(Gt(expected_number_of_samples * kMinExpectedSamplesPct)));
    EXPECT_OK(ValidateIxiaInterfaceCounters(ready_links_, gnmi_stub_.get(),
                                            ixia_counters_after_nsf));
  }
}

namespace {

constexpr int kInbandSamplingRate = 256;
constexpr int kInbandTrafficPps = 1000;
constexpr auto kClusterMac =
    netaddr::MacAddress(0x0, 0x1a, 0x11, 0x17, 0x5f, 0x80);

// Sends `num_packets` packets at a rate of `traffic_speed`. The packet
// ipv4_destination field changes based on `port_id`.
absl::Status SendNPacketsFromSwitch(
    int num_packets, int traffic_speed, int port_id,
    absl::string_view interface, gnmi::gNMI::StubInterface* sut_gnmi_stub,
    const pdpi::IrP4Info& ir_p4info, pdpi::P4RuntimeSession& p4_session,
    thinkit::TestEnvironment& test_environment) {
  const absl::Time start_time = absl::Now();
  auto packet = gutil::ParseProtoOrDie<packetlib::Packet>(
      absl::Substitute(R"pb(
                         headers {
                           ethernet_header {
                             ethernet_destination: "$0"
                             ethernet_source: "$1"
                             ethertype: "0x0800"
                           }
                         }
                         headers {
                           ipv4_header {
                             version: "0x4"
                             ihl: "0x5"
                             dscp: "0x03"
                             ecn: "0x0"
                             identification: "0x0000"
                             flags: "0x0"
                             fragment_offset: "0x0000"
                             ttl: "0x20"
                             protocol: "0x05"
                             ipv4_source: "$2"
                             ipv4_destination: "$3"
                           }
                         }
                         payload: "Test packet for Sflow Inband testing")pb",
                       kDstMac.ToString(), kSourceMac.ToString(),
                       kIpv4Src.ToString(), GetDstIpv4AddrByPortId(port_id)));
  ASSIGN_OR_RETURN(auto initial_in_counter,
                   ReadCounters(std::string(interface), sut_gnmi_stub));
  ASSIGN_OR_RETURN(std::string raw_packet, SerializePacket(packet));
  for (int i = 0; i < num_packets; i++) {
    // Rate limit to traffic_speed packets per second.
    RETURN_IF_ERROR(InjectEgressPacket(
        absl::StrCat(port_id), raw_packet, ir_p4info, &p4_session,
        /*packet_delay=*/absl::Milliseconds(1000 / traffic_speed)));
  }
  ASSIGN_OR_RETURN(auto final_in_counter,
                   ReadCounters(std::string(interface), sut_gnmi_stub));
  auto delta = DeltaCounters(initial_in_counter, final_in_counter);
  LOG(INFO) << "Ingress Deltas (" << interface << "):\n";
  ShowCounters(delta);
  // There might be some bearable drop.
  EXPECT_GE(delta.in_pkts, (double)0.75 * num_packets)
      << "Sent " << num_packets
      << " on interface: " << interface << " port_id: " << port_id
      << ". Received: " << delta.in_pkts;
  LOG(INFO) << "Sent " << num_packets << " packets in "
            << (absl::Now() - start_time) << " for port: " << port_id << "."
            << " Interface: " << interface << ". Packets dst ip: "
            << GetDstIpv4AddrByPortId(port_id);
  return absl::OkStatus();
}

// Sends packets at a rate of `traffic_speed` until `notification` has been
// notified. The packet ipv4_destination field changes based on `port_id`.
absl::Status SendPacketsFromSwitchUntilNotificationReceived(
    const absl::Notification& notification, int traffic_speed, int port_id,
    absl::string_view interface, gnmi::gNMI::StubInterface* sut_gnmi_stub,
    const pdpi::IrP4Info& ir_p4info, pdpi::P4RuntimeSession& p4_session,
    thinkit::TestEnvironment& test_environment) {
  const absl::Time start_time = absl::Now();
  auto packet = gutil::ParseProtoOrDie<packetlib::Packet>(
      absl::Substitute(R"pb(
                         headers {
                           ethernet_header {
                             ethernet_destination: "$0"
                             ethernet_source: "$1"
                             ethertype: "0x0800"
                           }
                         }
                         headers {
                           ipv4_header {
                             version: "0x4"
                             ihl: "0x5"
                             dscp: "0x03"
                             ecn: "0x0"
                             identification: "0x0000"
                             flags: "0x0"
                             fragment_offset: "0x0000"
                             ttl: "0x20"
                             protocol: "0x05"
                             ipv4_source: "$2"
                             ipv4_destination: "$3"
                           }
                         }
                         payload: "Test packet for Sflow Inband testing")pb",
                       kDstMac.ToString(), kSourceMac.ToString(),
                       kIpv4Src.ToString(), GetDstIpv4AddrByPortId(port_id)));
  ASSIGN_OR_RETURN(auto initial_in_counter,
                   ReadCounters(std::string(interface), sut_gnmi_stub));
  ASSIGN_OR_RETURN(std::string raw_packet, SerializePacket(packet));
  int num_packets = 0;
  while (!notification.HasBeenNotified()) {
    num_packets++;
    // Rate limit to traffic_speed packets per second.
    RETURN_IF_ERROR(InjectEgressPacket(
        absl::StrCat(port_id), raw_packet, ir_p4info, &p4_session,
        /*packet_delay=*/absl::Milliseconds(1000 / traffic_speed)));
  }
  ASSIGN_OR_RETURN(auto final_in_counter,
                   ReadCounters(std::string(interface), sut_gnmi_stub));
  auto delta = DeltaCounters(initial_in_counter, final_in_counter);
  LOG(INFO) << "Ingress Deltas (" << interface << "):\n";
  ShowCounters(delta);
  // There might be some bearable drop.
  EXPECT_GE(delta.in_pkts, (double)0.85 * num_packets)
      << "Sent " << num_packets
      << " on interface: " << interface << " port_id: " << port_id
      << ". Received: " << delta.in_pkts;
  LOG(INFO) << "Sent " << num_packets << " packets in "
            << (absl::Now() - start_time) << " for port: " << port_id << "."
            << " Interface: " << interface << ". Packets dst ip: "
            << GetDstIpv4AddrByPortId(port_id);
  return absl::OkStatus();
}

// Sets VRF id for all packets.
absl::Status SetSwitchVrfForAllPackets(pdpi::P4RuntimeSession& p4_session,
                                       const pdpi::IrP4Info& ir_p4info,
                                       absl::string_view vrf_id) {
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
                         vrf_id))));
  RETURN_IF_ERROR(pdpi::InstallPiTableEntry(&p4_session, pi_entry));

  ASSIGN_OR_RETURN(
      pi_entry,
      pdpi::PartialPdTableEntryToPiTableEntry(
          ir_p4info, gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
                         R"pb(
                           acl_pre_ingress_table_entry {
                             match {}  # Wildcard match
                             action { set_vrf { vrf_id: "$0" } }
                             priority: 1
                           })pb",
                         vrf_id))));
  return pdpi::InstallPiTableEntry(&p4_session, pi_entry);
}

// Programs ipv6_table_entry using `vrf_id`, `ip_address` and `next_hop_id`.
absl::Status ProgramRoutesForIpv6(pdpi::P4RuntimeSession& p4_session,
                                  const pdpi::IrP4Info& ir_p4info,
                                  absl::string_view vrf_id,
                                  absl::string_view ip_address,
                                  absl::string_view next_hop_id) {
  auto ipv4_entry = gutil::ParseProtoOrDie<sai::Update>(absl::Substitute(
      R"pb(
        type: INSERT
        table_entry {
          ipv6_table_entry {
            match {
              vrf_id: "$0"
              ipv6_dst { value: "$1" prefix_length: 128 }
            }
            action { set_nexthop_id { nexthop_id: "$2" } }
          }
        })pb",
      vrf_id, ip_address, next_hop_id));
  p4::v1::WriteRequest write_request;
  ASSIGN_OR_RETURN(
      p4::v1::Update pi_entry, pdpi::PdUpdateToPi(ir_p4info, ipv4_entry),
      _.SetPrepend() << "Failed in PD table conversion to PI, entry: "
                     << ipv4_entry.DebugString() << " error: ");
  *write_request.add_updates() = pi_entry;
  return pdpi::SetMetadataAndSendPiWriteRequest(&p4_session, write_request);
}

// Programs a next hop entry for `port_id` and returns nexthop id if successful.
absl::StatusOr<std::string> ProgramNextHops(pdpi::P4RuntimeSession& p4_session,
                                            const pdpi::IrP4Info& ir_p4info,
                                            absl::string_view port_id) {
  p4::v1::WriteRequest pi_request;
  const std::string rif_id = absl::StrCat("rif-", port_id);
  const std::string neighbor_id = "fe80::2";
  const std::string src_mac = "00:02:03:04:05:06";
  ASSIGN_OR_RETURN(*pi_request.add_updates(),
                   RouterInterfaceTableUpdate(ir_p4info, p4::v1::Update::INSERT,
                                              rif_id, port_id, src_mac));
  ASSIGN_OR_RETURN(
      *pi_request.add_updates(),
      NeighborTableUpdate(ir_p4info, p4::v1::Update::INSERT, rif_id,
                          neighbor_id, kClusterMac.ToString()));
  const std::string nexthop_id = absl::StrCat("nexthop-", port_id);
  ASSIGN_OR_RETURN(*pi_request.add_updates(),
                   NexthopTableUpdate(ir_p4info, p4::v1::Update::INSERT,
                                      nexthop_id, rif_id, neighbor_id));
  RETURN_IF_ERROR(
      pdpi::SetMetadataAndSendPiWriteRequest(&p4_session, pi_request));
  return nexthop_id;
}

constexpr int kIpProtocolTcp = 6;

// Sends `num_packets` SSH packets via `port` at `traffic_speed` rate.
absl::Status SendNSshPacketsFromSwitch(
    int num_packets, int traffic_speed, Port port, absl::string_view src_ip,
    absl::string_view dst_ip, gnmi::gNMI::StubInterface* sut_gnmi_stub,
    const pdpi::IrP4Info& ir_p4info, pdpi::P4RuntimeSession& p4_session,
    thinkit::TestEnvironment& test_environment) {
  auto packet = gutil::ParseProtoOrDie<packetlib::Packet>(absl::Substitute(
      R"pb(
        headers {
          ethernet_header {
            ethernet_destination: "$0"
            ethernet_source: "$1"
            ethertype: "0x86dd"
          }
        }
        headers {
          ipv6_header {
            dscp: "$2"
            ecn: "0x0"
            flow_label: "0x00000"
            next_header: "$3"
            hop_limit: "0x40"
            ipv6_source: "$4"
            ipv6_destination: "$5"
          }
        }
        headers {
          tcp_header {
            source_port: "$6"
            destination_port: "$7"
            sequence_number: "0x00000001"
            acknowledgement_number: "0x00000000"
            rest_of_header: "0x002200000000000"
          }
        }
        payload: "SSH packet without computed fields"
      )pb",
      kClusterMac.ToString(), kSourceMac.ToString(), packetlib::IpDscp(0),
      packetlib::IpProtocol(kIpProtocolTcp), src_ip, dst_ip,
      packetlib::TcpPort(2000), packetlib::TcpPort(22)));
  const absl::Time start_time = absl::Now();
  ASSIGN_OR_RETURN(std::string raw_packet, SerializePacket(packet));
  ASSIGN_OR_RETURN(
      auto initial_in_counter,
      ReadCounters(std::string(port.interface_name), sut_gnmi_stub));
  for (int i = 0; i < num_packets; i++) {
    // Rate limit to traffic_speed packets per second.
    RETURN_IF_ERROR(InjectEgressPacket(
        absl::StrCat(port.port_id), raw_packet, ir_p4info, &p4_session,
        /*packet_delay=*/absl::Milliseconds(1000 / traffic_speed)));
  }
  ASSIGN_OR_RETURN(
      auto final_in_counter,
      ReadCounters(std::string(port.interface_name), sut_gnmi_stub));
  auto delta = DeltaCounters(initial_in_counter, final_in_counter);
  LOG(INFO) << "Ingress Deltas (" << port.interface_name << "):\n";
  ShowCounters(delta);
  // There might be some bearable drop.
  EXPECT_GE(delta.in_pkts, (double)0.85 * num_packets)
      << "Sent " << num_packets << " on interface: " << port.interface_name
      << " port_id: " << port.port_id << ". Received: " << delta.in_pkts;

  LOG(INFO) << "Sent " << num_packets << " SSH packets in "
            << (absl::Now() - start_time)
            << " for interface: " << port.interface_name << "."
            << " port id: " << port.port_id << ". ";
  return absl::OkStatus();
}

// Returns true iff `sflowtool_output` has `ip_protocol` output. sFlow sample
// uses decimal for ip protocol.
bool HasSampleForProtocol(absl::string_view sflowtool_output, int ip_protocol) {
  constexpr int kFieldSize = 20;
  constexpr int kIpProtocolIdx = 11;
  // Each line indicates one sFlow sample.
  for (absl::string_view sflow_sample :
       absl::StrSplit(sflowtool_output, '\n')) {
    // Split by column.
    std::vector<absl::string_view> fields = absl::StrSplit(sflow_sample, ',');
    if (fields.size() < kFieldSize) {
      continue;
    }
    // Filter ip protocol. sFlow sample uses decimal.
    if (fields[kIpProtocolIdx] == absl::StrCat(ip_protocol)) {
      return true;
    }
  }
  return false;
}

absl::Status SetupAndVerifySamplingEnabledOnUpPorts(
    thinkit::MirrorTestbed& testbed, thinkit::Switch& sut,
    gnmi::gNMI::StubInterface* sut_gnmi_stub,
    const std::string& sut_gnmi_config, const std::string& agent_address,
    const std::vector<std::pair<std::string, int>>& collector_address_and_port,
    const absl::flat_hash_map<std::string, bool>& sflow_enabled_interfaces,
    const std::string& artifacts_prefix) {
  ASSIGN_OR_RETURN(
      auto sut_gnmi_config_with_sflow,
      UpdateSflowConfig(sut_gnmi_config, agent_address,
                        collector_address_and_port, sflow_enabled_interfaces,
                        kInbandSamplingRate, kSampleHeaderSize));
  EXPECT_OK(testbed.Environment().StoreTestArtifact(
      absl::StrCat(artifacts_prefix, "_gnmi_config_with_sflow.txt"),
      json_yang::FormatJsonBestEffort(sut_gnmi_config_with_sflow)));
  RETURN_IF_ERROR(pins_test::PushGnmiConfig(sut, sut_gnmi_config_with_sflow));
  // Wait until all sFLow gNMI states are converged.
  return pins_test::WaitForCondition(
      VerifySflowStatesConverged, absl::Seconds(30), sut_gnmi_stub,
      agent_address, kInbandSamplingRate, kSampleHeaderSize,
      collector_address_and_port, sflow_enabled_interfaces);
}

absl::Status SetUpMirrorTestbedWithSflowEnabledOnUpPorts(
    thinkit::MirrorTestbed& testbed, gnmi::gNMI::StubInterface* sut_gnmi_stub,
    gnmi::gNMI::StubInterface* control_gnmi_stub,
    const std::string& sut_gnmi_config, const std::string& sut_agent_address,
    const std::string& control_gnmi_config,
    const std::string& control_agent_address) {
  std::vector<std::pair<std::string, int>> collector_address_and_port{
      {kLocalLoopbackIpv6, pins::kSflowStandaloneCollectorPort}};
  ASSIGN_OR_RETURN(auto port_id_per_port_name,
                   pins_test::GetAllUpInterfacePortIdsByName(*sut_gnmi_stub));
  if (port_id_per_port_name.empty()) {
    return absl::FailedPreconditionError("No up interfaces.");
  }
  absl::flat_hash_map<std::string, bool> sflow_enabled_interfaces;
  for (const auto& [port_name, port_id] : port_id_per_port_name) {
    sflow_enabled_interfaces[port_name] = true;
    EXPECT_OK(testbed.Environment().AppendToTestArtifact(
        "sut_port_id_per_port_name_before_breakout.txt",
        absl::Substitute("port_name=$0, port_id=$1\n", port_name, port_id)));
  }
  RETURN_IF_ERROR(SetupAndVerifySamplingEnabledOnUpPorts(
      testbed, testbed.Sut(), sut_gnmi_stub, sut_gnmi_config, sut_agent_address,
      collector_address_and_port, sflow_enabled_interfaces,
      /*artifacts_prefix=*/"sut"));

  ASSIGN_OR_RETURN(
      port_id_per_port_name,
      pins_test::GetAllUpInterfacePortIdsByName(*control_gnmi_stub));
  if (port_id_per_port_name.empty()) {
    return absl::FailedPreconditionError("No up interfaces.");
  }
  absl::flat_hash_map<std::string, bool> control_sflow_enabled_interfaces;
  for (const auto& [port_name, port_id] : port_id_per_port_name) {
    control_sflow_enabled_interfaces[port_name] = true;
    EXPECT_OK(testbed.Environment().AppendToTestArtifact(
        "control_port_id_per_port_name_before_breakout.txt",
        absl::Substitute("port_name=$0, port_id=$1\n", port_name, port_id)));
  }

  RETURN_IF_ERROR(SetupAndVerifySamplingEnabledOnUpPorts(
      testbed, testbed.ControlSwitch(), control_gnmi_stub, control_gnmi_config,
      control_agent_address, collector_address_and_port,
      control_sflow_enabled_interfaces,
      /*artifacts_prefix=*/"control"));

  return absl::OkStatus();
}

}  // namespace

void SflowMirrorTestFixture::SetUp() {
  ASSERT_NE(GetParam().ssh_client, nullptr);
  GetParam().testbed_interface->SetUp();
  thinkit::MirrorTestbed& testbed =
      GetParam().testbed_interface->GetMirrorTestbed();

  nos_param_ = GetParam().nos_is_sonic ? nos_param_sonic : GetParam().nos_param;

  // Push gNMI config to SUT switch.
  const std::string& sut_gnmi_config = GetParam().sut_gnmi_config;
  ASSERT_OK(testbed.Environment().StoreTestArtifact("sut_gnmi_config.txt",
                                                    sut_gnmi_config));
  
  collector_port_ = GetSflowCollectorPort();
  ASSERT_OK_AND_ASSIGN(
      sut_p4_session_,
      pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
          testbed.Sut(), sut_gnmi_config, /*p4info=*/std::nullopt));
  ASSERT_OK_AND_ASSIGN(
      sut_p4_info_,
      pdpi::GetOrSetP4Info(*sut_p4_session_, GetParam().sut_p4_info));
  ASSERT_OK_AND_ASSIGN(sut_ir_p4_info_, pdpi::GetIrP4Info(*sut_p4_session_));
  
  ASSERT_OK(GetParam().ssh_client->RunCommand(
      testbed.Sut().ChassisName(),
      /*command=*/
      nos_param_.kRedisExecPrefix +
          "redis-cli -n 14 hset \"PORT_TABLE:CPU\" \"NULL\" \"NULL\"",
      absl::Seconds(20)));
  ASSERT_OK(GetParam().ssh_client->RunCommand(
      testbed.ControlSwitch().ChassisName(),
      /*command=*/
      nos_param_.kRedisExecPrefix +
          "redis-cli -n 14 hset \"PORT_TABLE:CPU\" \"NULL\" \"NULL\"",
      absl::Seconds(20)));

  // Push gNMI config to control switch.
  const std::string& control_gnmi_config = GetParam().control_gnmi_config;
  ASSERT_OK(testbed.Environment().StoreTestArtifact("control_gnmi_config.txt",
                                                    control_gnmi_config));
  ASSERT_OK_AND_ASSIGN(control_p4_session_,
                       pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
                           testbed.ControlSwitch(), control_gnmi_config,
                           /*p4info=*/std::nullopt));
  ASSERT_OK_AND_ASSIGN(
      control_p4_info_,
      pdpi::GetOrSetP4Info(*control_p4_session_, GetParam().control_p4_info));
  ASSERT_OK_AND_ASSIGN(control_ir_p4_info_,
                       pdpi::GetIrP4Info(*control_p4_session_));

  ASSERT_OK_AND_ASSIGN(control_gnmi_stub_,
                       testbed.ControlSwitch().CreateGnmiStub());

  // Create GNMI stub for admin operations.
  ASSERT_OK_AND_ASSIGN(sut_gnmi_stub_, testbed.Sut().CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(
      auto port_id_per_port_name,
      pins_test::GetAllUpInterfacePortIdsByName(*sut_gnmi_stub_));
  ASSERT_GE(port_id_per_port_name.size(), 2);

  ASSERT_OK_AND_ASSIGN(
      auto sut_loopback0_ipv6s,
      pins_test::ParseLoopbackIpv6s(GetParam().sut_gnmi_config));
  ASSERT_GT(sut_loopback0_ipv6s.size(), 0) << absl::Substitute(
      "No loopback IP found for $0 testbed.", testbed.Sut().ChassisName());
  agent_address_ = sut_loopback0_ipv6s[0].ToString();

  CollectSflowDebugs(GetParam().ssh_client, testbed.Sut().ChassisName(),
                     /*prefix=*/"pretest_", testbed.Environment(), nos_param_);
}

void SflowMirrorTestFixture::TearDown() {
  auto& testbed = GetParam().testbed_interface->GetMirrorTestbed();
  CollectSflowDebugs(GetParam().ssh_client, testbed.Sut().ChassisName(),
                     /*prefix=*/"posttest_", testbed.Environment(), nos_param_);
  if (sut_p4_session_ != nullptr) {
    EXPECT_OK(pdpi::ClearTableEntries(sut_p4_session_.get()));
    EXPECT_OK(sut_p4_session_->Finish());
  }
  if (control_p4_session_ != nullptr) {
    EXPECT_OK(pdpi::ClearTableEntries(control_p4_session_.get()));
    EXPECT_OK(control_p4_session_->Finish());
  }
  ASSERT_OK_AND_ASSIGN(control_p4_session_,
                       pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
                           testbed.ControlSwitch(),
                           GetParam().control_gnmi_config, GetControlP4Info()));
  GetParam().testbed_interface->TearDown();
}

absl::Status SflowMirrorTestFixture::NsfRebootAndWaitForConvergence(
    thinkit::MirrorTestbed& testbed, absl::string_view gnmi_config) {
  CollectSflowDebugs(GetParam().ssh_client, testbed.Sut().ChassisName(),
                     /*prefix=*/"pre_nsf_", testbed.Environment(), nos_param_);
  LOG(INFO) << "Start NSF reboot on switch";
  ASSIGN_OR_RETURN(::p4::v1::ReadResponse p4flow_snapshot_before_nsf,
                   pins_test::TakeP4FlowSnapshot(testbed.Sut()));
  pins_test::ImageConfigParams image_config_params{
      .gnmi_config = std::string(gnmi_config),
  };
  RETURN_IF_ERROR(pins_test::DoNsfRebootAndWaitForSwitchReadyOrRecover(
      &testbed, *GetParam().ssh_client, &image_config_params));
  CollectSflowDebugs(GetParam().ssh_client, testbed.Sut().ChassisName(),
                     /*prefix=*/"post_nsf_", testbed.Environment(), nos_param_);
  ASSIGN_OR_RETURN(::p4::v1::ReadResponse p4flow_snapshot_after_nsf,
                   pins_test::TakeP4FlowSnapshot(testbed.Sut()));
  RETURN_IF_ERROR(pins_test::CompareP4FlowSnapshots(p4flow_snapshot_before_nsf,
                                                    p4flow_snapshot_after_nsf));
  LOG(INFO) << "NSF reboot finished and switch is converged.";
  return absl::OkStatus();
}

// Push config with collector controller_IP:portA to switch.
// Perform NSF reboot on switch.
// Push config with collector localhost:portB to switch.
// Start collector at localhost:portB.
// Start traffic and verify.
TEST_P(SflowRebootTestFixture, ChangeCollectorConfigOnNsfReboot) {
  thinkit::MirrorTestbed& testbed =
      GetParam().testbed_interface->GetMirrorTestbed();
  if (!GetParam().nsf_enabled) {
    GTEST_SKIP()
        << "Skip TestNsfUpgradeGnpsiCollector since NSF is not enabled.";
  }
  // Configure SUT with control switch loopback0 ip as collector.
  ASSERT_OK_AND_ASSIGN(
      auto control_loopback0_ipv6s,
      pins_test::ParseLoopbackIpv6s(GetParam().control_gnmi_config));
  ASSERT_GT(control_loopback0_ipv6s.size(), 0)
      << absl::Substitute("No loopback IP found for $0 testbed.",
                          testbed.ControlSwitch().ChassisName());
  const std::string collector_ipv6 = control_loopback0_ipv6s[0].ToString();
  ASSERT_NE(collector_ipv6, agent_address_);

  std::vector<std::pair<std::string, int>> collector_address_and_port;
  collector_address_and_port.push_back({collector_ipv6, collector_port_});
  ASSERT_OK_AND_ASSIGN(Port traffic_port,
                       GetUnusedUpPort(*sut_gnmi_stub_, /*used_port=*/""));

  ASSERT_OK_AND_ASSIGN(
      auto port_id_per_port_name,
      pins_test::GetAllUpInterfacePortIdsByName(*sut_gnmi_stub_));

  absl::flat_hash_map<std::string, bool> sflow_enabled_interfaces;
  for (const auto& [interface_name, unused] : port_id_per_port_name) {
    sflow_enabled_interfaces[interface_name] = true;
  }
  ASSERT_OK_AND_ASSIGN(
      auto sut_gnmi_config_with_sflow,
      UpdateSflowConfig(GetParam().sut_gnmi_config, agent_address_,
                        collector_address_and_port, sflow_enabled_interfaces,
                        kInbandSamplingRate, kSampleHeaderSize));
  ASSERT_OK(testbed.Environment().StoreTestArtifact(
      "sut_gnmi_config_with_sflow_before_nsf.txt",
      json_yang::FormatJsonBestEffort(sut_gnmi_config_with_sflow)));
  ASSERT_OK(
      pins_test::PushGnmiConfig(testbed.Sut(), sut_gnmi_config_with_sflow));
  // Wait until all sFLow gNMI states are converged.
  ASSERT_OK(pins_test::WaitForCondition(
      VerifySflowStatesConverged, absl::Seconds(30), sut_gnmi_stub_.get(),
      agent_address_, kInbandSamplingRate, kSampleHeaderSize,
      collector_address_and_port, sflow_enabled_interfaces));

  ASSERT_OK_AND_ASSIGN(
      Port inband_port,
      GetUnusedUpPort(*sut_gnmi_stub_, traffic_port.interface_name));

  // Program rules to forward sample pkts to control switch loopback0 IPv6
  // address.
  // 1. Set a default vrf for all packets
  // 2. Install a route entry matching on the default vrf and route prefix of
  // the control switch loopback0 ipv6.
  // 3. Define the nexthop and dependent objects for the route entry action.
  const std::string vrf_id = "vrf-50";
  ASSERT_OK(
      SetSwitchVrfForAllPackets(*sut_p4_session_, GetSutIrP4Info(), vrf_id));

  ASSERT_OK_AND_ASSIGN(std::string next_hop_id,
                       ProgramNextHops(*sut_p4_session_, GetSutIrP4Info(),
                                       absl::StrCat(inband_port.port_id)));
  ASSERT_OK(ProgramRoutesForIpv6(*sut_p4_session_, GetSutIrP4Info(), vrf_id,
                                 collector_ipv6, next_hop_id));

  ASSERT_OK(
      NsfRebootAndWaitForConvergence(testbed, sut_gnmi_config_with_sflow));
  // Wait until all sFlow gNMI states are converged.
  ASSERT_OK(pins_test::WaitForCondition(
      VerifySflowStatesConverged, absl::Seconds(60), sut_gnmi_stub_.get(),
      agent_address_, kInbandSamplingRate, kSampleHeaderSize,
      collector_address_and_port, sflow_enabled_interfaces));
  std::vector<std::string> interface_names;
  for (const auto& [interface_name, _] : sflow_enabled_interfaces) {
    interface_names.push_back(interface_name);
  }
  ASSERT_OK(pins_test::WaitForCondition(
      CheckStateDbPortIndexTableExists, absl::Minutes(2),
      *GetParam().ssh_client, testbed.Sut().ChassisName(),
      nos_param_.kRedisCliPath, interface_names));
  ASSERT_OK(pins_test::WaitForCondition(pins_test::PortsUp, absl::Minutes(3),
                                        testbed.Sut(), interface_names,
                                        /*with_healthz=*/false));
  LOG(INFO) << "Sflow states are converged after NSF reboot.";

  // Sends traffic.
  ASSERT_OK_AND_ASSIGN(
      auto control_switch_port_id_per_port_name,
      pins_test::GetAllUpInterfacePortIdsByName(*control_gnmi_stub_));
  ASSERT_OK_AND_ASSIGN(
      int control_switch_port_id,
      GetPortIdFromInterfaceName(control_switch_port_id_per_port_name,
                                 traffic_port.interface_name));
  absl::Notification notification;
  std::thread traffic_thread = std::thread(
      [this, control_switch_port_id, traffic_port, &notification, &testbed] {
        LOG(INFO) << "Start sending packets from control switch after NSF.";
        ASSERT_OK(SendPacketsFromSwitchUntilNotificationReceived(
            notification, kInbandTrafficPps, control_switch_port_id,
            traffic_port.interface_name, sut_gnmi_stub_.get(),
            GetControlIrP4Info(), *control_p4_session_, testbed.Environment()));
        LOG(INFO) << "Finished sending packets from control switch after NSF.";
      });
  absl::Cleanup clean_up([&traffic_thread, &notification] {
    if (traffic_thread.joinable()) {
      notification.Notify();
      traffic_thread.join();
    }
  });

  // Push config with both control switch loopback0 IP and local loopback IP
  // collector.
  collector_address_and_port.push_back({kLocalLoopbackIpv6, collector_port_});
  ASSERT_OK_AND_ASSIGN(
      sut_gnmi_config_with_sflow,
      UpdateSflowConfig(GetParam().sut_gnmi_config, agent_address_,
                        collector_address_and_port, sflow_enabled_interfaces,
                        kInbandSamplingRate, kSampleHeaderSize));
  ASSERT_OK(testbed.Environment().StoreTestArtifact(
      "sut_gnmi_config_with_sflow_after_nsf.txt",
      json_yang::FormatJsonBestEffort(sut_gnmi_config_with_sflow)));
  ASSERT_OK(
      pins_test::PushGnmiConfig(testbed.Sut(), sut_gnmi_config_with_sflow));

  // Wait until all sFLow gNMI states are converged.
  ASSERT_OK(pins_test::WaitForCondition(
      VerifySflowStatesConverged, absl::Seconds(30), sut_gnmi_stub_.get(),
      agent_address_, kInbandSamplingRate, kSampleHeaderSize,
      collector_address_and_port, sflow_enabled_interfaces));

  // 1. Start sflowtool on control switch.
  // 2. Start sflowtool on SUT switch.
  // 3. Get sflowtool result and counters stats.
  std::string control_sflow_result, sut_sflow_result;
  {
    absl::Time start_time = absl::Now();
    ASSERT_OK_AND_ASSIGN(
        std::thread control_sflowtool_thread,
        RunSflowCollectorForNSecs(
            *GetParam().ssh_client, testbed.ControlSwitch().ChassisName(),
            SflowContainerExecCmdStr(nos_param_, kSflowtoolLineFormatTemplate),
            collector_port_,
            /*sflowtool_runtime=*/30, control_sflow_result));
    ASSERT_OK_AND_ASSIGN(
        std::thread sut_sflowtool_thread,
        RunSflowCollectorForNSecs(
            *GetParam().ssh_client, testbed.Sut().ChassisName(),
            SflowContainerExecCmdStr(nos_param_, kSflowtoolLineFormatTemplate),
            collector_port_,
            /*sflowtool_runtime=*/30, sut_sflow_result));
    ASSERT_OK_AND_ASSIGN(
        std::string sflow_queue_name,
        GetSflowQueueName(sut_gnmi_stub_.get(), nos_param_.kCpuQueueName));
    ASSERT_OK_AND_ASSIGN(auto initial_queue_counter,
                         pins_test::GetGnmiQueueCounters(
                             "CPU", sflow_queue_name, *sut_gnmi_stub_));
    ASSERT_OK_AND_ASSIGN(
        auto sut_initial_in_band_port_counter,
        ReadCounters(inband_port.interface_name, sut_gnmi_stub_.get()));

    ASSERT_OK_AND_ASSIGN(
        auto control_initial_in_band_port_counter,
        ReadCounters(inband_port.interface_name, control_gnmi_stub_.get()));
    ASSERT_OK_AND_ASSIGN(auto control_initial_cpu_counter,
                         ReadCounters("CPU", control_gnmi_stub_.get()));

    // Wait for sflowtool to finish and read counter data.
    absl::Cleanup clean_up([this, initial_queue_counter, start_time,
                            control_gnmi_stub_raw = control_gnmi_stub_.get(),
                            &notification, &sut_initial_in_band_port_counter,
                            &control_initial_in_band_port_counter,
                            &control_initial_cpu_counter, &inband_port,
                            &control_sflowtool_thread, &sut_sflowtool_thread,
                            &traffic_thread, &sflow_queue_name] {
      if (control_sflowtool_thread.joinable()) {
        control_sflowtool_thread.join();
      }
      if (sut_sflowtool_thread.joinable()) {
        sut_sflowtool_thread.join();
      }
      if (traffic_thread.joinable()) {
        notification.Notify();
        traffic_thread.join();
      }

      // Show counter data after sflowtool is finished. Put this inside clean up
      // so that we can get the accurate data.
      ASSERT_OK_AND_ASSIGN(
          auto final_queue_counter,
          pins_test::GetGnmiQueueCounters("CPU", sflow_queue_name,
                                          *(this->sut_gnmi_stub_)));
      LOG(INFO) << "CPU " << sflow_queue_name << " queue counter delta:\n"
                << (final_queue_counter - initial_queue_counter)
                << " \n total time: " << (absl::Now() - start_time);

      ASSERT_OK_AND_ASSIGN(
          auto sut_final_in_band_port_counter,
          ReadCounters(inband_port.interface_name, sut_gnmi_stub_.get()));
      LOG(INFO) << " SUT inband port " << inband_port.interface_name
                << " counter delta in total time: "
                << (absl::Now() - start_time);
      ShowCounters(DeltaCounters(sut_initial_in_band_port_counter,
                                 sut_final_in_band_port_counter));

      ASSERT_OK_AND_ASSIGN(
          auto control_final_in_band_port_counter,
          ReadCounters(inband_port.interface_name, control_gnmi_stub_.get()));
      LOG(INFO) << " Control switch inband port " << inband_port.interface_name
                << " counter delta in total time: "
                << (absl::Now() - start_time);
      ShowCounters(DeltaCounters(control_initial_in_band_port_counter,
                                 control_final_in_band_port_counter));

      ASSERT_OK_AND_ASSIGN(auto control_final_cpu_counter,
                           ReadCounters("CPU", control_gnmi_stub_.get()));
      LOG(INFO) << " Control switch CPU counter delta in total time: "
                << (absl::Now() - start_time);
      ShowCounters(DeltaCounters(control_initial_cpu_counter,
                                 control_final_cpu_counter));
    });
  }

  EXPECT_OK(testbed.Environment().StoreTestArtifact("control_sflow_result.txt",
                                                    control_sflow_result));
  EXPECT_OK(testbed.Environment().StoreTestArtifact("sut_sflow_result.txt",
                                                    sut_sflow_result));

  EXPECT_FALSE(control_sflow_result.empty())
      << "No samples on " << traffic_port.interface_name;
  const int control_sflow_samples =
      GetSflowSamplesOnSut(control_sflow_result, control_switch_port_id);
  const int sut_sflow_samples =
      GetSflowSamplesOnSut(sut_sflow_result, control_switch_port_id);
  EXPECT_GT(control_sflow_samples, 0);
  EXPECT_GT(sut_sflow_samples, 0);
}

// 1. Pick an interface and let control switch send some traffic via this
// interface.
// 2. Set rules on SUT switch to forward sample to control switch.
// 3. Verifies on control switch that samples are generated.
// |-----------| Traffic  | --------- |
// | control   | -------> |    SUT    |
// |-----------| Inband   | --------  |
// | control   | <------- |    SUT    |

TEST_P(SflowMirrorTestFixture, TestInbandPathToSflowCollector) {
  if (!GetParam().run_all_tests) {
    GTEST_SKIP() << "Skip the test on new platform, to be run later";
  }
  thinkit::MirrorTestbed& testbed =
      GetParam().testbed_interface->GetMirrorTestbed();

  const int packets_num = 10000;

  // Find the loopback0 address for CS.
  ASSERT_OK_AND_ASSIGN(
      auto control_loopback0_ipv6s,
      pins_test::ParseLoopbackIpv6s(GetParam().control_gnmi_config));
  ASSERT_GT(control_loopback0_ipv6s.size(), 0)
      << absl::Substitute("No loopback IP found for $0 testbed.",
                          testbed.ControlSwitch().ChassisName());
  const std::string collector_ipv6 = control_loopback0_ipv6s[0].ToString();
  ASSERT_NE(collector_ipv6, agent_address_);

  std::vector<std::pair<std::string, int>> collector_address_and_port;

  // Use main switch Loopback0 Ip address as collector.
  collector_address_and_port.push_back({collector_ipv6, collector_port_});
  collector_address_and_port.push_back({kLocalLoopbackIpv6, collector_port_});

  ASSERT_OK_AND_ASSIGN(Port traffic_port,
                       GetUnusedUpPort(*sut_gnmi_stub_, /*used_port=*/""));

  absl::flat_hash_map<std::string, bool> sflow_enabled_interfaces{
      {traffic_port.interface_name, true}};
  ASSERT_OK_AND_ASSIGN(
      auto sut_gnmi_config_with_sflow,
      UpdateSflowConfig(GetParam().sut_gnmi_config, agent_address_,
                        collector_address_and_port, sflow_enabled_interfaces,
                        kInbandSamplingRate, kSampleHeaderSize));
  ASSERT_OK(testbed.Environment().StoreTestArtifact(
      "sut_gnmi_config_with_sflow.txt",
      json_yang::FormatJsonBestEffort(sut_gnmi_config_with_sflow)));
  ASSERT_OK(
      pins_test::PushGnmiConfig(testbed.Sut(), sut_gnmi_config_with_sflow));

  // Wait until all sFLow gNMI states are converged.
  ASSERT_OK(pins_test::WaitForCondition(
      VerifySflowStatesConverged, absl::Seconds(30), sut_gnmi_stub_.get(),
      agent_address_, kInbandSamplingRate, kSampleHeaderSize,
      collector_address_and_port, sflow_enabled_interfaces));

  ASSERT_OK_AND_ASSIGN(
      Port inband_port,
      GetUnusedUpPort(*sut_gnmi_stub_, traffic_port.interface_name));

  // Program rules to forward sample pkts to control switch loopback0 IPv6
  // address.
  // 1. Set a default vrf for all packets
  // 2. Install a route entry matching on the default vrf and route prefix of
  // the control switch loopback0 ipv6.
  // 3. Define the nexthop and dependent objects for the route entry action.
  const std::string vrf_id = "vrf-50";
  ASSERT_OK(
      SetSwitchVrfForAllPackets(*sut_p4_session_, GetSutIrP4Info(), vrf_id));

  ASSERT_OK_AND_ASSIGN(std::string next_hop_id,
                       ProgramNextHops(*sut_p4_session_, GetSutIrP4Info(),
                                       absl::StrCat(inband_port.port_id)));
  ASSERT_OK(ProgramRoutesForIpv6(*sut_p4_session_, GetSutIrP4Info(), vrf_id,
                                 collector_ipv6, next_hop_id));

  // 1. Start sflowtool on control switch.
  // 2. Send traffic from control switch.
  // 3. Get sflowtool result and counters stats.
  std::string control_sflow_result, sut_sflow_result;
  int control_switch_port_id;
  {
    ASSERT_OK_AND_ASSIGN(
        std::thread control_sflowtool_thread,
        RunSflowCollectorForNSecs(
            *GetParam().ssh_client, testbed.ControlSwitch().ChassisName(),
            SflowContainerExecCmdStr(nos_param_, kSflowtoolLineFormatTemplate),
            collector_port_,
            /*sflowtool_runtime=*/packets_num / kInbandTrafficPps + 30,
            control_sflow_result));
    ASSERT_OK_AND_ASSIGN(
        std::thread sut_sflowtool_thread,
        RunSflowCollectorForNSecs(
            *GetParam().ssh_client, testbed.Sut().ChassisName(),
            SflowContainerExecCmdStr(nos_param_, kSflowtoolLineFormatTemplate),
            collector_port_,
            /*sflowtool_runtime=*/packets_num / kInbandTrafficPps + 30,
            sut_sflow_result));

    ASSERT_OK_AND_ASSIGN(
        std::string sflow_queue_name,
        GetSflowQueueName(sut_gnmi_stub_.get(), nos_param_.kCpuQueueName));
    ASSERT_OK_AND_ASSIGN(auto initial_queue_counter,
                         pins_test::GetGnmiQueueCounters(
                             "CPU", sflow_queue_name, *sut_gnmi_stub_));
    ASSERT_OK_AND_ASSIGN(
        auto sut_initial_in_band_port_counter,
        ReadCounters(inband_port.interface_name, sut_gnmi_stub_.get()));

    ASSERT_OK_AND_ASSIGN(
        auto control_initial_in_band_port_counter,
        ReadCounters(inband_port.interface_name, control_gnmi_stub_.get()));
    ASSERT_OK_AND_ASSIGN(auto control_initial_cpu_counter,
                         ReadCounters("CPU", control_gnmi_stub_.get()));

    absl::Time start_time = absl::Now();

    // Wait for sflowtool to finish and read counter data.
    absl::Cleanup clean_up([this, initial_queue_counter, start_time,
                            control_gnmi_stub_raw = control_gnmi_stub_.get(),
                            &sut_initial_in_band_port_counter,
                            &control_initial_in_band_port_counter,
                            &control_initial_cpu_counter, &inband_port,
                            &control_sflowtool_thread, &sut_sflowtool_thread,
                            &sflow_queue_name] {
      if (control_sflowtool_thread.joinable()) {
        control_sflowtool_thread.join();
      }
      if (sut_sflowtool_thread.joinable()) {
        sut_sflowtool_thread.join();
      }

      // Show counter data.
      ASSERT_OK_AND_ASSIGN(
          auto final_queue_counter,
          pins_test::GetGnmiQueueCounters("CPU", sflow_queue_name,
                                          *(this->sut_gnmi_stub_)));
      LOG(INFO) << "CPU " << sflow_queue_name << " queue counter delta:\n"
                << (final_queue_counter - initial_queue_counter)
                << " \n total time: " << (absl::Now() - start_time);

      ASSERT_OK_AND_ASSIGN(
          auto sut_final_in_band_port_counter,
          ReadCounters(inband_port.interface_name, sut_gnmi_stub_.get()));
      LOG(INFO) << " SUT inband port " << inband_port.interface_name
                << " counter delta in total time: "
                << (absl::Now() - start_time);
      ShowCounters(DeltaCounters(sut_initial_in_band_port_counter,
                                 sut_final_in_band_port_counter));

      ASSERT_OK_AND_ASSIGN(
          auto control_final_in_band_port_counter,
          ReadCounters(inband_port.interface_name, control_gnmi_stub_raw));
      LOG(INFO) << " Control switch inband port " << inband_port.interface_name
                << " counter delta in total time: "
                << (absl::Now() - start_time);
      ShowCounters(DeltaCounters(control_initial_in_band_port_counter,
                                 control_final_in_band_port_counter));

      ASSERT_OK_AND_ASSIGN(auto control_final_cpu_counter,
                           ReadCounters("CPU", control_gnmi_stub_raw));
      LOG(INFO) << " Control switch CPU counter delta in total time: "
                << (absl::Now() - start_time);
      ShowCounters(DeltaCounters(control_initial_cpu_counter,
                                 control_final_cpu_counter));
    });

    ASSERT_OK_AND_ASSIGN(
        auto control_switch_port_id_per_port_name,
        pins_test::GetAllUpInterfacePortIdsByName(*control_gnmi_stub_));
    ASSERT_OK_AND_ASSIGN(
        control_switch_port_id,
        GetPortIdFromInterfaceName(control_switch_port_id_per_port_name,
                                   traffic_port.interface_name));

    // Send packets from control switch.
    ASSERT_OK(SendNPacketsFromSwitch(
        packets_num, kInbandTrafficPps, control_switch_port_id,
        traffic_port.interface_name, sut_gnmi_stub_.get(), GetControlIrP4Info(),
        *control_p4_session_, testbed.Environment()));
  }

  EXPECT_OK(testbed.Environment().StoreTestArtifact("control_sflow_result.txt",
                                                    control_sflow_result));
  EXPECT_OK(testbed.Environment().StoreTestArtifact("sut_sflow_result.txt",
                                                    sut_sflow_result));

  EXPECT_FALSE(control_sflow_result.empty())
      << "No samples on " << traffic_port.interface_name;
  const int control_sflow_samples =
      GetSflowSamplesOnSut(control_sflow_result, control_switch_port_id);
  const int sut_sflow_samples =
      GetSflowSamplesOnSut(sut_sflow_result, control_switch_port_id);
  EXPECT_EQ(control_sflow_samples, sut_sflow_samples);
}

// 1. Pick an interface and let control switch send some traffic via this
// interface.
// 2. Start sflowtool and tcpdump on SUT.
// 3. Verify on SUT that samples are generated and tcpdump result has the
// expected DSCP value.
TEST_P(SflowMirrorTestFixture, TestSflowDscpValue) {
  thinkit::MirrorTestbed& testbed =
      GetParam().testbed_interface->GetMirrorTestbed();

  const int packets_num = 10000;

  ASSERT_OK_AND_ASSIGN(Port traffic_port,
                       GetUnusedUpPort(*sut_gnmi_stub_, /*used_port=*/""));
  LOG(INFO) << "Test parameters: traffic port name: "
            << traffic_port.interface_name << " id: " << traffic_port.port_id
            << " collector port: " << collector_port_;

  absl::flat_hash_map<std::string, bool> sflow_enabled_interfaces{
      {traffic_port.interface_name, true}};
  std::vector<std::pair<std::string, int>> collector_address_and_port{
      {kLocalLoopbackIpv6, collector_port_}};
  ASSERT_OK_AND_ASSIGN(
      auto sut_gnmi_config_with_sflow,
      UpdateSflowConfig(GetParam().sut_gnmi_config, agent_address_,
                        collector_address_and_port, sflow_enabled_interfaces,
                        kInbandSamplingRate, kSampleHeaderSize));
  ASSERT_OK(testbed.Environment().StoreTestArtifact(
      "sut_gnmi_config_with_sflow.txt",
      json_yang::FormatJsonBestEffort(sut_gnmi_config_with_sflow)));
  LOG(INFO) << "Test gnmi config: " << sut_gnmi_config_with_sflow;
  ASSERT_OK(
      pins_test::PushGnmiConfig(testbed.Sut(), sut_gnmi_config_with_sflow));

  // Wait until all sFLow gNMI states are converged.
  ASSERT_OK(pins_test::WaitForCondition(
      VerifySflowStatesConverged, absl::Seconds(30), sut_gnmi_stub_.get(),
      agent_address_, kInbandSamplingRate, kSampleHeaderSize,
      collector_address_and_port, sflow_enabled_interfaces));

  // Find the mirrored port to send packets from control switch.
  ASSERT_OK_AND_ASSIGN(
      auto control_switch_port_id_per_port_name,
      pins_test::GetAllUpInterfacePortIdsByName(*control_gnmi_stub_));
  ASSERT_OK_AND_ASSIGN(
      auto control_switch_port_id,
      GetPortIdFromInterfaceName(control_switch_port_id_per_port_name,
                                 traffic_port.interface_name));

  std::string sflow_result, tcpdump_result;
  {
    // Run sflowtool and tcpdump on SUT.
    const int runtime_secs = packets_num / kInbandTrafficPps + 30;
    ASSERT_OK_AND_ASSIGN(
        std::thread sflow_tool_thread,
        RunSflowCollectorForNSecs(
            *GetParam().ssh_client, testbed.Sut().ChassisName(),
            SflowContainerExecCmdStr(nos_param_, kSflowtoolLineFormatTemplate),
            collector_port_, runtime_secs, sflow_result));
    ASSERT_OK_AND_ASSIGN(
        std::thread tcpdump_thread,
        CaptureTcpdumpForNPackets(*GetParam().ssh_client,
                                  testbed.Sut().ChassisName(),
                                  /*packets_count=*/5, collector_port_,
                                  runtime_secs, nos_param_, tcpdump_result));

    ASSERT_OK_AND_ASSIGN(
        std::string sflow_queue_name,
        GetSflowQueueName(sut_gnmi_stub_.get(), nos_param_.kCpuQueueName));
    LOG(INFO) << "Test using sflow queue: " << sflow_queue_name;
    ASSERT_OK_AND_ASSIGN(auto initial_queue_counter,
                         pins_test::GetGnmiQueueCounters(
                             "CPU", sflow_queue_name, *sut_gnmi_stub_));
    absl::Time start_time = absl::Now();

    // Wait for sflowtool and tcpdump to finish and read counter data.
    absl::Cleanup clean_up([this, initial_queue_counter, start_time,
                            &sflow_tool_thread, &tcpdump_thread,
                            &sflow_queue_name] {
      if (sflow_tool_thread.joinable()) {
        sflow_tool_thread.join();
      }
      if (tcpdump_thread.joinable()) {
        tcpdump_thread.join();
      }
      ASSERT_OK_AND_ASSIGN(
          auto final_queue_counter,
          pins_test::GetGnmiQueueCounters("CPU", sflow_queue_name,
                                          *(this->sut_gnmi_stub_)));

      // Show CPU counter data.
      LOG(INFO) << "CPU " << sflow_queue_name << " queue counter delta:\n"
                << (final_queue_counter - initial_queue_counter)
                << " \n total time: " << (absl::Now() - start_time);
    });

    // Send packets from control switch.
    ASSERT_OK(SendNPacketsFromSwitch(
        packets_num, kInbandTrafficPps, control_switch_port_id,
        traffic_port.interface_name, sut_gnmi_stub_.get(), GetControlIrP4Info(),
        *control_p4_session_, testbed.Environment()));
  }
  EXPECT_OK(testbed.Environment().StoreTestArtifact("sflow_result.txt",
                                                    sflow_result));
  EXPECT_OK(testbed.Environment().StoreTestArtifact("tcpdump_result.txt",
                                                    tcpdump_result));
  ASSERT_THAT(ExtractTosFromTcpdumpResult(tcpdump_result),
              IsOkAndHolds(kSflowOutPacketsTos));
  
  VerifySflowResult(sflow_result, traffic_port.port_id,
                    !nos_param_.kIsSonicDebianLinux ? kDropPort : kCpuPort,
                    kSourceMac.ToHexString(), kDstMac.ToHexString(),
                    kEtherTypeIpv4, kIpv4Src.ToString(),
                    GetDstIpv4AddrByPortId(control_switch_port_id),
                    /*packet_size=*/std::nullopt, kInbandSamplingRate);

  EXPECT_FALSE(sflow_result.empty())
      << "No samples on " << traffic_port.interface_name;
}

// 1. Set sFlow config on SUT for all interfaces.
// 2. Set SUT sFlow collector as localhost ip.
// 3. Send traffic from control switch on all interfaces.
// 4. Verify samples are generated for each interface.
TEST_P(SflowMirrorTestFixture, TestSamplingWorksOnAllInterfaces) {
  thinkit::MirrorTestbed& testbed =
      GetParam().testbed_interface->GetMirrorTestbed();

  const int packets_num = 10000;
  ASSERT_OK_AND_ASSIGN(
      auto port_id_per_port_name,
      pins_test::GetAllUpInterfacePortIdsByName(*sut_gnmi_stub_));
  ASSERT_GE(port_id_per_port_name.size(), 0) << "No up interfaces.";
  ASSERT_OK_AND_ASSIGN(
      auto control_switch_port_id_per_port_name,
      pins_test::GetAllUpInterfacePortIdsByName(*control_gnmi_stub_));

  absl::flat_hash_map<std::string, bool> sflow_enabled_interfaces;
  for (const auto& [interface_name, unused] : port_id_per_port_name) {
    sflow_enabled_interfaces[interface_name] = true;
  }

  std::vector<std::pair<std::string, int>> collector_address_and_port{
      {kLocalLoopbackIpv6, collector_port_}};
  ASSERT_OK_AND_ASSIGN(
      auto sut_gnmi_config_with_sflow,
      UpdateSflowConfig(GetParam().sut_gnmi_config, agent_address_,
                        collector_address_and_port, sflow_enabled_interfaces,
                        kInbandSamplingRate, kSampleHeaderSize));
  ASSERT_OK(testbed.Environment().StoreTestArtifact(
      "sut_gnmi_config_with_sflow.txt",
      json_yang::FormatJsonBestEffort(sut_gnmi_config_with_sflow)));
  ASSERT_OK(
      pins_test::PushGnmiConfig(testbed.Sut(), sut_gnmi_config_with_sflow));

  // Wait until all sFLow gNMI states are converged.
  ASSERT_OK(pins_test::WaitForCondition(
      VerifySflowStatesConverged, absl::Seconds(30), sut_gnmi_stub_.get(),
      agent_address_, kInbandSamplingRate, kSampleHeaderSize,
      collector_address_and_port, sflow_enabled_interfaces));

  // Start sflowtool on SUT.
  std::string sflow_result;
  {
    ASSERT_OK_AND_ASSIGN(
        std::thread sflow_tool_thread,
        RunSflowCollectorNonStop(
            *GetParam().ssh_client, testbed.Sut().ChassisName(),
            SflowContainerExecCmdStr(nos_param_,
                                     kSflowtoolLineFormatNonStopTemplate),
            collector_port_, sflow_result));
    ASSERT_OK_AND_ASSIGN(
        std::string sflow_queue_name,
        GetSflowQueueName(sut_gnmi_stub_.get(), nos_param_.kCpuQueueName));
    ASSERT_OK_AND_ASSIGN(auto initial_queue_counter,
                         pins_test::GetGnmiQueueCounters(
                             "CPU", sflow_queue_name, *sut_gnmi_stub_));
    absl::Time start_time = absl::Now();

    // Wait for sflowtool to finish and read counter data.

    absl::Cleanup clean_up([this, initial_queue_counter, start_time,
                            &sflow_tool_thread, &sflow_queue_name] {
      if (sflow_tool_thread.joinable()) {
        sflow_tool_thread.join();
      }
      ASSERT_OK_AND_ASSIGN(
          auto final_queue_counter,
          pins_test::GetGnmiQueueCounters("CPU", sflow_queue_name,
                                          *(this->sut_gnmi_stub_)));

      // Show CPU counter data.
      LOG(INFO) << "CPU " << sflow_queue_name << " queue counter delta:\n"
                << (final_queue_counter - initial_queue_counter)
                << " \n total time: " << (absl::Now() - start_time);
    });

    // Send packets from control switch on all UP interfaces.
    for (const auto& [interface_name, _] : port_id_per_port_name) {
      ASSERT_OK_AND_ASSIGN(
          auto control_switch_port_id,
          GetPortIdFromInterfaceName(control_switch_port_id_per_port_name,
                                     interface_name));
      ASSERT_OK(SendNPacketsFromSwitch(
          packets_num, kInbandTrafficPps, control_switch_port_id,
          interface_name, sut_gnmi_stub_.get(), GetControlIrP4Info(),
          *control_p4_session_, testbed.Environment()));
    }
    // Sleep for 30s before stopping sflowtool.
    absl::SleepFor(absl::Seconds(30));
  }

  for (const auto& [interface_name, port_id_str] : port_id_per_port_name) {
    ASSERT_OK_AND_ASSIGN(
        auto control_switch_port_id,
        GetPortIdFromInterfaceName(control_switch_port_id_per_port_name,
                                   interface_name));
    const int sample_count =
        GetSflowSamplesOnSut(sflow_result, control_switch_port_id);
    SflowResult result = SflowResult{
        .sut_interface = interface_name,
        .packets = packets_num,
        .sampling_rate = kInbandSamplingRate,
        .expected_samples = packets_num / kInbandSamplingRate,
        .actual_samples = sample_count,
    };
    LOG(INFO) << "------ Test result ------\n" << result.DebugString();
    EXPECT_GT(sample_count, 0)
        << "No samples found for interface: " << interface_name
        << " sut port_id: " << port_id_str << ". Packets dst ip: "
        << GetDstIpv4AddrByPortId(control_switch_port_id);
  }

  EXPECT_OK(testbed.Environment().StoreTestArtifact("sflow_result.txt",
                                                    sflow_result));
}

// 1. Set sFlow config on SUT for all interfaces.
// 2. Set SUT sFlow collector as localhost ip.
// 3. Send traffic from control switch on random 5 interfaces.
// 4. Verify samples are generated for interesting interfaces.
// 5. Reboot SUT and wait for interfaces to be UP.
// 6. Send traffic from control switch on the same 5 interfaces.
// 7. Verify samples are generated for interesting interfaces.
TEST_P(SflowRebootTestFixture, TestSamplingWorksAfterReboot) {
  GetParam().testbed_interface->ExpectLinkFlaps();

  thinkit::MirrorTestbed& testbed =
      GetParam().testbed_interface->GetMirrorTestbed();

  ASSERT_OK_AND_ASSIGN(
      auto port_id_per_port_name,
      pins_test::GetAllUpInterfacePortIdsByName(*sut_gnmi_stub_));
  ASSERT_GE(port_id_per_port_name.size(), 5)
      << "Not enough up interfaces. Need 5. Actual up interfaces: "
      << port_id_per_port_name.size() << ".";
  ASSERT_OK_AND_ASSIGN(
      auto control_switch_port_id_per_port_name,
      pins_test::GetAllUpInterfacePortIdsByName(*control_gnmi_stub_));

  absl::flat_hash_map<std::string, bool> sflow_enabled_interfaces;
  // We do not want to send traffic on all ports since that would cost a lot of
  // time. Send traffic on 5 ports would be enough in our reboot test since
  // other test cases already cover sampling on all interfaces.
  std::vector<std::pair<std::string, std::string>>
      traffic_interfaces_and_port_ids;
  for (const auto& [interface_name, port_id] : port_id_per_port_name) {
    if (sflow_enabled_interfaces.size() < 5) {
      sflow_enabled_interfaces[interface_name] = true;
      traffic_interfaces_and_port_ids.push_back({interface_name, port_id});
    } else {
      sflow_enabled_interfaces[interface_name] = false;
    }
  }

  std::vector<std::pair<std::string, int>> collector_address_and_port{
      {kLocalLoopbackIpv6, collector_port_}};
  ASSERT_OK_AND_ASSIGN(
      auto sut_gnmi_config_with_sflow,
      UpdateSflowConfig(GetParam().sut_gnmi_config, agent_address_,
                        collector_address_and_port, sflow_enabled_interfaces,
                        kInbandSamplingRate, kSampleHeaderSize));
  ASSERT_OK(testbed.Environment().StoreTestArtifact(
      "sut_gnmi_config_with_sflow.txt",
      json_yang::FormatJsonBestEffort(sut_gnmi_config_with_sflow)));
  ASSERT_OK(
      pins_test::PushGnmiConfig(testbed.Sut(), sut_gnmi_config_with_sflow));

  // Wait until all sFLow gNMI states are converged.
  ASSERT_OK(pins_test::WaitForCondition(
      VerifySflowStatesConverged, absl::Seconds(30), sut_gnmi_stub_.get(),
      agent_address_, kInbandSamplingRate, kSampleHeaderSize,
      collector_address_and_port, sflow_enabled_interfaces));

  const int num_packets = 10000;

  absl::flat_hash_map<std::string, int64_t> packets_sampled_per_interface;
  for (const auto& [interface_name, unused] : traffic_interfaces_and_port_ids) {
    ASSERT_OK_AND_ASSIGN(packets_sampled_per_interface[interface_name],
                         GetSflowInterfacePacketsSampledCounter(
                             sut_gnmi_stub_.get(), interface_name));
  }
  // Start sflowtool on SUT.
  std::string sflow_result;
  {
    ASSERT_OK_AND_ASSIGN(
        std::thread sflow_tool_thread,
        RunSflowCollectorForNSecs(
            *GetParam().ssh_client, testbed.Sut().ChassisName(),
            SflowContainerExecCmdStr(nos_param_, kSflowtoolLineFormatTemplate),
            collector_port_,
            /*sflowtool_runtime=*/
            (num_packets / kInbandTrafficPps + 3) *
                    traffic_interfaces_and_port_ids.size() +
                20,
            sflow_result));

    // Wait for sflowtool to finish.
    auto clean_up = absl::Cleanup([&sflow_tool_thread] {
      if (sflow_tool_thread.joinable()) {
        sflow_tool_thread.join();
      }
    });

    // Send packets from control switch on picked interfaces.
    for (const auto& [interface_name, _] : traffic_interfaces_and_port_ids) {
      ASSERT_OK_AND_ASSIGN(
          auto control_switch_port_id,
          GetPortIdFromInterfaceName(control_switch_port_id_per_port_name,
                                     interface_name));
      ASSERT_OK(SendNPacketsFromSwitch(
          num_packets, kInbandTrafficPps, control_switch_port_id,
          interface_name, sut_gnmi_stub_.get(), GetControlIrP4Info(),
          *control_p4_session_, testbed.Environment()));
    }
  }

  // Validate sflowtool result.
  for (const auto& [interface_name, port_id_str] :
       traffic_interfaces_and_port_ids) {
    ASSERT_OK_AND_ASSIGN(
        auto control_switch_port_id,
        GetPortIdFromInterfaceName(control_switch_port_id_per_port_name,
                                   interface_name));
    const int sample_count =
        GetSflowSamplesOnSut(sflow_result, control_switch_port_id);
    SflowResult result = SflowResult{
        .sut_interface = interface_name,
        .packets = num_packets,
        .sampling_rate = kInbandSamplingRate,
        .expected_samples = num_packets / kInbandSamplingRate,
        .actual_samples = sample_count,
    };
    LOG(INFO) << "------ Test result ------\n" << result.DebugString();
    EXPECT_GT(sample_count, 0)
        << "No samples found for interface: " << interface_name
        << " sut port_id: " << port_id_str << ". Packets dst ip: "
        << GetDstIpv4AddrByPortId(control_switch_port_id);

    ASSERT_OK_AND_ASSIGN(int final_packets_sampled,
                         GetSflowInterfacePacketsSampledCounter(
                             sut_gnmi_stub_.get(), interface_name));
    int packets_sampled_counter_diff =
        final_packets_sampled - packets_sampled_per_interface[interface_name];
    EXPECT_GE(packets_sampled_counter_diff, sample_count)
        << "Gnmi path {/sampling/sflow/interfaces/interface[name="
        << interface_name
        << "]/state/packets-sampled} delta: " << packets_sampled_counter_diff
        << " is not greater or equal to control collector received sample "
           "count: "
        << sample_count;
    EXPECT_LE(packets_sampled_counter_diff, sample_count * (1 + kTolerance));
  }

  EXPECT_OK(testbed.Environment().StoreTestArtifact("sflow_result.txt",
                                                    sflow_result));

  // Reboot the switch and wait for interfaces to be up.
  if (sut_p4_session_ != nullptr) {
    EXPECT_OK(sut_p4_session_->Finish());
    sut_p4_session_ = nullptr;
  }
  if (GetParam().nsf_enabled) {
    ASSERT_OK(
        NsfRebootAndWaitForConvergence(testbed, sut_gnmi_config_with_sflow));
  } else {
    pins_test::TestGnoiSystemColdReboot(testbed.Sut());
  }
  std::vector<std::string> interface_names;
  for (const auto& [interface_name, unused] : traffic_interfaces_and_port_ids) {
    interface_names.push_back(interface_name);
  }
  ASSERT_OK(pins_test::WaitForCondition(pins_test::PortsUp, absl::Minutes(3),
                                        testbed.Sut(), interface_names,
                                        /*with_healthz=*/false));

  ASSERT_OK_AND_ASSIGN(sut_gnmi_stub_, testbed.Sut().CreateGnmiStub());
  // Wait until all sFLow gNMI states are converged.
  ASSERT_OK(pins_test::WaitForCondition(
      VerifySflowStatesConverged, absl::Minutes(2), sut_gnmi_stub_.get(),
      agent_address_, kInbandSamplingRate, kSampleHeaderSize,
      collector_address_and_port, sflow_enabled_interfaces));
  ASSERT_OK(pins_test::WaitForCondition(
      CheckStateDbPortIndexTableExists, absl::Minutes(2),
      *GetParam().ssh_client, testbed.Sut().ChassisName(),
      nos_param_.kRedisCliPath, interface_names));
  LOG(INFO) << "Sflow states are converged after reboot.";
  
  if (nos_param_.kIsSonicDebianLinux) {
    // Sleep for 2 more minutes
    absl::SleepFor(absl::Seconds(120));
  }

  for (const auto& [interface_name, unused] : sflow_enabled_interfaces) {
    ASSERT_OK_AND_ASSIGN(packets_sampled_per_interface[interface_name],
                         GetSflowInterfacePacketsSampledCounter(
                             sut_gnmi_stub_.get(), interface_name));
  }

  const int num_packets_after_reboot = 20000;
  {
    // Start sflowtool on SUT.
    ASSERT_OK_AND_ASSIGN(
        std::thread sflow_tool_thread,
        RunSflowCollectorNonStop(
            *GetParam().ssh_client, testbed.Sut().ChassisName(),
            SflowContainerExecCmdStr(nos_param_,
                                     kSflowtoolLineFormatNonStopTemplate),
            collector_port_, sflow_result));

    // Wait for sflowtool to finish.
    auto clean_up = absl::Cleanup(
        [&sflow_tool_thread, &chassis_name = testbed.Sut().ChassisName()] {
          StopSflowtool(*GetParam().ssh_client, chassis_name, kSflowToolName);
          if (sflow_tool_thread.joinable()) {
            sflow_tool_thread.join();
          }
        });

    // Send packets from control switch on picked interfaces.
    for (const auto& [interface_name, _] : traffic_interfaces_and_port_ids) {
      ASSERT_OK_AND_ASSIGN(
          auto control_switch_port_id,
          GetPortIdFromInterfaceName(control_switch_port_id_per_port_name,
                                     interface_name));
      ASSERT_OK(SendNPacketsFromSwitch(
          num_packets_after_reboot, kInbandTrafficPps, control_switch_port_id,
          interface_name, sut_gnmi_stub_.get(), GetControlIrP4Info(),
          *control_p4_session_, testbed.Environment()));
    }
    // Sleep for 30s before stopping sflowtool.
    absl::SleepFor(absl::Seconds(30));
  }

  EXPECT_OK(testbed.Environment().StoreTestArtifact(
      "sflow_result_after_reboot.txt", sflow_result));

  EXPECT_OK(IsExpectedSampleRateFromSamples(sflow_result, kInbandSamplingRate))
      << " Sample rate not as expected after reboot.";

  // Validate sflowtool result.
  for (const auto& [interface_name, port_id_str] :
       traffic_interfaces_and_port_ids) {
    ASSERT_OK_AND_ASSIGN(
        auto control_switch_port_id,
        GetPortIdFromInterfaceName(control_switch_port_id_per_port_name,
                                   interface_name));
    const int sample_count =
        GetSflowSamplesOnSut(sflow_result, control_switch_port_id);
    SflowResult result = SflowResult{
        .sut_interface = interface_name,
        .packets = num_packets_after_reboot,
        .sampling_rate = kInbandSamplingRate,
        .expected_samples = num_packets_after_reboot / kInbandSamplingRate,
        .actual_samples = sample_count,
    };
    LOG(INFO) << "------ Test result ------\n" << result.DebugString();
    EXPECT_GT(sample_count, 0)
        << "No samples found for interface: " << interface_name
        << " sut port_id: " << port_id_str << ". Packets dst ip: "
        << GetDstIpv4AddrByPortId(control_switch_port_id);

    ASSERT_OK_AND_ASSIGN(int final_sflow_interface_packets_sampled_counter,
                         GetSflowInterfacePacketsSampledCounter(
                             sut_gnmi_stub_.get(), interface_name));
    int sflow_interface_packets_sampled_counter_diff =
        final_sflow_interface_packets_sampled_counter -
        packets_sampled_per_interface[interface_name];
    EXPECT_GE(sflow_interface_packets_sampled_counter_diff, sample_count)
        << "Gnmi path {/sampling/sflow/interfaces/interface[name="
        << interface_name << "]/state/packets-sampled} delta: "
        << sflow_interface_packets_sampled_counter_diff
        << " is not greater or equal to control collector received sample "
           "count: "
        << sample_count;
    EXPECT_LE(sflow_interface_packets_sampled_counter_diff,
              sample_count * (1 + kTolerance));
  }
}

// 1. Set sFlow config on SUT for all interfaces. Disable some of them and
// enable the rest.
// 2. Send traffic from control switch on the disabled interfaces.
// 3. Verify samples are *not* generated for these interfaces.
// 5. Reboot SUT and wait for interfaces to be UP.
// 6. Send traffic from control switch on the disabled interfaces.
// 7. Verify samples are *not* generated for these interfaces.
TEST_P(SflowRebootTestFixture, TestNoSamplesOnDisabledInterfacesAfterReboot) {
  GetParam().testbed_interface->ExpectLinkFlaps();

  thinkit::MirrorTestbed& testbed =
      GetParam().testbed_interface->GetMirrorTestbed();

  ASSERT_OK_AND_ASSIGN(
      auto port_id_per_port_name,
      pins_test::GetAllUpInterfacePortIdsByName(*sut_gnmi_stub_));
  const int kDisabledInterfaceNumber = 3;
  ASSERT_GE(port_id_per_port_name.size(), kDisabledInterfaceNumber)
      << "Not enough up interfaces. Need " << kDisabledInterfaceNumber
      << ". Actual up interfaces: " << port_id_per_port_name.size() << ".";
  ASSERT_OK_AND_ASSIGN(
      auto control_switch_port_id_per_port_name,
      pins_test::GetAllUpInterfacePortIdsByName(*control_gnmi_stub_));

  absl::flat_hash_map<std::string, bool> sflow_enabled_interfaces;
  // We do not want to send traffic on all ports since that would cost a lot of
  // time. Send traffic on few ports would be enough in our reboot test since
  // other test cases already cover sampling on all interfaces.
  std::vector<std::string> traffic_interfaces;
  for (const auto& [interface_name, port_id] : port_id_per_port_name) {
    if (sflow_enabled_interfaces.size() < kDisabledInterfaceNumber) {
      sflow_enabled_interfaces[interface_name] = false;
      traffic_interfaces.push_back(interface_name);
    } else {
      sflow_enabled_interfaces[interface_name] = true;
    }
  }

  std::vector<std::pair<std::string, int>> collector_address_and_port{
      {kLocalLoopbackIpv6, collector_port_}};
  ASSERT_OK_AND_ASSIGN(
      auto sut_gnmi_config_with_sflow,
      UpdateSflowConfig(GetParam().sut_gnmi_config, agent_address_,
                        collector_address_and_port, sflow_enabled_interfaces,
                        kInbandSamplingRate, kSampleHeaderSize));
  ASSERT_OK(testbed.Environment().StoreTestArtifact(
      "sut_gnmi_config_with_sflow.txt",
      json_yang::FormatJsonBestEffort(sut_gnmi_config_with_sflow)));
  ASSERT_OK(
      pins_test::PushGnmiConfig(testbed.Sut(), sut_gnmi_config_with_sflow));

  // Wait until all sFLow gNMI states are converged.
  ASSERT_OK(pins_test::WaitForCondition(
      VerifySflowStatesConverged, absl::Seconds(30), sut_gnmi_stub_.get(),
      agent_address_, kInbandSamplingRate, kSampleHeaderSize,
      collector_address_and_port, sflow_enabled_interfaces));
  ASSERT_OK(pins_test::WaitForCondition(
      CheckStateDbPortIndexTableExists, absl::Seconds(30),
      *GetParam().ssh_client, testbed.Sut().ChassisName(),
      nos_param_.kRedisCliPath, traffic_interfaces));

  const int num_packets = 10000;
  std::string sflow_result;
  {
    // Start sflowtool on SUT.
    ASSERT_OK_AND_ASSIGN(
        std::thread sflow_tool_thread,
        RunSflowCollectorNonStop(
            *GetParam().ssh_client, testbed.Sut().ChassisName(),
            SflowContainerExecCmdStr(nos_param_,
                                     kSflowtoolLineFormatNonStopTemplate),
            collector_port_, sflow_result));
    // Wait for sflowtool to finish.
    auto clean_up = absl::Cleanup(
        [&sflow_tool_thread, &chassis_name = testbed.Sut().ChassisName()] {
          StopSflowtool(*GetParam().ssh_client, chassis_name, kSflowToolName);
          if (sflow_tool_thread.joinable()) {
            sflow_tool_thread.join();
          }
        });

    // Send packets from control switch on picked interfaces.
    for (const auto& interface_name : traffic_interfaces) {
      ASSERT_OK_AND_ASSIGN(
          auto control_switch_port_id,
          GetPortIdFromInterfaceName(control_switch_port_id_per_port_name,
                                     interface_name));
      ASSERT_OK(SendNPacketsFromSwitch(
          num_packets, kInbandTrafficPps, control_switch_port_id,
          interface_name, sut_gnmi_stub_.get(), GetControlIrP4Info(),
          *control_p4_session_, testbed.Environment()));
    }
    // Sleep 10s before stopping sflowtool.
    absl::SleepFor(absl::Seconds(10));
  }
  EXPECT_OK(testbed.Environment().StoreTestArtifact(
      "sflow_result_before_reboot.txt", sflow_result));

  // Validate samples should be 0 for disabled interfaces.
  for (const auto& interface_name : traffic_interfaces) {
    ASSERT_OK_AND_ASSIGN(
        auto control_switch_port_id,
        GetPortIdFromInterfaceName(control_switch_port_id_per_port_name,
                                   interface_name));
    const int sample_count =
        GetSflowSamplesOnSut(sflow_result, control_switch_port_id);
    EXPECT_EQ(sample_count, 0)
        << "Samples found for interface: " << interface_name
        << " control port_id: " << control_switch_port_id
        << ". Packets dst ip: "
        << GetDstIpv4AddrByPortId(control_switch_port_id);
  }

  // Reboot the switch and wait for interfaces to be up.
  if (sut_p4_session_ != nullptr) {
    EXPECT_OK(sut_p4_session_->Finish());
    sut_p4_session_ = nullptr;
  }
  if (GetParam().nsf_enabled) {
    ASSERT_OK(
        NsfRebootAndWaitForConvergence(testbed, sut_gnmi_config_with_sflow));
  } else {
    pins_test::TestGnoiSystemColdReboot(testbed.Sut());
  }
  ASSERT_OK(pins_test::WaitForCondition(pins_test::PortsUp, absl::Minutes(3),
                                        testbed.Sut(), traffic_interfaces,
                                        /*with_healthz=*/false));
  ASSERT_OK_AND_ASSIGN(sut_gnmi_stub_, testbed.Sut().CreateGnmiStub());
  // Wait until all sFLow gNMI states are converged.
  ASSERT_OK(pins_test::WaitForCondition(
      VerifySflowStatesConverged, absl::Minutes(2), sut_gnmi_stub_.get(),
      agent_address_, kInbandSamplingRate, kSampleHeaderSize,
      collector_address_and_port, sflow_enabled_interfaces));
  ASSERT_OK(pins_test::WaitForCondition(
      CheckStateDbPortIndexTableExists, absl::Minutes(2),
      *GetParam().ssh_client, testbed.Sut().ChassisName(),
      nos_param_.kRedisCliPath, traffic_interfaces));
  LOG(INFO) << "Sflow states are converged after reboot.";
   
  if (nos_param_.kIsSonicDebianLinux) {
    // Sleep for 2 more minutes
    absl::SleepFor(absl::Seconds(120));
  }

  {
    // Start sflowtool on SUT.
    ASSERT_OK_AND_ASSIGN(
        std::thread sflow_tool_thread,
        RunSflowCollectorNonStop(
            *GetParam().ssh_client, testbed.Sut().ChassisName(),
            SflowContainerExecCmdStr(nos_param_,
                                     kSflowtoolLineFormatNonStopTemplate),
            collector_port_, sflow_result));

    // Wait for sflowtool to finish.
    auto clean_up = absl::Cleanup(
        [&sflow_tool_thread, &chassis_name = testbed.Sut().ChassisName()] {
          StopSflowtool(*GetParam().ssh_client, chassis_name, kSflowToolName);
          if (sflow_tool_thread.joinable()) {
            sflow_tool_thread.join();
          }
        });

    // Send packets from control switch on picked interfaces.
    for (const auto& interface_name : traffic_interfaces) {
      ASSERT_OK_AND_ASSIGN(
          auto control_switch_port_id,
          GetPortIdFromInterfaceName(control_switch_port_id_per_port_name,
                                     interface_name));
      ASSERT_OK(SendNPacketsFromSwitch(
          num_packets, kInbandTrafficPps, control_switch_port_id,
          interface_name, sut_gnmi_stub_.get(), GetControlIrP4Info(),
          *control_p4_session_, testbed.Environment()));
    }
    // Sleep 10s before stopping sflowtool.
    absl::SleepFor(absl::Seconds(10));
  }

  EXPECT_OK(testbed.Environment().StoreTestArtifact(
      "sflow_result_after_reboot.txt", sflow_result));

  // Validate samples should be 0 for disabled interfaces.
  for (const auto& interface_name : traffic_interfaces) {
    ASSERT_OK_AND_ASSIGN(
        auto control_switch_port_id,
        GetPortIdFromInterfaceName(control_switch_port_id_per_port_name,
                                   interface_name));
    const int sample_count =
        GetSflowSamplesOnSut(sflow_result, control_switch_port_id);
    EXPECT_EQ(sample_count, 0)
        << "Samples found for interface: " << interface_name
        << " control port_id: " << control_switch_port_id
        << ". Packets dst ip: "
        << GetDstIpv4AddrByPortId(control_switch_port_id);
  }
}

// 1. Set sFlow config on SUT for one interface.
// 2. Set SUT sFlow collector as kLocalLoopbackIpv6.
// 3. Send ICMP traffic from control switch to SUT on this interface.
// 4. Validate the packets get punted and sFlowtool has expected result.
TEST_P(SflowMirrorTestFixture, TestIp2MePacketsAreSampledAndPunted) {
  thinkit::MirrorTestbed& testbed =
      GetParam().testbed_interface->GetMirrorTestbed();

  LOG(INFO) << "Starting TestIp2MePacketsAreSampledAndPunted test";

  const absl::string_view kSrcIp6Address = "2001:db8:0:12::1";
  const int packets_num = 3000;
  // Use 100 for traffic speed since we want to verify the punted packets number
  // and we don't want the punted packets to get discarded.
  const int traffic_speed = 100;

  ASSERT_OK_AND_ASSIGN(Port traffic_port,
                       GetUnusedUpPort(*sut_gnmi_stub_, /*used_port=*/""));
  ASSERT_OK_AND_ASSIGN(
      auto port_id_per_port_name,
      pins_test::GetAllUpInterfacePortIdsByName(*sut_gnmi_stub_));
  ASSERT_GE(port_id_per_port_name.size(), 0) << "No up interfaces.";

  LOG(INFO) << "Up interface numbers: " << port_id_per_port_name.size();
  LOG(INFO) << "Traffic port on SUT: " << traffic_port.interface_name << " / "
            << traffic_port.port_id;

  ASSERT_OK_AND_ASSIGN(
      auto control_switch_port_id_per_port_name,
      pins_test::GetAllUpInterfacePortIdsByName(*control_gnmi_stub_));
  ASSERT_OK_AND_ASSIGN(
      auto control_switch_port_id,
      GetPortIdFromInterfaceName(control_switch_port_id_per_port_name,
                                 traffic_port.interface_name));
  LOG(INFO) << "Traffic port on control: " << traffic_port.interface_name
            << " / " << control_switch_port_id;

  absl::flat_hash_map<std::string, bool> sflow_enabled_interfaces;
  for (const auto& [interface_name, unused] : port_id_per_port_name) {
    sflow_enabled_interfaces[interface_name] = true;
  }

  std::vector<std::pair<std::string, int>> collector_address_and_port{
      {kLocalLoopbackIpv6, collector_port_}};

  // Before starting Sflow testing, make sure punting packets to CPU works.
  bool verify_first = true;
  if (verify_first) {
    LOG(INFO) << "Start verifying punting packets to CPU works";
    Counters initial_cpu_counter;
    ASSERT_OK_AND_ASSIGN(initial_cpu_counter,
                         ReadCounters("CPU", sut_gnmi_stub_.get()));
    absl::Time start_time = absl::Now();
    auto control_switch_port = Port{
        .interface_name = traffic_port.interface_name,
        .port_id = control_switch_port_id,
    };
    ASSERT_OK(SendNSshPacketsFromSwitch(
        packets_num, traffic_speed, control_switch_port, kSrcIp6Address,
        agent_address_, sut_gnmi_stub_.get(), GetControlIrP4Info(),
        *control_p4_session_, testbed.Environment()));

    // Display the difference for CPU counter during test dev.
    ASSERT_OK_AND_ASSIGN(auto final_cpu_counter,
                         ReadCounters("CPU", sut_gnmi_stub_.get()));
    auto delta = DeltaCounters(initial_cpu_counter, final_cpu_counter);
    LOG(INFO) << "Ingress Deltas (CPU):\n total time: "
              << (absl::Now() - start_time);
    ShowCounters(delta);
    LOG(INFO) << "End verifying punting packets to CPU works";
    // Make sure at least a certain percent of packets are punted to CPU.
    uint64_t cpu_recv =
        nos_param_.kIsSonicDebianLinux ? delta.out_pkts : delta.in_pkts;
    if (cpu_recv < packets_num * kPassingPercentageCpuPunted / 100) {
      GTEST_SKIP()
          << "The SUT switch does not punt expected number of packets to CPU."
          << " Expected: " << packets_num << ". Actual: " << delta.in_pkts;
    }
  }

  // Sflow testing starting from here.
  LOG(INFO) << "Agent_address: " << agent_address_
            << " collector_address_and_port: " << kLocalLoopbackIpv6 << "/"
            << collector_port_ << " sflow_enabled_interfaces size: "
            << sflow_enabled_interfaces.size()
            << " kInbandSamplingRate:" << kInbandSamplingRate
            << " kSampleHeaderSize: " << kSampleHeaderSize;

  ASSERT_OK_AND_ASSIGN(
      auto sut_gnmi_config_with_sflow,
      UpdateSflowConfig(GetParam().sut_gnmi_config, agent_address_,
                        collector_address_and_port, sflow_enabled_interfaces,
                        kInbandSamplingRate, kSampleHeaderSize));
  ASSERT_OK(testbed.Environment().StoreTestArtifact(
      "sut_gnmi_config_with_sflow.txt",
      json_yang::FormatJsonBestEffort(sut_gnmi_config_with_sflow)));
  ASSERT_OK(
      pins_test::PushGnmiConfig(testbed.Sut(), sut_gnmi_config_with_sflow));

  // Wait until all sFLow gNMI states are converged.
  ASSERT_OK(pins_test::WaitForCondition(
      VerifySflowStatesConverged, absl::Seconds(30), sut_gnmi_stub_.get(),
      agent_address_, kInbandSamplingRate, kSampleHeaderSize,
      collector_address_and_port, sflow_enabled_interfaces));

  // Start sflowtool on peer switch.
  std::string sflow_result;

  Counters initial_cpu_counter;
  absl::Time start_time;
  {
    ASSERT_OK_AND_ASSIGN(
        std::thread sflow_tool_thread,
        RunSflowCollectorForNSecs(
            *GetParam().ssh_client, testbed.Sut().ChassisName(),
            SflowContainerExecCmdStr(nos_param_, kSflowtoolLineFormatTemplate),
            collector_port_,
            /*sflowtool_runtime=*/
            packets_num / traffic_speed + 20, sflow_result));

    // Wait for sflowtool to finish and read counter data.
    absl::Cleanup clean_up([&sflow_tool_thread] {
      if (sflow_tool_thread.joinable()) {
        sflow_tool_thread.join();
      }
    });

    ASSERT_OK_AND_ASSIGN(initial_cpu_counter,
                         ReadCounters("CPU", sut_gnmi_stub_.get()));

    start_time = absl::Now();
    auto control_switch_port = Port{
        .interface_name = traffic_port.interface_name,
        .port_id = control_switch_port_id,
    };
    ASSERT_OK(SendNSshPacketsFromSwitch(
        packets_num, traffic_speed, control_switch_port, kSrcIp6Address,
        agent_address_, sut_gnmi_stub_.get(), GetControlIrP4Info(),
        *control_p4_session_, testbed.Environment()));
  }

  // Display the difference for CPU counter during test dev.
  ASSERT_OK_AND_ASSIGN(auto final_cpu_counter,
                       ReadCounters("CPU", sut_gnmi_stub_.get()));
  auto delta = DeltaCounters(initial_cpu_counter, final_cpu_counter);
  // TODO: Enable Ip2Me test with correct expectation on CPU
  // counter.
  // EXPECT_EQ(delta.in_discards, 0);
  // EXPECT_GT(delta.in_pkts, packets_num);
  LOG(INFO) << "Ingress Deltas (CPU):\n total time: "
            << (absl::Now() - start_time);
  ShowCounters(delta);

  VerifySflowResult(sflow_result, traffic_port.port_id, kCpuPort,
                    kSourceMac.ToHexString(), kClusterMac.ToHexString(),
                    kEtherTypeIpv6, kSrcIp6Address, agent_address_,
                    /*packet_size=*/std::nullopt, kInbandSamplingRate);

  EXPECT_OK(testbed.Environment().StoreTestArtifact("sflow_result.txt",
                                                    sflow_result));
  std::vector<std::string> sflow_samples = absl::StrSplit(sflow_result, '\n');
  LOG(INFO) << "Received " << sflow_samples.size() << " samples";
  // Check Ssh pkts. TCP protocol number is 6.
  EXPECT_TRUE(HasSampleForProtocol(sflow_result, kIpProtocolTcp));
}

// TODO: Check sFlow sampling could still work after restart.
// affecting the other tests in longevity workflow. Enable the test once the
// issue related to minor alarms is fixed.
TEST_P(SflowRebootTestFixture, TestHsflowdRestartSucceed) {
  if (!GetParam().run_all_tests) {
    GTEST_SKIP() << "Skip the test on new platform, to be run later";
  }
  thinkit::MirrorTestbed& testbed =
      GetParam().testbed_interface->GetMirrorTestbed();
  auto& ssh_client = *GetParam().ssh_client;
  auto& device_name = testbed.Sut().ChassisName();
  // Get current hsflowd pid.
  ASSERT_OK_AND_ASSIGN(std::string pid, GetHsflowdPid(ssh_client, device_name));
  ASSERT_FALSE(pid.empty()) << "hsflowd pid should not be empty.";
  LOG(INFO) << "hsflowd pid: " << pid;
  // Crash hsflowd.
  ASSERT_OK_AND_ASSIGN(std::string crash_result,
                       ssh_client.RunCommand(device_name, /*command=*/
                                             R"(kill -6 $(pidof hsflowd))",
                                             /*timeout=*/absl::Seconds(5)));

  // Check if hsflowd crashes and restarts.
  ASSERT_OK(pins_test::WaitForCondition(
      [&ssh_client, &device_name, &pid]() -> absl::Status {
        ASSIGN_OR_RETURN(std::string hsflowd_pid,
                         GetHsflowdPid(ssh_client, device_name));
        if (!hsflowd_pid.empty() && hsflowd_pid != pid) {
          return absl::OkStatus();
        }
        return absl::FailedPreconditionError(
            absl::Substitute("Expected: hsflowd pid should exist and differ "
                             "from $0. Actual: hsflowd pid: $1.",
                             pid, hsflowd_pid));
      },
      absl::Seconds(120)));

  // Check and clean core file.
  ASSERT_OK_AND_ASSIGN(
      std::string core_file,
      ssh_client.RunCommand(
          device_name,
          /*command=*/"ls /tmp/core/hsflowd* -l; rm -f /tmp/core/hsflowd*",
          /*timeout=*/absl::Seconds(5)));
  EXPECT_TRUE(absl::StrContains(core_file, "hsflowd.core.bz2"))
      << "core file dump doesn't exist.";
  EXPECT_OK(testbed.Environment().StoreTestArtifact("ls_tmp_core_hsflowd.txt",
                                                    core_file));
}

// Test DPB with sFlow.
// 1. Select a random up port and do breakout on SUT.
// 2. Do breakout on same ports on Control switch.
// 3. Send packets from control switch via these new ports.
// 4. Verify there are samples generated for each interface.
TEST_P(SflowPortBreakoutTest, TestPortbreakoutWorks) {
  if (!GetParam().run_all_tests) {
    GTEST_SKIP() << "Skip the test on new platform, to be run later";
  }
  GetParam().testbed_interface->ExpectLinkFlaps();
  // Set collector address.
  thinkit::MirrorTestbed& testbed =
      GetParam().testbed_interface->GetMirrorTestbed();
  ASSERT_OK_AND_ASSIGN(
      auto control_loopback0_ipv6s,
      pins_test::ParseLoopbackIpv6s(GetParam().control_gnmi_config));
  ASSERT_GT(control_loopback0_ipv6s.size(), 0)
      << absl::Substitute("No loopback IP found for $0 testbed.",
                          testbed.ControlSwitch().ChassisName());
  // control switch.
  ASSERT_OK(SetUpMirrorTestbedWithSflowEnabledOnUpPorts(
      testbed, sut_gnmi_stub_.get(), control_gnmi_stub_.get(),
      GetParam().sut_gnmi_config, agent_address_,
      GetParam().control_gnmi_config, control_loopback0_ipv6s[0].ToString()));

  // Perform breakout on SUT.
  CollectSflowDebugs(GetParam().ssh_client, testbed.Sut().ChassisName(),
                     /*prefix=*/"predpb_sut_", testbed.Environment(),
                     nos_param_);
  pins_test::SflowBreakoutTestOption sut_option{
      .sampling_rate = kInbandSamplingRate,
      .sampling_header_size = kSampleHeaderSize,
      .agent_addr_ipv6 = agent_address_,
      .collector_ip = kLocalLoopbackIpv6,
      .collector_port = collector_port_,
      .mirror_broken_out = false,
  };
  ASSERT_OK_AND_ASSIGN(
      std::string platform_json_contents_sut,
      FetchPlatformJsonContents(*GetParam().ssh_client, testbed.Sut(),
                                GetParam().platform_json_path));
  ASSERT_OK(testbed.Environment().StoreTestArtifact(
      "predpb_sut_platform_json.txt", platform_json_contents_sut));
  ASSERT_OK_AND_ASSIGN(
      const pins_test::SflowBreakoutResult& sut_breakout_result,
      pins_test::TestBreakoutWithSflowConfig(testbed.Sut(),
                                             platform_json_contents_sut,
                                             GetSutP4Info(), sut_option));
  CollectSflowDebugs(GetParam().ssh_client, testbed.Sut().ChassisName(),
                     /*prefix=*/"postdpb_sut_", testbed.Environment(),
                     nos_param_);

  // Perform breakout on control switch with the same ports as SUT.
  CollectSflowDebugs(
      GetParam().ssh_client, testbed.ControlSwitch().ChassisName(),
      /*prefix=*/"predpb_control_", testbed.Environment(), nos_param_);
  pins_test::SflowBreakoutTestOption control_option{
      .sampling_rate = kInbandSamplingRate,
      .sampling_header_size = kSampleHeaderSize,
      .agent_addr_ipv6 = control_loopback0_ipv6s[0].ToString(),
      .collector_ip = kLocalLoopbackIpv6,
      .collector_port = collector_port_,
      .port_info = sut_breakout_result.port_info,
      .mirror_broken_out = true,
  };
  absl::Cleanup restore_control_config(
      [&control_switch = testbed.ControlSwitch(),
       &config = GetParam().control_gnmi_config] {
        ASSERT_OK(pins_test::PushGnmiConfig(control_switch, config));
      });
  ASSERT_OK_AND_ASSIGN(
      std::string platform_json_contents_control,
      FetchPlatformJsonContents(*GetParam().ssh_client, testbed.ControlSwitch(),
                                GetParam().platform_json_path));
  ASSERT_OK(testbed.Environment().StoreTestArtifact(
      "predpb_control_platform_json.txt", platform_json_contents_control));
  ASSERT_OK_AND_ASSIGN(
      const pins_test::SflowBreakoutResult& control_breakout_result,
      TestBreakoutWithSflowConfig(testbed.ControlSwitch(),
                                  platform_json_contents_control,
                                  GetControlP4Info(), control_option));
  CollectSflowDebugs(
      GetParam().ssh_client, testbed.ControlSwitch().ChassisName(),
      /*prefix=*/"postdpb_control_", testbed.Environment(), nos_param_);
  ASSERT_THAT(
      sut_breakout_result.breakout_ports,
      UnorderedElementsAreArray(control_breakout_result.breakout_ports));

  // Sleep 60s to ensure sFlow is converged.
  absl::SleepFor(absl::Seconds(60));

  // Update port name per id mapping for later testing.
  ASSERT_OK_AND_ASSIGN(
      auto port_id_per_port_name,
      pins_test::GetAllUpInterfacePortIdsByName(*sut_gnmi_stub_));
  ASSERT_GT(port_id_per_port_name.size(), 0) << "No up interfaces.";
  ASSERT_OK_AND_ASSIGN(
      auto control_switch_port_id_per_port_name,
      pins_test::GetAllUpInterfacePortIdsByName(*control_gnmi_stub_));

  // Verify sFlow still works on break out ports.
  const int packets_num = 10000;
  std::string sflow_result;
  {
    ASSERT_OK_AND_ASSIGN(
        std::thread sflow_tool_thread,
        RunSflowCollectorForNSecs(
            *GetParam().ssh_client, testbed.Sut().ChassisName(),
            SflowContainerExecCmdStr(nos_param_, kSflowtoolLineFormatTemplate),
            collector_port_,
            /*sflowtool_runtime=*/
            (packets_num / kInbandTrafficPps + 3) *
                    sut_breakout_result.breakout_ports.size() +
                100,
            sflow_result));
    ASSERT_OK_AND_ASSIGN(
        const auto kSflowQueueName,
        GetSflowQueueName(sut_gnmi_stub_.get(), nos_param_.kCpuQueueName));
    ASSERT_OK_AND_ASSIGN(auto initial_queue_counter,
                         pins_test::GetGnmiQueueCounters("CPU", kSflowQueueName,
                                                         *sut_gnmi_stub_));
    absl::Time start_time = absl::Now();

    // Wait for sflowtool to finish and read counter data.
    absl::Cleanup clean_up([this, initial_queue_counter, start_time,
                            &sflow_tool_thread, &kSflowQueueName] {
      if (sflow_tool_thread.joinable()) {
        sflow_tool_thread.join();
      }
      ASSERT_OK_AND_ASSIGN(
          auto final_queue_counter,
          pins_test::GetGnmiQueueCounters("CPU", kSflowQueueName,
                                          *(this->sut_gnmi_stub_)));

      // Show CPU counter data.
      LOG(INFO) << "CPU " << kSflowQueueName << " queue counter delta:\n"
                << (final_queue_counter - initial_queue_counter)
                << " \n total time: " << (absl::Now() - start_time);
    });

    // Send packets from control switch on all breakout ports.
    for (const std::string& port_name : sut_breakout_result.breakout_ports) {
      ASSERT_OK_AND_ASSIGN(
          int control_switch_port_id,
          GetPortIdFromInterfaceName(control_switch_port_id_per_port_name,
                                     port_name));
      ASSERT_OK(SendNPacketsFromSwitch(
          packets_num, kInbandTrafficPps, control_switch_port_id, port_name,
          sut_gnmi_stub_.get(), GetControlIrP4Info(), *control_p4_session_,
          testbed.Environment()));
    }
  }

  for (const auto& port_name : sut_breakout_result.breakout_ports) {
    ASSERT_OK_AND_ASSIGN(int control_switch_port_id,
                         GetPortIdFromInterfaceName(
                             control_switch_port_id_per_port_name, port_name));
    const int sample_count =
        GetSflowSamplesOnSut(sflow_result, control_switch_port_id);
    SflowResult result = SflowResult{
        .sut_interface = port_name,
        .packets = packets_num,
        .sampling_rate = kInbandSamplingRate,
        .expected_samples = packets_num / kInbandSamplingRate,
        .actual_samples = sample_count,
    };
    LOG(INFO) << "------ Test result ------\n" << result.DebugString();
    EXPECT_GT(sample_count, 0)
        << "No samples found for interface: " << port_name
        << ". Packets dst ip: "
        << GetDstIpv4AddrByPortId(control_switch_port_id);
  }

  EXPECT_OK(testbed.Environment().StoreTestArtifact("sflow_result.txt",
                                                    sflow_result));
}

}  // namespace pins
