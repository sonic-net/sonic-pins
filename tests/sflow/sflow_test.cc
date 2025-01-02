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
#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <thread>  // NOLINT: Need threads (instead of fiber) for upstream code.
#include <utility>
#include <vector>

#include "absl/cleanup/cleanup.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/ascii.h"
#include "absl/strings/match.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/synchronization/mutex.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/collections.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/ixia_helper.h"
#include "lib/utils/json_utils.h"
#include "lib/validator/validator_lib.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/p4_runtime_session_extras.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/pd.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "tests/forwarding/group_programming_util.h"
#include "tests/forwarding/util.h"
#include "tests/lib/p4rt_fixed_table_programming_helper.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "tests/qos/gnmi_parsers.h"
#include "tests/qos/packet_in_receiver.h"
#include "tests/qos/qos_test_util.h"
#include "tests/sflow/sflow_util.h"
#include "tests/thinkit_sanity_tests.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/ssh_client.h"

namespace pins {

namespace {

using ::gutil::IsOkAndHolds;

// Number of packets sent to one port.
constexpr int kPacketsNum = 1000000;

// Number of packets sent per second.
constexpr int kPacketsPerSecond = 16000;

// The maximum number of bytes that should be copied from a sampled packet to
// the sFlow datagram.
constexpr int kSampleHeaderSize = 512;

// Once accumulated data reaches kMaxPacketSize, sFlow would generate an sFlow
// datagram.
constexpr int kMaxPacketSize = 1400;

// Sflowtool binary name in the collector.
constexpr absl::string_view kSflowToolName = "sflowtool";

constexpr int kSflowCollectorPort = 6343;

constexpr absl::string_view kSflowtoolLineFormatTemplate =
    "/etc/init.d/sflow-container exec '$0 -l -p 6343 &"
    " pid=$$!; sleep $1; kill -9 $$pid;'";

constexpr absl::string_view kSflowtoolFullFormatTemplate =
    "/etc/init.d/sflow-container exec '$0 -p 6343 &"
    " pid=$$!; sleep $1; kill -9 $$pid;'";

constexpr absl::string_view kTcpdumpForTos =
    "tcpdump -c $0 -i lo -vv -eX udp and port 6343";

// IpV4 address for filtering the sFlow packet.
constexpr uint32_t kIpV4Src = 0x01020304;  // 1.2.3.4
// Ixia flow details.
constexpr auto kDstMac = netaddr::MacAddress(02, 02, 02, 02, 02, 03);
constexpr auto kSourceMac = netaddr::MacAddress(00, 01, 02, 03, 04, 05);
constexpr auto kIpV4Dst = netaddr::Ipv4Address(192, 168, 10, 1);

constexpr int kSamplingRateInterval = 4000;

// Buffering and software bottlenecks can cause some amount of variance in rate
// measured end to end.
// Level of tolerance for packet rate verification.
// This could be parameterized in future if this is platform dependent.
constexpr double kTolerance = 0.20;

// Vrf prefix used in the test.
constexpr absl::string_view kVrfIdPrefix = "vrf-";

// Used for sFLow collector.
constexpr char kLocalLoopbackIpv6[] = "::1";

// We need 300 samples/sec for 3 secs to trigger this back off. Let's use 5 secs
// and 900 samples/sec which are larger values to make sure backoff could be
// triggered.
constexpr int kBackOffThresholdSamples = 900;
constexpr int kBackOffThresholdDuration = 5;

constexpr absl::string_view kSflowQueueName = "BE1";
constexpr int kSflowOutPacketsTos = 0x80;
constexpr absl::string_view kEtherTypeIpv4 = "0x0800";

// Returns IP address in dot-decimal notation, e.g. "192.168.2.1".
std::string GetSrcIpv4AddrByPortId(const int port_id) {
  return netaddr::Ipv4Address(std::bitset<32>(kIpV4Src + port_id)).ToString();
}

// Sets ACL punt rule according to `port_id`.
absl::Status SetUpAclPunt(pdpi::P4RuntimeSession& p4_session,
                          const pdpi::IrP4Info& ir_p4info, int port_id) {
  ASSIGN_OR_RETURN(
      p4::v1::TableEntry pi_entry,
      pdpi::PartialPdTableEntryToPiTableEntry(
          ir_p4info, gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
                         R"pb(
                           acl_ingress_table_entry {
                             match {
                               dst_mac { value: "$0" mask: "ff:ff:ff:ff:ff:ff" }
                               is_ipv4 { value: "0x1" }
                               src_ip { value: "$1" mask: "255.255.255.255" }
                               dst_ip { value: "$2" mask: "255.255.255.255" }
                             }
                             action { acl_trap { qos_queue: "0x7" } }
                             priority: 1
                           }
                         )pb",
                         kDstMac.ToString(), GetSrcIpv4AddrByPortId(port_id),
                         kIpV4Dst.ToString()))));
  return pdpi::InstallPiTableEntry(&p4_session, pi_entry);
}

// Sets ACL drop rule according to `port_id`.
absl::Status SetUpAclDrop(pdpi::P4RuntimeSession& p4_session,
                          const pdpi::IrP4Info& ir_p4info, int port_id) {
  ASSIGN_OR_RETURN(
      p4::v1::TableEntry pi_entry,
      pdpi::PartialPdTableEntryToPiTableEntry(
          ir_p4info, gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
                         R"pb(
                           acl_ingress_table_entry {
                             match {
                               dst_mac { value: "$0" mask: "ff:ff:ff:ff:ff:ff" }
                               is_ipv4 { value: "0x1" }
                               src_ip { value: "$1" mask: "255.255.255.255" }
                               dst_ip { value: "$2" mask: "255.255.255.255" }
                             }
                             action { acl_drop {} }
                             priority: 1
                           }
                         )pb",
                         kDstMac.ToString(), GetSrcIpv4AddrByPortId(port_id),
                         kIpV4Dst.ToString()))));
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

// The packets are all same for one port. Use port_id as the index for
// generating packets.
absl::Status SendNPacketsToSut(absl::Span<const std::string> traffic_ref,
                               absl::string_view topology_ref,
                               absl::Duration runtime,
                               thinkit::GenericTestbed& testbed) {
  // Send Ixia traffic.
  RETURN_IF_ERROR(
      pins_test::ixia::StartTraffic(traffic_ref, topology_ref, testbed));

  // Wait for Traffic to be sent.
  absl::SleepFor(runtime);

  // Stop Ixia traffic.
  RETURN_IF_ERROR(pins_test::ixia::StopTraffic(traffic_ref, testbed));

  return absl::OkStatus();
}

// Set up Ixia traffic with given parameters and return the traffic ref and
// topology ref string.
absl::StatusOr<std::pair<std::vector<std::string>, std::string>>
SetUpIxiaTraffic(absl::Span<const IxiaLink> ixia_links,
                 thinkit::GenericTestbed& testbed, const int64_t pkt_count,
                 const int64_t pkt_rate, const int frame_size = 1000) {
  std::vector<std::string> traffic_refs;
  std::string topology_ref;
  for (const IxiaLink& ixia_link : ixia_links) {
    LOG(INFO) << __func__ << " Ixia if:" << ixia_link.ixia_interface
              << " sut if:" << ixia_link.sut_interface
              << " port id:" << ixia_link.port_id;

    std::string ixia_interface = ixia_link.ixia_interface;
    std::string sut_interface = ixia_link.sut_interface;

    // Set up Ixia traffic.
    ASSIGN_OR_RETURN(pins_test::ixia::IxiaPortInfo ixia_port,
                     pins_test::ixia::ExtractPortInfo(ixia_interface));
    ASSIGN_OR_RETURN(std::string topology_ref_tmp,
                     pins_test::ixia::IxiaConnect(ixia_port.hostname, testbed));
    if (topology_ref.empty()) {
      topology_ref = topology_ref_tmp;
    } else {
      EXPECT_EQ(topology_ref, topology_ref_tmp);
    }

    ASSIGN_OR_RETURN(std::string vport_ref,
                     pins_test::ixia::IxiaVport(topology_ref, ixia_port.card,
                                                ixia_port.port, testbed));

    ASSIGN_OR_RETURN(std::string traffic_ref,
                     pins_test::ixia::IxiaSession(vport_ref, testbed));

    RETURN_IF_ERROR(
        pins_test::ixia::SetFrameRate(traffic_ref, pkt_rate, testbed));

    RETURN_IF_ERROR(
        pins_test::ixia::SetFrameCount(traffic_ref, pkt_count, testbed));

    RETURN_IF_ERROR(
        pins_test::ixia::SetFrameSize(traffic_ref, frame_size, testbed));

    RETURN_IF_ERROR(pins_test::ixia::SetSrcMac(traffic_ref,
                                               kSourceMac.ToString(), testbed));

    RETURN_IF_ERROR(
        pins_test::ixia::SetDestMac(traffic_ref, kDstMac.ToString(), testbed));

    RETURN_IF_ERROR(pins_test::ixia::AppendIPv4(traffic_ref, testbed));

    // Use Ipv4 source address to differentiate different ports.
    RETURN_IF_ERROR(pins_test::ixia::SetSrcIPv4(
        traffic_ref, GetSrcIpv4AddrByPortId(ixia_link.port_id), testbed));

    RETURN_IF_ERROR(pins_test::ixia::SetDestIPv4(traffic_ref,
                                                 kIpV4Dst.ToString(), testbed));
    traffic_refs.push_back(traffic_ref);
  }
  return std::make_pair(traffic_refs, topology_ref);
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

absl::Status SetIxiaTrafficParams(absl::string_view traffic_ref,
                                  int64_t pkts_num, int64_t traffic_rate,
                                  thinkit::GenericTestbed& generic_testbed) {
  RETURN_IF_ERROR(pins_test::ixia::SetFrameRate(traffic_ref, traffic_rate,
                                                generic_testbed));
  return pins_test::ixia::SetFrameCount(traffic_ref, pkts_num, generic_testbed);
}

// Run sflowtool on SUT in a new thread. Returns the thread to let caller to
// wait for the finish.
absl::StatusOr<std::thread> RunSflowCollectorForNSecs(
    thinkit::SSHClient& ssh_client, absl::string_view device_name,
    absl::string_view sflow_template, const int sflowtool_runtime,
    std::string& sflow_tool_result) {
  std::thread sflow_tool_thread =
      std::thread([&sflow_tool_result, &ssh_client, device_name, sflow_template,
                   sflowtool_runtime]() {
        const std::string ssh_command =
            absl::Substitute(sflow_template, kSflowToolName, sflowtool_runtime);
        LOG(INFO) << "ssh command:" << ssh_command;
        ASSERT_OK_AND_ASSIGN(
            sflow_tool_result,
            ssh_client.RunCommand(
                device_name, ssh_command,
                /*timeout=*/absl::Seconds(sflowtool_runtime + 10)));
      });
  // Sleep to wait sflowtool to start.
  absl::SleepFor(absl::Seconds(5));
  return sflow_tool_thread;
}

// Run tcpdump on SUT in a new thread. Returns the thread to let caller to
// wait for the finish.
absl::StatusOr<std::thread> CaptureTcpdumpForNPackets(
    thinkit::SSHClient& ssh_client, absl::string_view device_name,
    int packets_count, const int runtime, std::string& result) {
  std::thread thread = std::thread([device_name, packets_count, runtime,
                                    &ssh_client, &result]() {
    std::string ssh_command = absl::Substitute(kTcpdumpForTos, packets_count);
    LOG(INFO) << "ssh command:" << ssh_command;
    ASSERT_OK_AND_ASSIGN(
        result, ssh_client.RunCommand(device_name, ssh_command,
                                      /*timeout=*/absl::Seconds(runtime + 10)));
  });
  return thread;
}

// Send packets to SUT and validate packet counters via gNMI.
absl::Status SendSflowTraffic(absl::Span<const std::string> traffic_refs,
                              absl::string_view topology_ref,
                              absl::Span<const IxiaLink> ixia_links,
                              thinkit::GenericTestbed& testbed,
                              gnmi::gNMI::StubInterface* gnmi_stub,
                              const int64_t pkt_count, const int64_t pkt_rate) {
  // Read initial counters via GNMI from the SUT
  LOG(INFO) << "Read initial packet counters.";
  ASSIGN_OR_RETURN(std::vector<Counters> initial_in_counters,
                   GetIxiaInterfaceCounters(ixia_links, gnmi_stub));
  ASSIGN_OR_RETURN(
      auto initial_queue_counter,
      pins_test::GetGnmiQueueCounters("CPU", kSflowQueueName, *gnmi_stub));
  absl::Time start_time = absl::Now();

  RETURN_IF_ERROR(SendNPacketsToSut(
      traffic_refs, topology_ref,
      /*runtime=*/absl::Seconds(std::ceil(1.0f * pkt_count / pkt_rate)),
      testbed));

  LOG(INFO) << "Read final packet counters.";
  // Read final counters via GNMI from the SUT
  ASSIGN_OR_RETURN(std::vector<Counters> final_in_counters,
                   GetIxiaInterfaceCounters(ixia_links, gnmi_stub));
  for (size_t i = 0; i < ixia_links.size(); ++i) {
    auto delta = DeltaCounters(initial_in_counters[i], final_in_counters[i]);
    // Display the difference in the counters for now (during test dev)
    LOG(INFO) << "\nIngress Deltas (" << ixia_links[i].sut_interface << "):\n";
    ShowCounters(delta);
    EXPECT_EQ(delta.in_pkts, pkt_count)
        << "Received packets count is not equal to sent packets count: "
        << ". Interface: " << ixia_links[i].sut_interface << ". Sent "
        << pkt_count << ". Received " << delta.in_pkts << ".";
  }
  ASSIGN_OR_RETURN(
      auto final_queue_counter,
      pins_test::GetGnmiQueueCounters("CPU", kSflowQueueName, *gnmi_stub));

  // Show CPU counter data.
  auto delta =
      DeltaCounters(initial_in_counters.back(), final_in_counters.back());
  LOG(INFO) << "\nIngress Deltas (\"CPU\"):\n";
  ShowCounters(delta);
  LOG(INFO) << "CPU " << kSflowQueueName << " queue counter delta:\n"
            << final_queue_counter - initial_queue_counter
            << " \n total time: " << (absl::Now() - start_time);
  return absl::OkStatus();
}

int GetSflowSamplesOnSut(const std::string& sflowtool_output,
                         const int port_id) {
  constexpr int kFieldSize = 20, kSrcIpIdx = 9;
  int count = 0;
  // Each line indicates one sFlow sample.
  for (absl::string_view sflow : absl::StrSplit(sflowtool_output, '\n')) {
    // Split by column.
    std::vector<absl::string_view> fields = absl::StrSplit(sflow, ',');
    if (fields.size() < kFieldSize) {
      continue;
    }
    // Filter source ip.
    if (fields[kSrcIpIdx] == GetSrcIpv4AddrByPortId(port_id)) {
      count++;
    }
  }
  return count;
}

// Get port speed by reading interface/ethernet/state/port-speed path.
absl::StatusOr<std::string> GetPortSpeed(absl::string_view iface,
                                         gnmi::gNMI::StubInterface* gnmi_stub) {
  std::string ops_state_path = absl::StrCat("interfaces/interface[name=", iface,
                                            "]/ethernet/state/port-speed");

  std::string ops_parse_str = "openconfig-if-ethernet:port-speed";
  return pins_test::GetGnmiStatePathInfo(gnmi_stub, ops_state_path,
                                         ops_parse_str);
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
  // srcIP 1.2.5.12
  // ...
  // endSample   ----------------------
  // endDatagram   =================================
  EXPECT_OK(test_environment.StoreTestArtifact(file_name, sflow_datagram));

  // Verifies this datagram is generated from specific traffic. We use srcIP
  // value for specific in port so we use it to validate as well.
  ASSIGN_OR_RETURN(absl::string_view src_ip,
                   ExtractValueByKey(sflow_datagram, "srcIP"));
  if (src_ip != GetSrcIpv4AddrByPortId(port_id)) {
    return absl::FailedPreconditionError(
        absl::Substitute("srcIp field in sflow sample is not as expected: "
                         "expected: $0, actual: $1.",
                         GetSrcIpv4AddrByPortId(port_id), src_ip));
  }
  // Header length would be after `headerLen` field.
  ASSIGN_OR_RETURN(absl::string_view header_len_str,
                   ExtractValueByKey(sflow_datagram, "headerLen"));
  int header_len;
  (void)absl::SimpleAtoi(header_len_str, &header_len);
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
                       int packet_size, int sampling_rate) {
  constexpr int kFieldSize = 20, kInputPortIdx = 2, kOutputPortIdx = 3,
                kSrcMacIdx = 4, kDstMacIdx = 5, kEthTypeIdx = 6, kSrcIpIdx = 9,
                kDstIpIdx = 10, kPktSizeIdx = 17, kSamplingRateIdx = 19;
  // Each line indicates one sFlow sample.
  for (absl::string_view sflow_sample :
       absl::StrSplit(sflowtool_output, '\n')) {
    // Split by column.
    std::vector<absl::string_view> fields = absl::StrSplit(sflow_sample, ',');
    if (fields.size() < kFieldSize) {
      continue;
    }
    // Filter source ip.
    if (fields[kSrcIpIdx] == src_ip) {
      if (input_port.has_value()) {
        EXPECT_EQ(fields[kInputPortIdx], absl::StrCat(*input_port));
      }
      if (output_port.has_value()) {
        EXPECT_EQ(fields[kOutputPortIdx], absl::StrCat(*output_port));
      }
      // The sample mac address does not have the "0x" prefix
      EXPECT_EQ(fields[kSrcMacIdx], src_mac.substr(2));
      EXPECT_EQ(fields[kDstMacIdx], dst_mac.substr(2));
      EXPECT_EQ(fields[kEthTypeIdx], ethernet_type);
      EXPECT_EQ(fields[kSrcIpIdx], src_ip);
      EXPECT_EQ(fields[kDstIpIdx], dst_ip);
      // Since PINs cap at 1028 packet size for punt packets, the maximum value
      // of sample's packet size field would be 1028.
      EXPECT_EQ(fields[kPktSizeIdx], absl::StrCat(std::min(packet_size, 1028)));
      EXPECT_EQ(fields[kSamplingRateIdx], absl::StrCat(sampling_rate));
    }
  }
}

// Save output for:
// /proc/bcm/knet-cb/psample/map
// /proc/bcm/knet-cb/psample/stats
// /proc/bcm/knet-cb/psample/rate
// sflow container /etc/hsflowd.auto
// state db json
// app state db json
void CollectSflowDebugs(thinkit::SSHClient* ssh_client,
                        absl::string_view device_name, absl::string_view prefix,
                        thinkit::TestEnvironment& environment) {
  ASSERT_OK_AND_ASSIGN(
      std::string result,
      ssh_client->RunCommand(device_name,
                             /*command=*/"cat /proc/bcm/knet-cb/psample/map",
                             absl::Seconds(20)));
  EXPECT_OK(environment.StoreTestArtifact(
      absl::StrCat(prefix, "sut_bcm_knet_psample_map.txt"), result));

  ASSERT_OK_AND_ASSIGN(
      result,
      ssh_client->RunCommand(device_name,
                             /*command=*/"cat /proc/bcm/knet-cb/psample/stats",
                             absl::Seconds(20)));
  EXPECT_OK(environment.StoreTestArtifact(
      absl::StrCat(prefix, "sut_bcm_knet_psample_stats.txt"), result));

  ASSERT_OK_AND_ASSIGN(
      result, ssh_client->RunCommand(
                  device_name, /*command=*/"cat /proc/bcm/knet-cb/psample/rate",
                  absl::Seconds(20)));
  EXPECT_OK(environment.StoreTestArtifact(
      absl::StrCat(prefix, "sut_bcm_knet_psample_rate.txt"), result));

  ASSERT_OK_AND_ASSIGN(
      result, ssh_client->RunCommand(
                  device_name,
                  /*command=*/
                  "/etc/init.d/sflow-container exec 'cat /etc/hsflowd.auto'",
                  absl::Seconds(20)));
  EXPECT_OK(environment.StoreTestArtifact(
      absl::StrCat(prefix, "sflow_container_hsflowd_auto.txt"), result));
  ASSERT_OK_AND_ASSIGN(
      result, ssh_client->RunCommand(device_name,
                                     /*command=*/
                                     "ip -6 route show", absl::Seconds(20)));
  EXPECT_OK(environment.StoreTestArtifact(
      absl::StrCat(prefix, "ipv6_route_show.txt"), result));
  ASSERT_OK_AND_ASSIGN(
      result, ssh_client->RunCommand(device_name,
                                     /*command=*/
                                     "ip -6 neigh show", absl::Seconds(20)));
  EXPECT_OK(environment.StoreTestArtifact(
      absl::StrCat(prefix, "ipv6_neigh_show.txt"), result));

  // STATE_DB
  ASSERT_OK_AND_ASSIGN(
      result, ssh_client->RunCommand(device_name,
                                     /*command=*/
                                     "ctr tasks exec --exec-id tmp db-con "
                                     "redis-dump -H 127.0.0.1 -p 6379 -d 6 -y",
                                     absl::Seconds(20)));
  EXPECT_OK(environment.StoreTestArtifact(
      absl::StrCat(prefix, "sut_state_db.txt"), result));

  // APPL_STATE_DB
  ASSERT_OK_AND_ASSIGN(
      result, ssh_client->RunCommand(device_name,
                                     /*command=*/
                                     "ctr tasks exec --exec-id tmp db-con "
                                     "redis-dump -H 127.0.0.1 -p 6379 -d 14 -y",
                                     absl::Seconds(20)));
  EXPECT_OK(environment.StoreTestArtifact(
      absl::StrCat(prefix, "sut_app_state_db.txt"), result));
}

// Returns OK if `sflowtool_output` has expected sample rate. i.e.,
// comp(actual_sample_rate, sample_rate) is true. Returns an InternalError if
// something goes wrong.
// TODO: Change test expectation once sFlow change is merged in
// PINs release.
absl::Status IsExpectedSampleRateFromSamples(
    absl::string_view sflowtool_output, int sample_rate,
    std::function<bool(int, int)> comp) {
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
  if (!comp(actual_sample_rate, sample_rate)) {
    return absl::InternalError(
        absl::Substitute("Expect sample rate : $0. Actual sample rate: $1.",
                         sample_rate, actual_sample_rate));
  }
  return absl::OkStatus();
}

// Verify that `comp`(`sflow_enabled_interfaces`[interface],
// `initial_interfaces_to_sample_rate`[interface]) is true .
// TODO: Change test expectation once sFlow change is merged in
// PINs release.
absl::Status IsExpectedSamplingRateFromGnmi(
    gnmi::gNMI::StubInterface* gnmi_stub,
    const absl::flat_hash_set<std::string>& sflow_enabled_interfaces,
    const absl::flat_hash_map<std::string, int>&
        initial_interfaces_to_sample_rate,
    std::function<bool(int, int)> comp) {
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
    if (!comp(sample_rate, *initial_sample_rate)) {
      return absl::InternalError(absl::Substitute(
          "Current interface $0 sample rate is not as expected. "
          "Initial sample rate: $1. Current sample rate: $2.",
          interface, *initial_sample_rate, sample_rate));
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

}  // namespace

void SflowTestFixture::SetUp() {
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

  int sampling_size, sampling_rate;
  std::vector<std::pair<std::string, int>> collector_address_and_port;
  const std::string& gnmi_config = GetParam().gnmi_config;
  ASSERT_OK(testbed_->Environment().StoreTestArtifact("gnmi_config.txt",
                                                      gnmi_config));
  sampling_size = kSampleHeaderSize;
  sampling_rate = kSamplingRateInterval;

  // Set to localhost ip by default.
  collector_address_and_port.push_back(
      {kLocalLoopbackIpv6, kSflowCollectorPort});
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
  ASSERT_FALSE(ready_links_.empty()) << "Ixia links are not ready";

  CollectSflowDebugs(ssh_client_, testbed_->Sut().ChassisName(),
                     /*prefix=*/"pretest_", testbed_->Environment());
}

void SflowTestFixture::TearDown() {
  LOG(INFO) << "\n------ TearDown START ------\n";

  CollectSflowDebugs(ssh_client_, testbed_->Sut().ChassisName(),
                     /*prefix=*/"posttest_", testbed_->Environment());

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
  testbed_->Environment().SetTestCaseID("6c980337-c187-4f19-99a9-e03b6dcf24b5");

  const IxiaLink& ingress_link = ready_links_[0];
  Port ingress_port = Port{
      .interface_name = ingress_link.sut_interface,
      .port_id = ingress_link.port_id,
  };
  const int pkt_size = 500;

  // ixia_ref_pair would include the traffic reference and topology reference
  // which could be used to send traffic later.
  std::pair<std::vector<std::string>, std::string> ixia_ref_pair;
  // Set up Ixia traffic.
  ASSERT_OK_AND_ASSIGN(ixia_ref_pair,
                       SetUpIxiaTraffic({ingress_link}, *testbed_, kPacketsNum,
                                        kPacketsPerSecond, pkt_size));

  std::string sflow_result;
  {
    // Start sflowtool on SUT.
    ASSERT_OK_AND_ASSIGN(
        std::thread sflow_tool_thread,
        RunSflowCollectorForNSecs(
            *ssh_client_, testbed_->Sut().ChassisName(),
            kSflowtoolLineFormatTemplate,
            /*sflowtool_runtime=*/kPacketsNum / kPacketsPerSecond + 30,
            sflow_result));

    // Wait for sflowtool to finish.
    absl::Cleanup clean_up([&sflow_tool_thread] {
      if (sflow_tool_thread.joinable()) {
        sflow_tool_thread.join();
      }
    });

    // Send packets from Ixia to SUT.
    ASSERT_OK(SendSflowTraffic(ixia_ref_pair.first, ixia_ref_pair.second,
                               {ingress_link}, *testbed_, gnmi_stub_.get(),
                               kPacketsNum, kPacketsPerSecond));
  }

  LOG(INFO) << "sFlow samples:\n" << sflow_result;
  VerifySflowResult(sflow_result, ingress_port.port_id,
                    /*output_port=*/std::nullopt, kSourceMac.ToHexString(),
                    kDstMac.ToHexString(), kEtherTypeIpv4,
                    GetSrcIpv4AddrByPortId(ingress_link.port_id),
                    kIpV4Dst.ToString(), pkt_size, kSamplingRateInterval);

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
  testbed_->Environment().SetTestCaseID("909e2260-d4ca-4018-8c6a-2bd7891ee686");

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
  // Set up Ixia traffic. ixia_ref_pair would include the traffic reference and
  // topology reference which could be used to send traffic later.
  std::pair<std::vector<std::string>, std::string> ixia_ref_pair;
  ASSERT_OK_AND_ASSIGN(ixia_ref_pair,
                       SetUpIxiaTraffic({ingress_link}, *testbed_, kPacketsNum,
                                        kPacketsPerSecond, pkt_size));

  std::string sflow_result;
  {
    // Start sflowtool on SUT.
    ASSERT_OK_AND_ASSIGN(
        std::thread sflow_tool_thread,
        RunSflowCollectorForNSecs(
            *ssh_client_, testbed_->Sut().ChassisName(),
            kSflowtoolLineFormatTemplate,
            /*sflowtool_runtime=*/kPacketsNum / kPacketsPerSecond + 30,
            sflow_result));

    // Wait for sflowtool to finish.
    absl::Cleanup clean_up([&sflow_tool_thread] {
      if (sflow_tool_thread.joinable()) {
        sflow_tool_thread.join();
      }
    });

    // Send packets from Ixia to SUT.
    ASSERT_OK(SendSflowTraffic(ixia_ref_pair.first, ixia_ref_pair.second,
                               {ingress_link}, *testbed_, gnmi_stub_.get(),
                               kPacketsNum, kPacketsPerSecond));
  }

  LOG(INFO) << "sFlow samples:\n" << sflow_result;
  EXPECT_OK(testbed_->Environment().StoreTestArtifact("sflow_result.txt",
                                                      sflow_result));
  VerifySflowResult(sflow_result, ingress_port.port_id, egress_port.port_id,
                    kSourceMac.ToHexString(), kDstMac.ToHexString(),
                    kEtherTypeIpv4,
                    GetSrcIpv4AddrByPortId(ingress_link.port_id),
                    kIpV4Dst.ToString(), pkt_size, kSamplingRateInterval);

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
  testbed_->Environment().SetTestCaseID("6d567c91-d018-4fb3-85fc-c75c5f425d15");

  const IxiaLink& ingress_link = ready_links_[0];
  Port ingress_port = Port{
      .interface_name = ingress_link.sut_interface,
      .port_id = ingress_link.port_id,
  };
  ASSERT_OK(
      SetUpAclDrop(*sut_p4_session_, GetIrP4Info(), ingress_port.port_id));
  const int pkt_size = 500;

  // Set up Ixia traffic. ixia_ref_pair would include the traffic reference and
  // topology reference which could be used to send traffic later.
  std::pair<std::vector<std::string>, std::string> ixia_ref_pair;
  ASSERT_OK_AND_ASSIGN(ixia_ref_pair,
                       SetUpIxiaTraffic({ingress_link}, *testbed_, kPacketsNum,
                                        kPacketsPerSecond, pkt_size));

  std::string sflow_result;
  {
    // Start sflowtool on SUT.
    ASSERT_OK_AND_ASSIGN(
        std::thread sflow_tool_thread,
        RunSflowCollectorForNSecs(
            *ssh_client_, testbed_->Sut().ChassisName(),
            kSflowtoolLineFormatTemplate,
            /*sflowtool_runtime=*/kPacketsNum / kPacketsPerSecond + 30,
            sflow_result));

    // Wait for sflowtool to finish.
    absl::Cleanup clean_up([&sflow_tool_thread] {
      if (sflow_tool_thread.joinable()) {
        sflow_tool_thread.join();
      }
    });

    // Send packets from Ixia to SUT.
    ASSERT_OK(SendSflowTraffic(ixia_ref_pair.first, ixia_ref_pair.second,
                               {ingress_link}, *testbed_, gnmi_stub_.get(),
                               kPacketsNum, kPacketsPerSecond));
  }

  LOG(INFO) << "sFlow samples:\n" << sflow_result;
  VerifySflowResult(sflow_result, ingress_port.port_id,
                    /*output_port=*/std::nullopt, kSourceMac.ToHexString(),
                    kDstMac.ToHexString(), kEtherTypeIpv4,
                    GetSrcIpv4AddrByPortId(ingress_link.port_id),
                    kIpV4Dst.ToString(), pkt_size, kSamplingRateInterval);

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
  testbed_->Environment().SetTestCaseID("70a4e3e1-f3ae-416e-99a7-24f259942981");

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
  // Set up Ixia traffic. ixia_ref_pair would include the traffic reference
  // and topology reference which could be used to send traffic later.
  std::pair<std::vector<std::string>, std::string> ixia_ref_pair;
  ASSERT_OK_AND_ASSIGN(
      ixia_ref_pair,
      SetUpIxiaTraffic({ingress_link}, *testbed_, packets_num, traffic_speed));
  std::string sflow_result;

  absl::Time start_time;
  ASSERT_OK_AND_ASSIGN(auto initial_cpu_counter,
                       ReadCounters("CPU", gnmi_stub_.get()));
  ASSERT_OK_AND_ASSIGN(
      auto initial_queue_counter,
      pins_test::GetGnmiQueueCounters("CPU", /*queue=*/"NC1", *gnmi_stub_));

  // 1. Start sflowtool on SUT.
  // 2. Send packets from Ixia to SUT.
  // 3. Wait for sflowtool to finish.
  {
    ASSERT_OK_AND_ASSIGN(
        std::thread sflow_tool_thread,
        RunSflowCollectorForNSecs(
            *GetParam().ssh_client, testbed_->Sut().ChassisName(),
            kSflowtoolLineFormatTemplate,
            /*sflowtool_runtime=*/
            packets_num / traffic_speed + 30, sflow_result));

    absl::Cleanup clean_up([&sflow_tool_thread] {
      if (sflow_tool_thread.joinable()) {
        sflow_tool_thread.join();
      }
    });

    start_time = absl::Now();
    ASSERT_OK(SendSflowTraffic(ixia_ref_pair.first, ixia_ref_pair.second,
                               {ingress_link}, *testbed_, gnmi_stub_.get(),
                               packets_num, traffic_speed));
  }

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
      pins_test::GetGnmiQueueCounters("CPU", /*queue=*/"NC1", *gnmi_stub_));
  auto delta_queue_counter = final_queue_counter - initial_queue_counter;
  LOG(INFO) << "CPU NC1 queue counter delta:\n"
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
  EXPECT_EQ(num_packets_punted, packets_num) << absl::StreamFormat(
      "Expected punted packets: %d. Actually punted packets: %d.", packets_num,
      num_packets_punted);

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
  testbed_->Environment().SetTestCaseID("d1e8ae2a-0595-4b33-9743-7dbff8eaf48a");

  const int packet_size = GetParam().packet_size,
            sample_size = GetParam().sample_size;
  ASSERT_NE(packet_size, 0);
  ASSERT_NE(sample_size, 0);
  // ixia_ref_pair would include the traffic reference and topology reference
  // which could be used to send traffic later.
  std::pair<std::vector<std::string>, std::string> ixia_ref_pair;
  ASSERT_OK(SetSflowSamplingSize(gnmi_stub_.get(), sample_size));
  const IxiaLink& ingress_link = ready_links_[0];

  // Set up Ixia traffic.
  ASSERT_OK_AND_ASSIGN(ixia_ref_pair,
                       SetUpIxiaTraffic({ingress_link}, *testbed_, kPacketsNum,
                                        kPacketsPerSecond, packet_size));

  // Start sflowtool on SUT.
  std::string sflow_result;
  {
    // Start sflowtool on SUT.
    ASSERT_OK_AND_ASSIGN(
        std::thread sflow_tool_thread,
        RunSflowCollectorForNSecs(
            *ssh_client_, testbed_->Sut().ChassisName(),
            kSflowtoolFullFormatTemplate,
            /*sflowtool_runtime=*/kPacketsNum / kPacketsPerSecond + 30,
            sflow_result));

    // Wait for sflowtool to finish.
    absl::Cleanup clean_up([&sflow_tool_thread] {
      if (sflow_tool_thread.joinable()) {
        sflow_tool_thread.join();
      }
    });

    // Send packets from Ixia to SUT.
    ASSERT_OK(SendSflowTraffic(ixia_ref_pair.first, ixia_ref_pair.second,
                               {ingress_link}, *testbed_, gnmi_stub_.get(),
                               kPacketsNum, kPacketsPerSecond));
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
  testbed_->Environment().SetTestCaseID("a143121e-c90f-4892-bd6b-897c3d9f9ff3");

  const IxiaLink& ingress_link = ready_links_[0];
  const int sample_rate = GetParam().sample_rate;
  ASSERT_GT(sample_rate, 0);
  const int64_t traffic_rate = sample_rate * 2;
  // Run 300s.
  const int64_t packets_num = sample_rate * 600;
  const int pkt_size = 500;

  ASSERT_OK(SetSflowIngressSamplingRate(
      gnmi_stub_.get(), ingress_link.sut_interface, sample_rate));

  // ixia_ref_pair would include the traffic reference and topology reference
  // which could be used to send traffic later.
  std::pair<std::vector<std::string>, std::string> ixia_ref_pair;
  // Set up Ixia traffic.
  ASSERT_OK_AND_ASSIGN(ixia_ref_pair,
                       SetUpIxiaTraffic({ingress_link}, *testbed_, packets_num,
                                        traffic_rate, pkt_size));

  std::string sflow_result;
  {
    // Start sflowtool on SUT.
    ASSERT_OK_AND_ASSIGN(
        std::thread sflow_tool_thread,
        RunSflowCollectorForNSecs(
            *ssh_client_, testbed_->Sut().ChassisName(),
            kSflowtoolLineFormatTemplate,
            /*sflowtool_runtime=*/packets_num / traffic_rate + 30,
            sflow_result));

    // Wait for sflowtool to finish.
    absl::Cleanup clean_up([&sflow_tool_thread] {
      if (sflow_tool_thread.joinable()) {
        sflow_tool_thread.join();
      }
    });

    // Send packets from Ixia to SUT.
    ASSERT_OK(SendSflowTraffic(ixia_ref_pair.first, ixia_ref_pair.second,
                               {ingress_link}, *testbed_, gnmi_stub_.get(),
                               packets_num, traffic_rate));
  }

  EXPECT_OK(testbed_->Environment().StoreTestArtifact(
      absl::Substitute("sflow_result_sampling_rate_$0_result.txt", sample_rate),
      sflow_result));
  VerifySflowResult(sflow_result, ingress_link.port_id,
                    /*output_port=*/std::nullopt, kSourceMac.ToHexString(),
                    kDstMac.ToHexString(), kEtherTypeIpv4,
                    GetSrcIpv4AddrByPortId(ingress_link.port_id),
                    kIpV4Dst.ToString(), pkt_size, sample_rate);

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
  testbed_->Environment().SetTestCaseID("58653895-219a-4b9e-b6af-03f6a33b5959");

  const IxiaLink& ingress_link = ready_links_[0];

  absl::flat_hash_map<std::string, bool> sflow_interfaces;
  ASSERT_OK_AND_ASSIGN(sflow_interfaces, GetSflowInterfacesFromSut(*testbed_));
  absl::flat_hash_set<std::string> sflow_enabled_interfaces;
  for (const auto& [name, enabled] : sflow_interfaces) {
    if (enabled) {
      sflow_enabled_interfaces.insert(name);
    }
  }

  // Read initial sample rate from testbed.
  absl::flat_hash_map<std::string, int> initial_interfaces_to_sample_rate;
  ASSERT_OK_AND_ASSIGN(initial_interfaces_to_sample_rate,
                       GetSflowSamplingRateForInterfaces(
                           gnmi_stub_.get(), sflow_enabled_interfaces));

  // Set up Ixia traffic.
  // ixia_ref_pair would include the traffic reference and topology reference
  // which could be used to send traffic later.
  std::pair<std::vector<std::string>, std::string> ixia_ref_pair;
  ASSERT_OK_AND_ASSIGN(ixia_ref_pair,
                       SetUpIxiaTraffic({ingress_link}, *testbed_, 0, 0));
  const std::string traffic_ref = ixia_ref_pair.first[0],
                    topology_ref = ixia_ref_pair.second;

  const int interface_sample_rate = kSamplingRateInterval;
  // Setup Ixia for normal traffic speed - it would generate 10
  // samples/sec.
  int64_t traffic_rate = 10 * interface_sample_rate;
  ASSERT_OK(SetIxiaTrafficParams(traffic_ref,
                                 traffic_rate * kBackOffThresholdDuration,
                                 traffic_rate, *testbed_));

  // Start sflowtool on SUT.
  std::string sflow_result;
  {
    ASSERT_OK_AND_ASSIGN(
        std::thread sflow_tool_thread,
        RunSflowCollectorForNSecs(
            *ssh_client_, testbed_->Sut().ChassisName(),
            kSflowtoolLineFormatTemplate,
            /*sflowtool_runtime=*/kBackOffThresholdDuration + 30,
            sflow_result));

    // Wait for sflowtool to finish.
    absl::Cleanup clean_up([&sflow_tool_thread] {
      if (sflow_tool_thread.joinable()) {
        sflow_tool_thread.join();
      }
    });

    // Send packets from Ixia to SUT.
    ASSERT_OK(SendSflowTraffic(
        std::vector<std::string>{std::string(traffic_ref)}, topology_ref,
        {ingress_link}, *testbed_, gnmi_stub_.get(),
        /*pkt_count=*/traffic_rate * kBackOffThresholdDuration, traffic_rate));
  }

  ASSERT_OK(testbed_->Environment().StoreTestArtifact(
      absl::StrCat("sFlow_samples_traffic_rate_", traffic_rate,
                   "_before_backoff.txt"),
      sflow_result));

  std::function<bool(int, int)> is_eq = [](int a, int b) { return a == b; };
  std::function<bool(int, int)> is_gt = [](int a, int b) { return a > b; };
  // Verify that sample rate from sflowtool result is the same as initial.
  ASSERT_OK(IsExpectedSampleRateFromSamples(sflow_result, interface_sample_rate,
                                            is_eq));
  // Verify that sample rate on all interfaces is still the initial value.
  // TODO: Enable this check after b/284911076 is merged in
  // release.
  // ASSERT_OK(IsExpectedSamplingRateFromGnmi(
  //     gnmi_stub_.get(), sflow_enabled_interfaces,
  //     initial_interfaces_to_sample_rate, is_eq));

  // Setup Ixia for higher traffic speed to trigger sFlow backoff - it would
  // generate kBackOffThresholdSamples per sec.
  traffic_rate = kBackOffThresholdSamples * interface_sample_rate;
  ASSERT_OK(SetIxiaTrafficParams(traffic_ref,
                                 traffic_rate * kBackOffThresholdDuration,
                                 traffic_rate, *testbed_));

  // Start sflowtool on SUT.
  {
    ASSERT_OK_AND_ASSIGN(
        std::thread sflow_tool_thread,
        RunSflowCollectorForNSecs(
            *ssh_client_, testbed_->Sut().ChassisName(),
            kSflowtoolLineFormatTemplate,
            /*sflowtool_runtime=*/kBackOffThresholdDuration + 30,
            sflow_result));

    // Wait for sflowtool to finish.
    absl::Cleanup clean_up([&sflow_tool_thread] {
      if (sflow_tool_thread.joinable()) {
        sflow_tool_thread.join();
      }
    });

    // Send packets from Ixia to SUT.
    ASSERT_OK(SendSflowTraffic(
        std::vector<std::string>{std::string(traffic_ref)}, topology_ref,
        {ingress_link}, *testbed_, gnmi_stub_.get(),
        /*pkt_count=*/traffic_rate * kBackOffThresholdDuration, traffic_rate));
  }

  ASSERT_OK(testbed_->Environment().StoreTestArtifact(
      absl::StrCat("sFlow_samples_traffic_rate_", traffic_rate,
                   "_triggering_backoff.txt"),
      sflow_result));

  // Verify that sample rate from sflowtool result is greater.
  ASSERT_OK(IsExpectedSampleRateFromSamples(sflow_result, interface_sample_rate,
                                            is_gt));
  // Verify that sample rate on all interfaces is greater.
  // TODO: Enable this check after b/284911076 is merged in
  // release.
  // ASSERT_OK(IsExpectedSamplingRateFromGnmi(
  //     gnmi_stub_.get(), sflow_enabled_interfaces,
  //     initial_interfaces_to_sample_rate, is_gt));

  // Use a normal traffic speed, sample rate should remain as greater.
  traffic_rate = 10 * interface_sample_rate;
  ASSERT_OK(SetIxiaTrafficParams(traffic_ref,
                                 traffic_rate * kBackOffThresholdDuration,
                                 traffic_rate, *testbed_));

  {
    // Start sflowtool on SUT.
    ASSERT_OK_AND_ASSIGN(
        std::thread sflow_tool_thread,
        RunSflowCollectorForNSecs(
            *ssh_client_, testbed_->Sut().ChassisName(),
            kSflowtoolLineFormatTemplate,
            /*sflowtool_runtime=*/kBackOffThresholdDuration + 30,
            sflow_result));

    // Wait for sflowtool to finish.
    absl::Cleanup clean_up([&sflow_tool_thread] {
      if (sflow_tool_thread.joinable()) {
        sflow_tool_thread.join();
      }
    });

    // Send packets from Ixia to SUT.
    ASSERT_OK(SendSflowTraffic(
        std::vector<std::string>{std::string(traffic_ref)}, topology_ref,
        {ingress_link}, *testbed_, gnmi_stub_.get(),
        /*pkt_count=*/traffic_rate * kBackOffThresholdDuration, traffic_rate));
  }

  ASSERT_OK(testbed_->Environment().StoreTestArtifact(
      absl::StrCat("sFlow_samples_traffic_rate_", traffic_rate,
                   "_after_backoff.txt"),
      sflow_result));

  // Verify that sample rate from sflowtool result is still greater.
  EXPECT_OK(IsExpectedSampleRateFromSamples(sflow_result, interface_sample_rate,
                                            is_gt));
  // Verify that sample rate on all interfaces is still greater.
  // TODO: Enable this check after b/284911076 is merged in
  // release.
  // EXPECT_OK(IsExpectedSamplingRateFromGnmi(
  //     gnmi_stub_.get(), sflow_enabled_interfaces,
  //     initial_interfaces_to_sample_rate, is_gt));
}

namespace {

constexpr int kInbandSamplingRate = 256;
constexpr int kInbandTrafficPps = 1000;
constexpr absl::string_view kClusterMacAddr = "00:1a:11:17:5f:80";

// Sends `num_packets` packets at a rate of `traffic_speed`. The packet
// ipv4_source field changes based on `port_id`.
absl::Status SendNPacketsFromSwitch(
    int num_packets, int traffic_speed, int port_id,
    const pdpi::IrP4Info& ir_p4info, pdpi::P4RuntimeSession& p4_session,
    thinkit::TestEnvironment& test_environment) {
  const absl::Time start_time = absl::Now();
  auto packet = gutil::ParseProtoOrDie<packetlib::Packet>(
      absl::Substitute(R"pb(
                         headers {
                           ethernet_header {
                             ethernet_destination: "$0"
                             ethernet_source: "00:01:02:03:04:05"
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
                             ipv4_source: "$1"
                             ipv4_destination: "$2"
                           }
                         }
                         payload: "Test packet for Sflow Inband testing")pb",
                       kDstMac.ToString(), GetSrcIpv4AddrByPortId(port_id),
                       kIpV4Dst.ToString()));
  ASSIGN_OR_RETURN(std::string raw_packet, SerializePacket(packet));
  for (int i = 0; i < num_packets; i++) {
    // Rate limit to traffic_speed packets per second.
    RETURN_IF_ERROR(InjectEgressPacket(
        absl::StrCat(port_id), raw_packet, ir_p4info, &p4_session,
        /*packet_delay=*/absl::Milliseconds(1000 / traffic_speed)));
  }

  LOG(INFO) << "Sent " << num_packets << " packets in "
            << (absl::Now() - start_time) << " for port: " << port_id << "."
            << " Packets source ip: " << GetSrcIpv4AddrByPortId(port_id);
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
  ASSIGN_OR_RETURN(*pi_request.add_updates(),
                   NeighborTableUpdate(ir_p4info, p4::v1::Update::INSERT,
                                       rif_id, neighbor_id, kClusterMacAddr));
  const std::string nexthop_id = absl::StrCat("nexthop-", port_id);
  ASSIGN_OR_RETURN(*pi_request.add_updates(),
                   NexthopTableUpdate(ir_p4info, p4::v1::Update::INSERT,
                                      nexthop_id, rif_id, neighbor_id));
  RETURN_IF_ERROR(
      pdpi::SetMetadataAndSendPiWriteRequest(&p4_session, pi_request));
  return nexthop_id;
}

// Sends `num_packets` ICMP packets via `port` at `traffic_speed` rate.
absl::Status SendNIcmpPacketsFromSwitch(
    int num_packets, int traffic_speed, Port port, absl::string_view dst_ip,
    const pdpi::IrP4Info& ir_p4info, pdpi::P4RuntimeSession& p4_session,
    thinkit::TestEnvironment& test_environment) {
  auto icmp_packet = gutil::ParseProtoOrDie<packetlib::Packet>(absl::Substitute(
      R"pb(
        headers {
          ethernet_header {
            ethernet_destination: "$0"
            ethernet_source: "c2:00:51:fa:00:00"
            ethertype: "0x86dd"
          }
        }
        headers {
          ipv6_header {
            dscp: "0x00"
            ecn: "0x0"
            flow_label: "0x00000"
            next_header: "0x3a"
            hop_limit: "0x40"
            ipv6_source: "2001:db8:0:12::1"
            ipv6_destination: "$1"
          }
        }
        headers {
          icmp_header { type: "0x80" code: "0x00" rest_of_header: "0x110d0000" }
        }
        payload: "ICMPv6 packet without computed fields"
      )pb",
      kClusterMacAddr, dst_ip));
  const absl::Time start_time = absl::Now();
  ASSIGN_OR_RETURN(std::string raw_packet, SerializePacket(icmp_packet));
  for (int i = 0; i < num_packets; i++) {
    // Rate limit to traffic_speed packets per second.
    RETURN_IF_ERROR(InjectEgressPacket(
        absl::StrCat(port.port_id), raw_packet, ir_p4info, &p4_session,
        /*packet_delay=*/absl::Milliseconds(1000 / traffic_speed)));
  }

  LOG(INFO) << "Sent " << num_packets << " ICMP packets in "
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

}  // namespace

void SflowMirrorTestFixture::SetUp() {
  ASSERT_NE(GetParam().ssh_client, nullptr);
  GetParam().testbed_interface->SetUp();
  thinkit::MirrorTestbed& testbed =
      GetParam().testbed_interface->GetMirrorTestbed();

  // Push gNMI config to SUT switch.
  const std::string& sut_gnmi_config = GetParam().sut_gnmi_config;
  ASSERT_OK(testbed.Environment().StoreTestArtifact("sut_gnmi_config.txt",
                                                    sut_gnmi_config));
  ASSERT_OK_AND_ASSIGN(sut_p4_session_,
                       pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
                           testbed.Sut(), sut_gnmi_config, GetP4Info()));
  ASSERT_OK_AND_ASSIGN(ir_p4_info_, pdpi::CreateIrP4Info(GetP4Info()));

  // Push gNMI config to control switch.
  const std::string& control_gnmi_config = GetParam().control_gnmi_config;
  ASSERT_OK(testbed.Environment().StoreTestArtifact("control_gnmi_config.txt",
                                                    control_gnmi_config));
  ASSERT_OK_AND_ASSIGN(
      control_p4_session_,
      pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
          testbed.ControlSwitch(), control_gnmi_config, GetP4Info()));

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
                     /*prefix=*/"pretest_", testbed.Environment());
}

void SflowMirrorTestFixture::TearDown() {
  auto& testbed = GetParam().testbed_interface->GetMirrorTestbed();
  CollectSflowDebugs(GetParam().ssh_client, testbed.Sut().ChassisName(),
                     /*prefix=*/"posttest_", testbed.Environment());
  if (sut_p4_session_ != nullptr) {
    EXPECT_OK(OutputTableEntriesToArtifact(
        *sut_p4_session_, testbed.Environment(),
        /*artifact_name=*/"posttest_SUT_table_entries.txt"));
  }
  if (control_p4_session_ != nullptr) {
    EXPECT_OK(OutputTableEntriesToArtifact(
        *control_p4_session_, testbed.Environment(),
        /*artifact_name=*/"posttest_control_table_entries.txt"));
  }

  // Restore sFlow config on SUT.
  ASSERT_OK_AND_ASSIGN(auto sflow_enabled,
                       IsSflowConfigEnabled(GetParam().sut_gnmi_config));
  ASSERT_OK(SetSflowConfigEnabled(sut_gnmi_stub_.get(), sflow_enabled));
  ASSERT_OK(
      pins_test::PushGnmiConfig(testbed.Sut(), GetParam().sut_gnmi_config));
  // Restores control switch config.
  ASSERT_OK(pins_test::PushGnmiConfig(testbed.ControlSwitch(),
                                      GetParam().control_gnmi_config));

  if (sut_p4_session_ != nullptr) {
    EXPECT_OK(pdpi::ClearTableEntries(sut_p4_session_.get()));
    EXPECT_OK(sut_p4_session_->Finish());
  }
  if (control_p4_session_ != nullptr) {
    EXPECT_OK(pdpi::ClearTableEntries(control_p4_session_.get()));
    EXPECT_OK(control_p4_session_->Finish());
  }
  GetParam().testbed_interface->TearDown();
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
  thinkit::MirrorTestbed& testbed =
      GetParam().testbed_interface->GetMirrorTestbed();
  testbed.Environment().SetTestCaseID("3948ef62-67d9-42e2-8cc6-30dc10cb382f");

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
  collector_address_and_port.push_back({collector_ipv6, kSflowCollectorPort});
  collector_address_and_port.push_back(
      {kLocalLoopbackIpv6, kSflowCollectorPort});

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
  ASSERT_OK(SetSwitchVrfForAllPackets(*sut_p4_session_, GetIrP4Info(), vrf_id));

  ASSERT_OK_AND_ASSIGN(std::string next_hop_id,
                       ProgramNextHops(*sut_p4_session_, GetIrP4Info(),
                                       absl::StrCat(inband_port.port_id)));
  ASSERT_OK(ProgramRoutesForIpv6(*sut_p4_session_, GetIrP4Info(), vrf_id,
                                 collector_ipv6, next_hop_id));

  // 1. Start sflowtool on control switch.
  // 2. Send traffic from control switch.
  // 3. Get sflowtool result and counters stats.
  std::string control_sflow_result, sut_sflow_result;
  {
    ASSERT_OK_AND_ASSIGN(
        std::thread control_sflowtool_thread,
        RunSflowCollectorForNSecs(
            *GetParam().ssh_client, testbed.ControlSwitch().ChassisName(),
            kSflowtoolLineFormatTemplate,
            /*sflowtool_runtime=*/packets_num / kInbandTrafficPps + 30,
            control_sflow_result));
    ASSERT_OK_AND_ASSIGN(
        std::thread sut_sflowtool_thread,
        RunSflowCollectorForNSecs(
            *GetParam().ssh_client, testbed.Sut().ChassisName(),
            kSflowtoolLineFormatTemplate,
            /*sflowtool_runtime=*/packets_num / kInbandTrafficPps + 30,
            sut_sflow_result));

    ASSERT_OK_AND_ASSIGN(auto initial_queue_counter,
                         pins_test::GetGnmiQueueCounters("CPU", kSflowQueueName,
                                                         *sut_gnmi_stub_));
    ASSERT_OK_AND_ASSIGN(
        auto sut_initial_in_band_port_counter,
        ReadCounters(inband_port.interface_name, sut_gnmi_stub_.get()));
    ASSERT_OK_AND_ASSIGN(auto control_gnmi_stub,
                         testbed.ControlSwitch().CreateGnmiStub());
    ASSERT_OK_AND_ASSIGN(
        auto control_initial_in_band_port_counter,
        ReadCounters(inband_port.interface_name, control_gnmi_stub.get()));
    ASSERT_OK_AND_ASSIGN(auto control_initial_cpu_counter,
                         ReadCounters("CPU", control_gnmi_stub.get()));

    absl::Time start_time = absl::Now();

    // Wait for sflowtool to finish and read counter data.
    absl::Cleanup clean_up([this, initial_queue_counter, start_time,
                            control_gnmi_stub_raw = control_gnmi_stub.get(),
                            &sut_initial_in_band_port_counter,
                            &control_initial_in_band_port_counter,
                            &control_initial_cpu_counter, &inband_port,
                            &control_sflowtool_thread, &sut_sflowtool_thread] {
      if (control_sflowtool_thread.joinable()) {
        control_sflowtool_thread.join();
      }
      if (sut_sflowtool_thread.joinable()) {
        sut_sflowtool_thread.join();
      }

      // Show counter data.
      ASSERT_OK_AND_ASSIGN(
          auto final_queue_counter,
          pins_test::GetGnmiQueueCounters("CPU", kSflowQueueName,
                                          *(this->sut_gnmi_stub_)));
      LOG(INFO) << "CPU " << kSflowQueueName << " queue counter delta:\n"
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

    // Send packets from control switch.
    ASSERT_OK(SendNPacketsFromSwitch(
        packets_num, kInbandTrafficPps, traffic_port.port_id, GetIrP4Info(),
        *control_p4_session_, testbed.Environment()));
  }

  EXPECT_OK(testbed.Environment().StoreTestArtifact("control_sflow_result.txt",
                                                    control_sflow_result));
  EXPECT_OK(testbed.Environment().StoreTestArtifact("sut_sflow_result.txt",
                                                    sut_sflow_result));

  // TODO: TestInbandPathToSflowCollector should have a strict
  // check on the sflow samples received on control switch.
  EXPECT_FALSE(control_sflow_result.empty())
      << "No samples on " << traffic_port.interface_name;
}

// 1. Pick an interface and let control switch send some traffic via this
// interface.
// 2. Start sflowtool and tcpdump on SUT.
// 3. Verify on SUT that samples are generated and tcpdump result has the
// expected DSCP value.
TEST_P(SflowMirrorTestFixture, TestSflowDscpValue) {
  thinkit::MirrorTestbed& testbed =
      GetParam().testbed_interface->GetMirrorTestbed();
  testbed.Environment().SetTestCaseID("38694bb8-2a82-4379-8b85-96dcda824a14");

  const int packets_num = 10000;

  ASSERT_OK_AND_ASSIGN(Port traffic_port,
                       GetUnusedUpPort(*sut_gnmi_stub_, /*used_port=*/""));

  absl::flat_hash_map<std::string, bool> sflow_enabled_interfaces{
      {traffic_port.interface_name, true}};
  std::vector<std::pair<std::string, int>> collector_address_and_port{
      {kLocalLoopbackIpv6, kSflowCollectorPort}};
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

  std::string sflow_result, tcpdump_result;
  {
    // Run sflowtool and tcpdump on SUT.
    const int runtime_secs = packets_num / kInbandTrafficPps + 30;
    ASSERT_OK_AND_ASSIGN(std::thread sflow_tool_thread,
                         RunSflowCollectorForNSecs(*GetParam().ssh_client,
                                                   testbed.Sut().ChassisName(),
                                                   kSflowtoolLineFormatTemplate,
                                                   runtime_secs, sflow_result));
    ASSERT_OK_AND_ASSIGN(
        std::thread tcpdump_thread,
        CaptureTcpdumpForNPackets(
            *GetParam().ssh_client, testbed.Sut().ChassisName(),
            /*packets_count=*/5, runtime_secs, tcpdump_result));

    ASSERT_OK_AND_ASSIGN(auto initial_queue_counter,
                         pins_test::GetGnmiQueueCounters("CPU", kSflowQueueName,
                                                         *sut_gnmi_stub_));
    absl::Time start_time = absl::Now();

    // Wait for sflowtool and tcpdump to finish and read counter data.
    absl::Cleanup clean_up([this, initial_queue_counter, start_time,
                            &sflow_tool_thread, &tcpdump_thread] {
      if (sflow_tool_thread.joinable()) {
        sflow_tool_thread.join();
      }
      if (tcpdump_thread.joinable()) {
        tcpdump_thread.join();
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

    // Send packets from control switch.
    ASSERT_OK(SendNPacketsFromSwitch(
        packets_num, kInbandTrafficPps, traffic_port.port_id, GetIrP4Info(),
        *control_p4_session_, testbed.Environment()));
  }
  EXPECT_OK(testbed.Environment().StoreTestArtifact("tcpdump_result.txt",
                                                    tcpdump_result));
  ASSERT_THAT(ExtractTosFromTcpdumpResult(tcpdump_result),
              IsOkAndHolds(kSflowOutPacketsTos));
  EXPECT_OK(testbed.Environment().StoreTestArtifact("sflow_result.txt",
                                                    sflow_result));
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
  testbed.Environment().SetTestCaseID("03bdb9da-387a-4256-9323-60d4503ce3c0");

  const int packets_num = 10000;
  ASSERT_OK_AND_ASSIGN(
      auto port_id_per_port_name,
      pins_test::GetAllUpInterfacePortIdsByName(*sut_gnmi_stub_));
  ASSERT_GE(port_id_per_port_name.size(), 0) << "No up interfaces.";
  absl::flat_hash_map<std::string, bool> sflow_enabled_interfaces;
  for (const auto& [interface_name, unused] : port_id_per_port_name) {
    sflow_enabled_interfaces[interface_name] = true;
  }

  std::vector<std::pair<std::string, int>> collector_address_and_port{
      {kLocalLoopbackIpv6, kSflowCollectorPort}};
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
        RunSflowCollectorForNSecs(*GetParam().ssh_client,
                                  testbed.Sut().ChassisName(),
                                  kSflowtoolLineFormatTemplate,
                                  /*sflowtool_runtime=*/
                                  (packets_num / kInbandTrafficPps + 3) *
                                          port_id_per_port_name.size() +
                                      20,
                                  sflow_result));
    ASSERT_OK_AND_ASSIGN(auto initial_queue_counter,
                         pins_test::GetGnmiQueueCounters("CPU", kSflowQueueName,
                                                         *sut_gnmi_stub_));
    absl::Time start_time = absl::Now();

    // Wait for sflowtool to finish and read counter data.
    absl::Cleanup clean_up(
        [this, initial_queue_counter, start_time, &sflow_tool_thread] {
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

    // Send packets from control switch on all UP interfaces.
    for (const auto& [unused, port_id_str] : port_id_per_port_name) {
      int port_id;
      ASSERT_TRUE(absl::SimpleAtoi(port_id_str, &port_id))
          << port_id_str << " is not a valid port id.";
      ASSERT_OK(SendNPacketsFromSwitch(packets_num, kInbandTrafficPps, port_id,
                                       GetIrP4Info(), *control_p4_session_,
                                       testbed.Environment()));
    }
  }

  for (const auto& [interface_name, port_id_str] : port_id_per_port_name) {
    int port_id;
    ASSERT_TRUE(absl::SimpleAtoi(port_id_str, &port_id))
        << port_id_str << " is not a valid port id.";
    const int sample_count = GetSflowSamplesOnSut(sflow_result, port_id);
    SflowResult result = SflowResult{
        .sut_interface = interface_name,
        .packets = packets_num,
        .sampling_rate = kInbandSamplingRate,
        .expected_samples = packets_num / kInbandSamplingRate,
        .actual_samples = sample_count,
    };
    LOG(INFO) << "------ Test result ------\n" << result.DebugString();
    EXPECT_GT(sample_count, 0)
        << "No samples found for " << interface_name
        << ". Packets source ip: " << GetSrcIpv4AddrByPortId(port_id);
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
TEST_P(SflowMirrorTestFixture, TestSamplingWorksAfterReboot) {
  GetParam().testbed_interface->ExpectLinkFlaps();

  thinkit::MirrorTestbed& testbed =
      GetParam().testbed_interface->GetMirrorTestbed();
  testbed.Environment().SetTestCaseID("6cd622a1-2d95-4e07-9c7d-77a2faad4bc0");

  ASSERT_OK_AND_ASSIGN(
      auto port_id_per_port_name,
      pins_test::GetAllUpInterfacePortIdsByName(*sut_gnmi_stub_));
  ASSERT_GE(port_id_per_port_name.size(), 5)
      << "Not enough up interfaces. Need 5. Actual up interfaces: "
      << port_id_per_port_name.size() << ".";
  absl::flat_hash_map<std::string, bool> sflow_enabled_interfaces;
  // We do not want to send traffic on all ports since that would cost a lot of
  // time. Send traffic on 5 ports would be enough in our reboot test since
  // other test cases already cover sampling on all interfaces.
  std::vector<std::pair<std::string, std::string>>
      traffic_interfaces_and_port_ids;
  for (const auto& [interface_name, port_id] : port_id_per_port_name) {
    sflow_enabled_interfaces[interface_name] = true;
    traffic_interfaces_and_port_ids.push_back({interface_name, port_id});
    if (sflow_enabled_interfaces.size() >= 5) {
      break;
    }
  }

  std::vector<std::pair<std::string, int>> collector_address_and_port{
      {kLocalLoopbackIpv6, kSflowCollectorPort}};
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
  // Start sflowtool on SUT.
  std::string sflow_result;
  {
    ASSERT_OK_AND_ASSIGN(
        std::thread sflow_tool_thread,
        RunSflowCollectorForNSecs(
            *GetParam().ssh_client, testbed.Sut().ChassisName(),
            kSflowtoolLineFormatTemplate,
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
    for (const auto& [unused, port_id_str] : traffic_interfaces_and_port_ids) {
      int port_id;
      ASSERT_TRUE(absl::SimpleAtoi(port_id_str, &port_id))
          << port_id_str << " is not a valid port id.";
      ASSERT_OK(SendNPacketsFromSwitch(num_packets, kInbandTrafficPps, port_id,
                                       GetIrP4Info(), *control_p4_session_,
                                       testbed.Environment()));
    }
  }

  // Validate sflowtool result.
  for (const auto& [interface_name, port_id_str] :
       traffic_interfaces_and_port_ids) {
    int port_id;
    ASSERT_TRUE(absl::SimpleAtoi(port_id_str, &port_id))
        << port_id_str << " is not a valid port id.";
    const int sample_count = GetSflowSamplesOnSut(sflow_result, port_id);
    SflowResult result = SflowResult{
        .sut_interface = interface_name,
        .packets = num_packets,
        .sampling_rate = kInbandSamplingRate,
        .expected_samples = num_packets / kInbandSamplingRate,
        .actual_samples = sample_count,
    };
    LOG(INFO) << "------ Test result ------\n" << result.DebugString();
    EXPECT_GT(sample_count, 0)
        << "No samples found for " << interface_name
        << ". Packets source ip: " << GetSrcIpv4AddrByPortId(port_id);
  }

  EXPECT_OK(testbed.Environment().StoreTestArtifact("sflow_result.txt",
                                                    sflow_result));

  // Reboot the switch and wait for interfaces to be up.
  if (sut_p4_session_ != nullptr) {
    EXPECT_OK(sut_p4_session_->Finish());
    sut_p4_session_ = nullptr;
  }
  pins_test::TestGnoiSystemColdReboot(testbed.Sut());
  std::vector<std::string> interface_names;
  for (const auto& [interface_name, unused] : sflow_enabled_interfaces) {
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

  {
    // Start sflowtool on SUT.
    ASSERT_OK_AND_ASSIGN(
        std::thread sflow_tool_thread,
        RunSflowCollectorForNSecs(
            *GetParam().ssh_client, testbed.Sut().ChassisName(),
            kSflowtoolLineFormatTemplate,
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
    for (const auto& [unused, port_id_str] : traffic_interfaces_and_port_ids) {
      int port_id;
      ASSERT_TRUE(absl::SimpleAtoi(port_id_str, &port_id))
          << port_id_str << " is not a valid port id.";
      ASSERT_OK(SendNPacketsFromSwitch(num_packets, kInbandTrafficPps, port_id,
                                       GetIrP4Info(), *control_p4_session_,
                                       testbed.Environment()));
    }
  }

  EXPECT_OK(testbed.Environment().StoreTestArtifact(
      "sflow_result_after_reboot.txt", sflow_result));

  // Validate sflowtool result.
  for (const auto& [interface_name, port_id_str] :
       traffic_interfaces_and_port_ids) {
    int port_id;
    ASSERT_TRUE(absl::SimpleAtoi(port_id_str, &port_id))
        << port_id_str << " is not a valid port id.";
    const int sample_count = GetSflowSamplesOnSut(sflow_result, port_id);
    SflowResult result = SflowResult{
        .sut_interface = interface_name,
        .packets = num_packets,
        .sampling_rate = kInbandSamplingRate,
        .expected_samples = num_packets / kInbandSamplingRate,
        .actual_samples = sample_count,
    };
    LOG(INFO) << "------ Test result ------\n" << result.DebugString();
    EXPECT_GT(sample_count, 0)
        << "No samples found for " << interface_name
        << ". Packets source ip: " << GetSrcIpv4AddrByPortId(port_id);
  }
}

// 1. Set sFlow config on SUT for one interface.
// 2. Set SUT sFlow collector as kLocalLoopbackIpv6.
// 3. Send ICMP traffic from control switch to SUT on this interface.
// 4. Validate the packets get punted and sFlowtool has expected result.
TEST_P(SflowMirrorTestFixture, TestIp2MePacketsAreSampledAndPunted) {
  thinkit::MirrorTestbed& testbed =
      GetParam().testbed_interface->GetMirrorTestbed();
  testbed.Environment().SetTestCaseID("7f765661-840e-4913-b210-8bbf9d5a0e8f");

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

  absl::flat_hash_map<std::string, bool> sflow_enabled_interfaces;
  for (const auto& [interface_name, unused] : port_id_per_port_name) {
    sflow_enabled_interfaces[interface_name] = true;
  }

  std::vector<std::pair<std::string, int>> collector_address_and_port{
      {kLocalLoopbackIpv6, kSflowCollectorPort}};
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
            kSflowtoolLineFormatTemplate,
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

    ASSERT_OK(SendNIcmpPacketsFromSwitch(
        packets_num, traffic_speed, traffic_port, agent_address_, GetIrP4Info(),
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

  EXPECT_OK(testbed.Environment().StoreTestArtifact("sflow_result.txt",
                                                    sflow_result));
  ASSERT_FALSE(sflow_result.empty())
      << "No samples on " << traffic_port.interface_name;
  std::vector<std::string> sflow_samples = absl::StrSplit(sflow_result, '\n');
  LOG(INFO) << "Received " << sflow_samples.size() << " samples";
  // Check ICMP pkts. ICMP for IPv6  protocol number is 58.
  EXPECT_TRUE(HasSampleForProtocol(sflow_result, /*ip_protocol=*/58));
}

}  // namespace pins
