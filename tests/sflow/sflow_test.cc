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

#include <cmath>
#include <memory>
#include <string>
#include <thread>  // NOLINT
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/synchronization/mutex.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/collections.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/ixia_helper.h"
#include "lib/validator/validator_lib.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/pd.h"
#include "p4_pdpi/string_encodings/decimal_string.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/ssh_client.h"

namespace pins {

namespace {
// Number of packets sent to one port.
constexpr int kPacketsNum = 400000;

// Number of packets sent per second.
constexpr int kPacketsPerSecond = 3000;

// The maximum number of bytes that should be copied from a sampled packet to
// the sFlow datagram
constexpr int kSampleSize = 128;

// Once accumulated data reaches kMaxPacketSize, Sflow would generate an sflow
// packet.
constexpr int kMaxPacketSize = 1400;

// Sflowtool binary name in the collector.
constexpr absl::string_view kSflowToolName = "sflowtool";
constexpr absl::string_view kSflowCommandTemplate =
    "/etc/init.d/sflow-container exec '$0 -l -p 6343 &"
    " pid=$$!; sleep $1; kill -9 $$pid;'";

// IpV4 address for filtering the sflow packet.
constexpr uint32_t kIpV4Src = 0x01020304;  // 1.2.3.4
// Ixia flow details.
constexpr auto kDstMac = netaddr::MacAddress(02, 02, 02, 02, 02, 02);
constexpr auto kSourceMac = netaddr::MacAddress(00, 01, 02, 03, 04, 05);
constexpr auto kIpV4Dst = netaddr::Ipv4Address(192, 168, 10, 1);

// TODO: Parse the sampling rate from config or state path.
constexpr int kSamplingRateInterval = 4000;

// Buffering and software bottlenecks can cause some amount of variance in rate
// measured end to end.
// Level of tolerance for packet rate verification.
// This could be parameterized in future if this is platform dependent.
constexpr double kTolerance = 0.1;

constexpr absl::string_view kSpeed100GB =
    "\"openconfig-if-ethernet:SPEED_100GB\"";
constexpr absl::string_view kSpeed200GB =
    "\"openconfig-if-ethernet:SPEED_200GB\"";

std::string GetSrcIpv4AddrByPortId(const int port_id) {
  return netaddr::Ipv4Address(std::bitset<32>(kIpV4Src + port_id)).ToString();
}

// These are the counters we track in these tests.
struct Counters {
  uint64_t in_pkts;
  uint64_t out_pkts;
  uint64_t in_octets;
  uint64_t out_octets;
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
}

// DeltaCounters - computer delta as change from initial to final counters
Counters DeltaCounters(const Counters& initial, const Counters& final) {
  Counters delta = {};

  delta.in_pkts = final.in_pkts - initial.in_pkts;
  delta.out_pkts = final.out_pkts - initial.out_pkts;
  delta.in_octets = final.in_octets - initial.in_octets;
  delta.out_octets = final.out_octets - initial.out_octets;
  return delta;
}

absl::StatusOr<Counters> ReadCounters(std::string iface,
                                      gnmi::gNMI::StubInterface* gnmi_stub) {
  Counters cnt = {};

  ASSIGN_OR_RETURN(cnt.in_pkts, GetGnmiStat("in-pkts", iface, gnmi_stub));
  ASSIGN_OR_RETURN(cnt.out_pkts, GetGnmiStat("out-pkts", iface, gnmi_stub));
  ASSIGN_OR_RETURN(cnt.in_octets, GetGnmiStat("in-octets", iface, gnmi_stub));
  ASSIGN_OR_RETURN(cnt.out_octets, GetGnmiStat("out-octets", iface, gnmi_stub));
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
                 thinkit::GenericTestbed& testbed, const int pkt_count,
                 const int pkt_rate, const int frame_size = 1000) {
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
  return counters;
}

// Run sflowtool on SUT in a new thread. Returns the thread to let caller to
// wait for the finish.
absl::StatusOr<std::thread> StartSflowCollector(
    thinkit::SSHClient* ssh_client, absl::string_view device_name,
    const int sflowtool_runtime, std::string& sflow_tool_result) {
  std::thread sflow_tool_thread = std::thread(
      [&sflow_tool_result, ssh_client, device_name, sflowtool_runtime]() {
        const std::string ssh_command = absl::Substitute(
            kSflowCommandTemplate, kSflowToolName, sflowtool_runtime);
        LOG(INFO) << "ssh command:" << ssh_command;
        ASSERT_OK_AND_ASSIGN(
            sflow_tool_result,
            ssh_client->RunCommand(
                device_name, ssh_command,
                /*timeout=*/absl::Seconds(sflowtool_runtime + 2)));
      });
  // Sleep to wait sflowtool to start.
  absl::SleepFor(absl::Seconds(5));
  return sflow_tool_thread;
}

// Send packets to SUT and validate packet counters via gNMI.
absl::Status SendSflowTraffic(const std::vector<std::string>& traffic_refs,
                              const std::string& topology_ref,
                              absl::Span<const IxiaLink> ixia_links,
                              thinkit::GenericTestbed& testbed,
                              gnmi::gNMI::StubInterface* gnmi_stub,
                              const int pkt_count, const int pkt_rate) {
  // Send packets to SUT.
  const absl::Time start_time = absl::Now();

  // Read initial counters via GNMI from the SUT
  LOG(INFO) << "Read initial packet counters.";
  ASSIGN_OR_RETURN(std::vector<Counters> initial_in_counters,
                   GetIxiaInterfaceCounters(ixia_links, gnmi_stub));

  RETURN_IF_ERROR(SendNPacketsToSut(
      traffic_refs, topology_ref,
      /*runtime=*/absl::Seconds(std::ceil(1.0f * kPacketsNum / pkt_rate)),
      testbed));

  LOG(INFO) << "Sent " << kPacketsNum << " packets in "
            << (absl::Now() - start_time) << "\n";

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
        << ". Port id: " << ixia_links[i].port_id << ". Sent " << pkt_count
        << ". Received " << delta.in_pkts << ".";
  }

  return absl::OkStatus();
}

int GetSflowSamplesOnSut(const std::string& sflowtool_output,
                         const int port_id) {
  // Every "startDatagram" indicates an sFlow datagram.
  constexpr int kFieldSize = 20, kSrcIpIdx = 9;
  int count = 0;
  for (absl::string_view sflow : absl::StrSplit(sflowtool_output, '\n')) {
    std::vector<absl::string_view> fields = absl::StrSplit(sflow, ',');
    if (fields.size() < kFieldSize) {
      continue;
    }
    // Filter src ip.
    if (fields[kSrcIpIdx] == GetSrcIpv4AddrByPortId(port_id)) {
      count++;
    }
  }
  return count;
}

// Set port speed by configuraing interface/ethernet/config/port-speed value.
absl::Status SetPortSpeed(absl::string_view port_speed, absl::string_view iface,
                          gnmi::gNMI::StubInterface& gnmi_stub) {
  std::string ops_config_path = absl::StrCat(
      "interfaces/interface[name=", iface, "]/ethernet/config/port-speed");
  std::string ops_val =
      absl::StrCat("{\"openconfig-if-ethernet:port-speed\":", port_speed, "}");

  RETURN_IF_ERROR(pins_test::SetGnmiConfigPath(
      &gnmi_stub, ops_config_path, pins_test::GnmiSetType::kUpdate, ops_val));

  return absl::OkStatus();
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

}  // namespace

void SflowTestFixture::SetUp() {
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

  const std::string gnmi_config = GetParam().gnmi_config;
  ASSERT_OK(testbed_->Environment().StoreTestArtifact("gnmi_config.txt",
                                                      gnmi_config));
  ASSERT_OK(testbed_->Environment().StoreTestArtifact(
      "p4info.pb.txt", GetP4Info().DebugString()));
  ASSERT_OK_AND_ASSIGN(sut_p4_session_,
                       pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
                           testbed_->Sut(), gnmi_config, GetP4Info()));
  ASSERT_OK_AND_ASSIGN(ir_p4_info_, pdpi::CreateIrP4Info(GetP4Info()));

  ASSERT_OK_AND_ASSIGN(gnmi_stub_, testbed_->Sut().CreateGnmiStub());
  // Go through all the ports that connect to the Ixia and set them
  // first to 200GB.
  absl::flat_hash_map<std::string, thinkit::InterfaceInfo> interface_info =
      testbed_->GetSutInterfaceInfo();
  for (const auto& [interface, info] : interface_info) {
    if (info.interface_modes.contains(thinkit::TRAFFIC_GENERATOR)) {
      ASSERT_OK(SetPortSpeed(kSpeed200GB, interface, *gnmi_stub_));
    }
  }

  auto speed_config_applied =
      [&interface_info](absl::string_view expected_speed,
                        gnmi::gNMI::StubInterface* gnmi_stub) -> absl::Status {
    for (const auto& [interface, info] : interface_info) {
     if (info.interface_modes.contains(thinkit::TRAFFIC_GENERATOR)) {
        ASSIGN_OR_RETURN(auto port_speed, GetPortSpeed(interface, gnmi_stub));
        if (port_speed != expected_speed) {
          return absl::FailedPreconditionError(absl::Substitute(
              "Port speed is not converged. Interface $0 "
              "speed state path value is $1, expected speed is $2.",
              interface, port_speed, expected_speed));
        }
      }
    }
    return absl::OkStatus();
  };

  // Wait to let the links come up. Switch guarantees state paths to reflect
  // in 10s. Lets wait for a bit more.
  EXPECT_OK(pins_test::WaitForCondition(speed_config_applied, absl::Seconds(30),
                                        kSpeed200GB, gnmi_stub_.get()));
  ASSERT_OK(pins_test::WaitForGnmiPortIdConvergence(
      testbed_->Sut(), GetParam().gnmi_config,
      /*timeout=*/absl::Minutes(3)));

  ASSERT_OK_AND_ASSIGN(ready_links_,
                       GetIxiaConnectedUpLinks(*testbed_, *gnmi_stub_));

  // If links didn't come, lets try 100GB as some testbeds have 100GB
  // IXIA connections.
  if (ready_links_.empty()) {
    for (const auto& [interface, info] : interface_info) {
     if (info.interface_modes.contains(thinkit::TRAFFIC_GENERATOR)) {
        ASSERT_OK(SetPortSpeed(kSpeed100GB, interface, *gnmi_stub_));
      }
    }
    // Wait to let the links come up. Switch guarantees state paths to reflect
    // in 10s. Lets wait for a bit more.
    EXPECT_OK(pins_test::WaitForCondition(speed_config_applied,
                                          absl::Seconds(30), kSpeed100GB,
                                          gnmi_stub_.get()));
    ASSERT_OK_AND_ASSIGN(ready_links_,
                         GetIxiaConnectedUpLinks(*testbed_, *gnmi_stub_));
  }
  ASSERT_FALSE(ready_links_.empty()) << "Ixia links are not ready";
}

void SflowTestFixture::TearDown() {
  // Clear table entries and stop RPC sessions.
  LOG(INFO) << "\n------ TearDown START ------\n";
  if (sut_p4_session_ != nullptr) {
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

// This test checks SFlow works as expected for interface set with punt rule.
// 1. Pick one interface connected to Ixia and set up punt rule.
// 2. Set up Ixia traffic and send packets to SUT via Ixia.
// 3. Collect Sflow samples via sflowtool on SUT.
// 4. Validate the result is as expected

}  // namespace pins
