// Copyright 2025 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "tests/qos/punt_qos_test.h"

#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <vector>

#include "absl/base/thread_annotations.h"
#include "absl/container/flat_hash_map.h"
#include "absl/flags/declare.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "absl/synchronization/mutex.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
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
#include "lib/gnmi/openconfig.pb.h"
#include "lib/otg_helper.h"
#include "lib/utils/generic_testbed_utils.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/netaddr/ipv4_address.h"
#include "p4_pdpi/netaddr/mac_address.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "proto/gnmi/gnmi.pb.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"
#include "tests/gnmi/util.h"
#include "tests/integration/system/nsf/interfaces/testbed.h"
#include "tests/integration/system/nsf/util.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "tests/qos/packet_in_receiver.h"
#include "tests/qos/qos_test_util.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/proto/generic_testbed.pb.h"
#include "thinkit/ssh_client.h"
#include "thinkit/switch.h"

ABSL_DECLARE_FLAG(std::optional<sai::Instantiation>, switch_instantiation);

namespace pins_test {

using ::grpc::ClientContext;
using ::otg::FlowLatencyMetrics;
using ::otg::GetMetricsRequest;
using ::otg::GetMetricsResponse;
using ::otg::MetricsRequest;
using ::otg::Openapi;
using ::otg::SetConfigRequest;
using ::otg::SetConfigResponse;
using ::otg::StateTrafficFlowTransmit;

using ::pins_test::otg_helper::AddEthernetHeader;
using ::pins_test::otg_helper::AddIPv4Header;
using ::pins_test::otg_helper::AddIPv6Header;
using ::pins_test::otg_helper::AddPorts;
using ::pins_test::otg_helper::CreateFlow;
using ::pins_test::otg_helper::SetFlowDuration;
using ::pins_test::otg_helper::SetFlowRatePps;
using ::pins_test::otg_helper::SetFlowSize;
using ::pins_test::otg_helper::SetIPv4Priority;
using ::pins_test::otg_helper::SetIPv6Priority;
using ::pins_test::otg_helper::SetTrafficTransmissionState;

absl::Status NsfRebootHelper(const Testbed &testbed,
                             std::shared_ptr<thinkit::SSHClient> ssh_client) {
  return DoNsfRebootAndWaitForSwitchReadyOrRecover(testbed, *ssh_client,
                                                   nullptr, false);
}

absl::StatusOr<double> GetCpuAverage(gnmi::gNMI::StubInterface &gnmi) {
  const int kNumCPUs = 8;
  int total_cpu_usage = 0;
  LOG(INFO) << "GetCpuAverage:";
  for (int cpu_index = 0; cpu_index < kNumCPUs; ++cpu_index) {
    const std::string cpu_avg_path =
        absl::StrFormat("system/cpus/cpu[index=%d]/state/total/avg", cpu_index);
    ASSIGN_OR_RETURN(std::string cpu_avg,
                     ReadGnmiPath(&gnmi, cpu_avg_path, gnmi::GetRequest::STATE,
                                  "openconfig-system:avg"));
    LOG(INFO) << "cpu_index: " << cpu_index << ", CPU average: " << cpu_avg;
    int cpu_avg_int;
    if (!absl::SimpleAtoi(StripQuotes(cpu_avg), &cpu_avg_int)) {
      return absl::InternalError(
          absl::StrCat("Failed to parse CPU average: ", cpu_avg));
    }
    total_cpu_usage += cpu_avg_int;
  }
  return static_cast<double>(total_cpu_usage) / kNumCPUs;
}

void PuntQoSTestWithIxia::SetUp() {
  GetParam().testbed_interface->SetUp();
  // Pick a testbed with an Ixia Traffic Generator.
  auto requirements =
      gutil::ParseProtoOrDie<thinkit::TestRequirements>(
          R"pb(interface_requirements {
                 count: 1
                 interface_mode: TRAFFIC_GENERATOR
               })pb");

  ASSERT_OK_AND_ASSIGN(
      generic_testbed_,
      GetParam().testbed_interface->GetTestbedWithRequirements(requirements));

  ASSERT_GT(GetParam().control_plane_bandwidth_bytes_per_second, 0);

  thinkit::Switch& sut = generic_testbed_->Sut();
  ASSERT_OK_AND_ASSIGN(sut_p4_session_,
                       pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
                           sut, std::nullopt, GetParam().p4info));

  ASSERT_OK_AND_ASSIGN(sut_gnmi_stub_, sut.CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(sut_gnmi_config_,
                       pins_test::GetGnmiConfig(*sut_gnmi_stub_));
  EXPECT_OK(generic_testbed_->Environment().StoreTestArtifact(
      "gnmi_config.json", sut_gnmi_config_));
  EXPECT_OK(generic_testbed_->Environment().StoreTestArtifact(
      "p4info.textproto", GetParam().p4info));

  const absl::flat_hash_map<std::string, thinkit::InterfaceInfo>
      interface_info = generic_testbed_->GetSutInterfaceInfo();

  ASSERT_OK_AND_ASSIGN(
      std::vector<pins_test::InterfaceLink> up_links,
      GetUpLinks(pins_test::GetAllTrafficGeneratorLinks, *generic_testbed_));

  ASSERT_FALSE(up_links.empty());

  ixia_sut_link_.ixia_tx_interface = up_links[0].peer_interface;
  ixia_sut_link_.sut_rx_interface = up_links[0].sut_interface;
  ixia_sut_link_.ixia_rx_interface = up_links[1].peer_interface;
  ixia_sut_link_.sut_tx_interface = up_links[1].sut_interface;
  ixia_sut_link_.ixia_mirror_interface = up_links[2].peer_interface;
  ixia_sut_link_.sut_mirror_interface = up_links[2].sut_interface;
  ixia_sut_link_.ixia_mirror_backup_interface = up_links[3].peer_interface;
  ixia_sut_link_.sut_mirror_backup_interface = up_links[3].sut_interface;
  ixia_sut_link_.ixia_tx_loc = up_links[0].peer_traffic_location;
  ixia_sut_link_.ixia_rx_loc = up_links[1].peer_traffic_location;

  LOG(INFO) << absl::StrFormat(
      "Test packet route: [Ixia: %s] => [SUT: %s] -> [SUT: %s] => [Ixia: %s] "
      "SUT Mirror port %s => Ixia port %s, SUT Mirror backup port %s => Ixia "
      "port %s",
      ixia_sut_link_.ixia_tx_interface, ixia_sut_link_.sut_rx_interface,
      ixia_sut_link_.sut_tx_interface, ixia_sut_link_.ixia_rx_interface,
      ixia_sut_link_.sut_mirror_interface, ixia_sut_link_.ixia_mirror_interface,
      ixia_sut_link_.sut_mirror_backup_interface,
      ixia_sut_link_.ixia_mirror_backup_interface);

  ASSERT_OK_AND_ASSIGN(p4rt_id_by_interface_,
                       GetAllInterfaceNameToPortId(*sut_gnmi_stub_));
}

void PuntQoSTestWithIxia::TearDown() {
  GetParam().testbed_interface->TearDown();
}

namespace {

const sai::NexthopRewriteOptions kNextHopRewriteOptions = {
    .src_mac_rewrite = netaddr::MacAddress(0x66, 0x55, 0x44, 0x33, 0x22, 0x11),
    .dst_mac_rewrite = netaddr::MacAddress(2, 2, 2, 2, 2, 2),
};

// Buffering and software bottlenecks can cause
// some amount of variance in rate measured end to end.
// Level of tolerance for packet rate verification.
constexpr float kTolerancePercent = 5.0;
constexpr float kQueueCountersTolerancePercent = 10.0;

// Ixia configurations:
// 1. Frames sent per second by Ixia.
// 2. Total frames sent by Ixia.
// 3. Default frame size.
// 4. Maximum frame size.
// 5. Minimum frame size.
constexpr int kFramesPerSecond = 1000000;
constexpr int kTotalFrames = 10000000;
constexpr absl::Duration kTrafficDuration =
    absl::Seconds(kTotalFrames / kFramesPerSecond);
constexpr int kFrameSize = 8000;

// Constants for lower rate traffic.
const int kTotalFramesTrafficLowTrafficRate = 500'000;
const int kBytesPerSecondLowTrafficRate = 200'000'000;  // 200 MBps
const int kFramesPerSecondLowTrafficRate =
    kBytesPerSecondLowTrafficRate / (kFrameSize);
constexpr absl::Duration kTrafficDurationLowTrafficRate = absl::Seconds(
    kTotalFramesTrafficLowTrafficRate / kFramesPerSecondLowTrafficRate);

struct PacketReceiveInfo {
  absl::Mutex mutex;
  int num_packets_punted ABSL_GUARDED_BY(mutex) = 0;
  absl::Time time_first_packet_punted ABSL_GUARDED_BY(mutex);
  absl::Time time_last_packet_punted ABSL_GUARDED_BY(mutex);
};

TEST_P(PuntQoSTestWithIxia, SetDscpAndQueuesAndDenyAboveRateLimit) {
  bool is_rate_mode_in_packets = GetParam().is_rate_mode_in_packets;
  // Flow details.
  const auto dest_mac = netaddr::MacAddress(02, 02, 02, 02, 02, 02);
  const auto source_mac = netaddr::MacAddress(00, 01, 02, 03, 04, 05);
  const auto source_ip = netaddr::Ipv4Address(192, 168, 10, 1);
  const auto dest_ip = netaddr::Ipv4Address(172, 0, 0, 1);

  // Create config.
  SetConfigRequest set_config_request;
  otg::Config *config = set_config_request.mutable_config();

  // Add ports.
  AddPorts(*config, ixia_sut_link_.ixia_tx_interface,
           ixia_sut_link_.ixia_rx_interface, ixia_sut_link_.ixia_tx_loc,
           ixia_sut_link_.ixia_rx_loc);

  // Create flow.
  otg::Flow &flow =
      CreateFlow(*config, ixia_sut_link_.ixia_tx_interface,
                 ixia_sut_link_.ixia_rx_interface, "punt_qos_test_flow");

  SetFlowSize(flow, kFrameSize);
  SetFlowDuration(flow, kTotalFrames);
  SetFlowRatePps(flow, kFramesPerSecond);

  // Set capture metrics.
  flow.mutable_metrics()->set_enable(true);
  flow.mutable_metrics()->set_loss(false);
  flow.mutable_metrics()->set_timestamps(true);
  flow.mutable_metrics()->mutable_latency()->set_enable(true);
  flow.mutable_metrics()->mutable_latency()->set_mode(
      FlowLatencyMetrics::Mode::cut_through);

  // Add ethernet header.
  otg_helper::AddEthernetHeader(flow, source_mac.ToString(),
                                dest_mac.ToString());

  // Add IPv4 header.
  otg::FlowIpv4 &ip_packet =
      AddIPv4Header(flow, source_ip.ToString(), dest_ip.ToString());
  SetIPv4Priority(ip_packet, 0, 0);

  // Get Queues.
  ASSERT_OK_AND_ASSIGN(auto cpu_queues, ExtractQueueInfoViaGnmiConfig(
                                            /*port=*/"CPU", sut_gnmi_config_,
                                            is_rate_mode_in_packets));
  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(GetParam().p4info));
  ASSERT_OK_AND_ASSIGN(const std::string kSutEgressPortP4rtId,
                       gutil::FindOrStatus(p4rt_id_by_interface_,
                                           ixia_sut_link_.sut_tx_interface));
  ASSERT_OK_AND_ASSIGN(const std::string kSutIngressPortP4rtId,
                       gutil::FindOrStatus(p4rt_id_by_interface_,
                                           ixia_sut_link_.sut_rx_interface));
  ASSERT_OK_AND_ASSIGN(
      const std::string kSutMirrorToPortP4rtId,
      gutil::FindOrStatus(p4rt_id_by_interface_,
                          ixia_sut_link_.sut_mirror_interface));
  ASSERT_OK_AND_ASSIGN(
      const std::string kSutMirrorToBackupPortP4rtId,
      gutil::FindOrStatus(p4rt_id_by_interface_,
                          ixia_sut_link_.sut_mirror_backup_interface));
  // Listen for punted packets from the SUT.
  PacketReceiveInfo packet_receive_info;
  {
    absl::MutexLock lock(&packet_receive_info.mutex);
    packet_receive_info.num_packets_punted = 0;
  }

  for (auto& [queue_name, queue_info] : cpu_queues) {
    // Skip unconfigured queues or queues with very low rate-limit as it is not
    // feasible to verify flow rate limit at low queue rates.
    if (queue_info.rate_packets_per_second <= 10) {
      continue;
    }
    // Skip Inband queues.
    if (absl::StartsWith(queue_info.p4_queue_name, "INBAND")) {
      continue;
    }
    // Lets set flow rate limit to be half of queue limit so that queue limit
    // doesn't take effect.
    int flow_rate_limit_in_bytes_per_second =
        (kFrameSize * queue_info.rate_packets_per_second) / 2;

    if (flow_rate_limit_in_bytes_per_second >
        GetParam().control_plane_bandwidth_bytes_per_second) {
      flow_rate_limit_in_bytes_per_second =
          GetParam().control_plane_bandwidth_bytes_per_second / 2;
    }
    ASSERT_OK(pdpi::ClearEntities(*sut_p4_session_));
    const std::string kDefaultCosQueue = "0x8";
    sai::AclQueueAssignments queue_assignments = {
        .cpu_queue = queue_name,
        .unicast_green_queue = GetParam().unicast_green_queue,
        .unicast_red_queue = GetParam().unicast_red_queue,
        .multicast_green_queue = GetParam().multicast_green_queue,
        .multicast_red_queue = GetParam().multicast_red_queue,
    };
    sai::AclMeterConfiguration meter_configuration = {
        .bytes_per_second = flow_rate_limit_in_bytes_per_second,
        .burst_bytes = kFrameSize,
    };

    // Add forwarding rule and mirror rule.
    sai::MirrorSessionParams mirror_session_params = {
        .mirror_session_id = "1",
        .monitor_port = kSutMirrorToPortP4rtId,
        .monitor_backup_port = kSutMirrorToBackupPortP4rtId,
        .mirror_encap_src_mac = "02:02:02:02:02:01",
        .mirror_encap_dst_mac = "02:02:02:02:02:02",
        .mirror_encap_vlan_id = "0x001",
        .mirror_encap_src_ip = "2000::1",
        .mirror_encap_dst_ip = "2000::2",
        .mirror_encap_udp_src_port = "0x1000",
        .mirror_encap_udp_dst_port = "0x1001",
    };

    ASSERT_OK_AND_ASSIGN(
        std::vector<p4::v1::Entity> entities,
        sai::EntryBuilder()
            .AddEntriesForwardingIpPacketsToGivenPort(
                /*egress_port=*/kSutEgressPortP4rtId,
                /*ip_version=*/sai::IpVersion::kIpv4And6,
                /*rewrite_options*/ kNextHopRewriteOptions)
            .AddEntryPuntingPacketsWithDstMac(
                dest_mac.ToString(), sai::PuntAction::kCopy, kDefaultCosQueue)
            .AddEntryToSetDscpAndQueuesAndDenyAboveRateLimit(
                queue_assignments, meter_configuration)
            .AddMirrorSessionTableEntry(mirror_session_params)
            .AddMarkToMirrorAclEntry(
                {.ingress_port = kSutIngressPortP4rtId,
                 .mirror_session_id = mirror_session_params.mirror_session_id})
            .LogPdEntries()
            .GetDedupedPiEntities(ir_p4info));

    ASSERT_OK(
        pdpi::InstallPiEntities(sut_p4_session_.get(), ir_p4info, entities));

    LOG(INFO) << "\n\n\nTesting Queue : " << queue_info.gnmi_queue_name
              << ", acl_qos_table_action: "
              << "set_dscp_and_queues_and_deny_above_rate_limit"
              << "\n===================\n\n\n";

    ASSERT_OK_AND_ASSIGN(
        QueueCounters initial_cpu_queue_counters,
        GetGnmiQueueCounters("CPU", queue_name, *sut_gnmi_stub_));

    // Set the config.
    SetConfigResponse set_config_response;
    ClientContext set_config_context;
    LOG(INFO) << "Set Config Request: " << absl::StrCat(set_config_request);
    Openapi::StubInterface *traffic_client =
        generic_testbed_->GetTrafficClient();
    ASSERT_OK(traffic_client->SetConfig(&set_config_context, set_config_request,
                                        &set_config_response));
    LOG(INFO) << "Set Config Response: " << absl::StrCat(set_config_response);

    if (GetParam().nsf_reboot && GetParam().ssh_client_for_nsf) {
      ASSERT_OK(NsfRebootHelper(generic_testbed_.get(),
                                GetParam().ssh_client_for_nsf));
      // Create a new P4rt session after NSF Reboot
      ASSERT_OK_AND_ASSIGN(sut_p4_session_, pdpi::P4RuntimeSession::Create(
                                                generic_testbed_->Sut()));
    } else if (GetParam().nsf_reboot && !GetParam().ssh_client_for_nsf) {
      FAIL() << "ssh_client parameter needed for NSF Reboot is not provided";
    }

    ASSERT_OK_AND_ASSIGN(
        QueueCounters initial_forwarding_queue_counters,
        GetGnmiQueueCounters(ixia_sut_link_.sut_tx_interface,
                             GetParam().unicast_green_queue, *sut_gnmi_stub_));
    
    PacketInReceiver receiver(*sut_p4_session_, [&packet_receive_info](auto) {
      absl::MutexLock lock(&packet_receive_info.mutex);
      if (packet_receive_info.num_packets_punted == 0) {
        packet_receive_info.time_first_packet_punted = absl::Now();
      }
      packet_receive_info.time_last_packet_punted = absl::Now();
      packet_receive_info.num_packets_punted++;
      return;
    });

    // Reset received packet count at tester for each iteration.
    {
      absl::MutexLock lock(&packet_receive_info.mutex);
      packet_receive_info.num_packets_punted = 0;
    }

    // Get packet count for Mirror-To-Port.
    ASSERT_OK_AND_ASSIGN(
        uint64_t mirror_packets_pre,
        GetInterfaceCounter("out-unicast-pkts",
                            ixia_sut_link_.sut_mirror_interface,
                            sut_gnmi_stub_.get()));
    LOG(INFO) << "Mirror-To-Port packets pre: " << mirror_packets_pre;
    // Get queue counters for Mirror-To-Port.
    ASSERT_OK_AND_ASSIGN(
        QueueCounters initial_mirror_green_queue_counters,
        GetGnmiQueueCounters(ixia_sut_link_.sut_mirror_interface,
                             GetParam().multicast_green_queue,
                             *sut_gnmi_stub_));

    ASSERT_OK_AND_ASSIGN(
        QueueCounters initial_mirror_red_queue_counters,
        GetGnmiQueueCounters(ixia_sut_link_.sut_mirror_interface,
                             GetParam().multicast_red_queue, *sut_gnmi_stub_));

    // Start the traffic.
    ASSERT_OK(SetTrafficTransmissionState(
        *traffic_client, StateTrafficFlowTransmit::State::start));

    // Wait for Traffic to be sent.
    absl::SleepFor(kTrafficDuration);

    // Verify GNMI queue stats match packets received.
    static constexpr absl::Duration kPollInterval = absl::Seconds(5);
    static constexpr absl::Duration kTotalTime = absl::Seconds(50);
    static const int kIterations = kTotalTime / kPollInterval;

    // Check for counters every 5 seconds up to 35 seconds till they match.
    for (int gnmi_counters_check = 0; gnmi_counters_check < kIterations;
         gnmi_counters_check++) {
      absl::SleepFor(kPollInterval);
      QueueCounters final_cpu_queue_counters;
      QueueCounters delta_cpu_queue_counters;
      QueueCounters final_forwarding_queue_counters;
      QueueCounters delta_forwarding_queue_counters;
      ASSERT_OK_AND_ASSIGN(
          final_cpu_queue_counters,
          GetGnmiQueueCounters("CPU", queue_name, *sut_gnmi_stub_));
      delta_cpu_queue_counters = {
          .num_packets_transmitted =
              final_cpu_queue_counters.num_packets_transmitted -
              initial_cpu_queue_counters.num_packets_transmitted,
          .num_packets_dropped = final_cpu_queue_counters.num_packets_dropped -
                                 initial_cpu_queue_counters.num_packets_dropped,
      };
      LOG(INFO) << "Forwarding queue name: " << GetParam().unicast_green_queue;
      LOG(INFO) << "Initial Forwarding queue stats: "
                << initial_forwarding_queue_counters;
      LOG(INFO) << "Final Forwarding queue stats: "
                << final_forwarding_queue_counters;
      LOG(INFO) << delta_cpu_queue_counters;

      ASSERT_OK_AND_ASSIGN(final_forwarding_queue_counters,
                           GetGnmiQueueCounters(ixia_sut_link_.sut_tx_interface,
                                                GetParam().unicast_green_queue,
                                                *sut_gnmi_stub_));
      delta_forwarding_queue_counters = {
          .num_packets_transmitted =
              final_forwarding_queue_counters.num_packets_transmitted -
              initial_forwarding_queue_counters.num_packets_transmitted,
          .num_packets_dropped =
              final_forwarding_queue_counters.num_packets_dropped -
              initial_forwarding_queue_counters.num_packets_dropped,
      };
      LOG(INFO) << delta_cpu_queue_counters;

      absl::MutexLock lock(&packet_receive_info.mutex);
      if (packet_receive_info.num_packets_punted >=
              delta_cpu_queue_counters.num_packets_transmitted *
                  (1 - (kTolerancePercent / 100)) &&
          delta_forwarding_queue_counters.num_packets_transmitted > 0) {
        break;
      }
      EXPECT_NE(gnmi_counters_check, kIterations - 1)
          << "GNMI packet count "
          << delta_cpu_queue_counters.num_packets_transmitted
          << " != Packets received at controller "
          << packet_receive_info.num_packets_punted
          << "Or Forwarding queue packet count "
          << delta_forwarding_queue_counters.num_packets_transmitted
          << "did not increment.";
    }

    {
      absl::MutexLock lock(&packet_receive_info.mutex);

      LOG(INFO) << "Packets received at Controller: "
                << packet_receive_info.num_packets_punted;
      LOG(INFO) << "Timestamp of first received packet: "
                << packet_receive_info.time_first_packet_punted;
      LOG(INFO) << "Timestamp of last received packet: "
                << packet_receive_info.time_last_packet_punted;

      // Verify punt rate matches configured rate limit.
      absl::Duration duration = packet_receive_info.time_last_packet_punted -
                                packet_receive_info.time_first_packet_punted;
      LOG(INFO) << "Duration of packets received: " << duration;
      LOG(INFO) << "Frame size: " << kFrameSize;
      int64_t punt_rate_received_in_bytes_per_second = 0;
      int64_t useconds = absl::ToInt64Microseconds(duration);
      EXPECT_NE(useconds, 0);
      int64_t num_bytes = packet_receive_info.num_packets_punted * kFrameSize;
      LOG(INFO) << "Num bytes received: " << num_bytes;
      punt_rate_received_in_bytes_per_second = num_bytes * 1000000 / useconds;
      LOG(INFO) << "Rate of packets received (bytes per second): "
                << punt_rate_received_in_bytes_per_second;

      EXPECT_LE(
          punt_rate_received_in_bytes_per_second,
          flow_rate_limit_in_bytes_per_second * (1 + kTolerancePercent / 100));
      EXPECT_GE(
          punt_rate_received_in_bytes_per_second,
          flow_rate_limit_in_bytes_per_second * (1 - kTolerancePercent / 100));

      // Get flow metrics.
      GetMetricsRequest metrics_req;
      GetMetricsResponse metrics_res;
      ClientContext metrics_ctx;
      metrics_req.mutable_metrics_request()->set_choice(
          MetricsRequest::Choice::flow);
      metrics_req.mutable_metrics_request()->mutable_flow();
      ASSERT_OK(
          traffic_client->GetMetrics(&metrics_ctx, metrics_req, &metrics_res));
      LOG(INFO) << "Traffic Metrics: " << metrics_res;

      const otg::FlowMetric &flow_metric =
          metrics_res.metrics_response().flow_metrics(0);
      int64_t kObservedTrafficRate = 0;
      double total_time_in_second =
          (flow_metric.timestamps().last_timestamp_ns() -
           flow_metric.timestamps().first_timestamp_ns()) /
          1000000000;
      if (total_time_in_second != 0) {
        kObservedTrafficRate = flow_metric.bytes_rx() / total_time_in_second;
      }
      LOG(INFO) << "Rate of forwarded packets received (bytes per second): "
                << kObservedTrafficRate;
      // For "deny" actions verify that forwarded traffic does not
      // get impacted by the policer.
      EXPECT_LE(kObservedTrafficRate, flow_rate_limit_in_bytes_per_second *
                                          (1 + kTolerancePercent / 100));
      EXPECT_GE(kObservedTrafficRate, flow_rate_limit_in_bytes_per_second *
                                          (1 - kTolerancePercent / 100));

      ASSERT_OK_AND_ASSIGN(
          auto mirror_packets_post,
          GetInterfaceCounter("out-unicast-pkts",
                              ixia_sut_link_.sut_mirror_interface,
                              sut_gnmi_stub_.get()));

      LOG(INFO) << "Mirror-To-Port packets post: " << mirror_packets_post;

      absl::SleepFor(kMaxQueueCounterUpdateTime);

      ASSERT_OK_AND_ASSIGN(
          QueueCounters final_mirror_green_queue_counters,
          GetGnmiQueueCounters(ixia_sut_link_.sut_mirror_interface,
                               GetParam().multicast_green_queue,
                               *sut_gnmi_stub_));

      ASSERT_OK_AND_ASSIGN(
          QueueCounters final_mirror_red_queue_counters,
          GetGnmiQueueCounters(ixia_sut_link_.sut_mirror_interface,
                               GetParam().multicast_red_queue,
                               *sut_gnmi_stub_));

      QueueCounters delta_mirror_green = final_mirror_green_queue_counters -
                                         initial_mirror_green_queue_counters;
      QueueCounters delta_mirror_red =
          final_mirror_red_queue_counters - initial_mirror_red_queue_counters;
      LOG(INFO) << "Mirror-To-Port green queue delta: " << delta_mirror_green;
      LOG(INFO) << "Mirror-To-Port red queue delta: " << delta_mirror_red;

      ASSERT_OK_AND_ASSIGN(
          auto mirror_queue_info,
          ExtractQueueInfoViaGnmiConfig(ixia_sut_link_.sut_mirror_interface,
                                        sut_gnmi_config_, false));
      int64_t mirror_red_queue_rate_limit =
          mirror_queue_info[GetParam().multicast_red_queue]
              .rate_packets_per_second;
      LOG(INFO) << "Mirror-To-Port red queue rate limit (bps): "
                << mirror_red_queue_rate_limit;
      int64_t expected_green_mirror_packets =
          (absl::ToDoubleSeconds(kTrafficDuration) *
           flow_rate_limit_in_bytes_per_second) /
          kFrameSize;
      int64_t expected_red_mirror_packets =
          (absl::ToDoubleSeconds(kTrafficDuration) *
           (mirror_red_queue_rate_limit / (8 * kFrameSize)));
      int64_t expected_mirror_packets =
          expected_green_mirror_packets + expected_red_mirror_packets;
      LOG(INFO) << "Expected mirror packets: " << expected_mirror_packets;
      // Verify Mirror-To-Port counters.
      EXPECT_GE(mirror_packets_post - mirror_packets_pre,
                expected_mirror_packets * (1 - kTolerancePercent / 100));
      EXPECT_LE(mirror_packets_post - mirror_packets_pre,
                expected_mirror_packets * (1 + kTolerancePercent / 100));

      EXPECT_GE(delta_mirror_green.num_packets_transmitted,
                expected_green_mirror_packets *
                    (1 - kQueueCountersTolerancePercent / 100));
      EXPECT_LE(delta_mirror_green.num_packets_transmitted,
                expected_green_mirror_packets *
                    (1 + kQueueCountersTolerancePercent / 100));
      EXPECT_GE(delta_mirror_red.num_packets_transmitted,
                expected_red_mirror_packets *
                    (1 - kQueueCountersTolerancePercent / 100));
      EXPECT_LE(delta_mirror_red.num_packets_transmitted,
                expected_red_mirror_packets *
                    (1 + kQueueCountersTolerancePercent / 100));
    }
    receiver.Destroy();
  }  // for each queue.
}

TEST_P(PuntQoSTestWithIxia, MirrorFailover) {
  // Flow details.
  const auto dest_mac = netaddr::MacAddress(02, 02, 02, 02, 02, 02);
  const auto source_mac = netaddr::MacAddress(00, 01, 02, 03, 04, 05);
  const auto source_ip = netaddr::Ipv4Address(192, 168, 10, 1);
  const auto dest_ip = netaddr::Ipv4Address(172, 0, 0, 1);

  // Create config.
  SetConfigRequest set_config_request;
  otg::Config *config = set_config_request.mutable_config();

  // Add ports.
  AddPorts(*config, ixia_sut_link_.ixia_tx_interface,
           ixia_sut_link_.ixia_rx_interface, ixia_sut_link_.ixia_tx_loc,
           ixia_sut_link_.ixia_rx_loc);

  // Create flow.
  otg::Flow &flow =
      CreateFlow(*config, ixia_sut_link_.ixia_tx_interface,
                 ixia_sut_link_.ixia_rx_interface, "punt_qos_flow");

  SetFlowSize(flow, kFrameSize);
  SetFlowDuration(flow, kTotalFramesTrafficLowTrafficRate);
  SetFlowRatePps(flow, kFramesPerSecondLowTrafficRate);

  // Add ethernet header.
  AddEthernetHeader(flow, source_mac.ToString(), dest_mac.ToString());

  // Add IPv4 header.
  otg::FlowIpv4 &ip_packet =
      AddIPv4Header(flow, source_ip.ToString(), dest_ip.ToString());
  SetIPv4Priority(ip_packet, 0, 0);

  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(GetParam().p4info));
  ASSERT_OK_AND_ASSIGN(const std::string kSutIngressPortP4rtId,
                       gutil::FindOrStatus(p4rt_id_by_interface_,
                                           ixia_sut_link_.sut_rx_interface));
  ASSERT_OK_AND_ASSIGN(const std::string kSutEgressPortP4rtId,
                       gutil::FindOrStatus(p4rt_id_by_interface_,
                                           ixia_sut_link_.sut_tx_interface));
  ASSERT_OK_AND_ASSIGN(
      const std::string kSutMirrorToPortP4rtId,
      gutil::FindOrStatus(p4rt_id_by_interface_,
                          ixia_sut_link_.sut_mirror_interface));
  ASSERT_OK_AND_ASSIGN(
      const std::string kSutMirrorToBackupPortP4rtId,
      gutil::FindOrStatus(p4rt_id_by_interface_,
                          ixia_sut_link_.sut_mirror_backup_interface));

  ASSERT_OK(pdpi::ClearEntities(*sut_p4_session_));
  // Add forwarding rule and mirror rule.
  sai::MirrorSessionParams mirror_session_params = {
      .mirror_session_id = "1",
      .monitor_port = kSutMirrorToPortP4rtId,
      .monitor_backup_port = kSutMirrorToBackupPortP4rtId,
      .mirror_encap_src_mac = "02:02:02:02:02:01",
      .mirror_encap_dst_mac = "02:02:02:02:02:02",
      .mirror_encap_vlan_id = "0x001",
      .mirror_encap_src_ip = "2000::1",
      .mirror_encap_dst_ip = "2000::2",
      .mirror_encap_udp_src_port = "0x1000",
      .mirror_encap_udp_dst_port = "0x1001",
  };

  ASSERT_OK(
      sai::EntryBuilder()
          .AddEntriesForwardingIpPacketsToGivenPort(
              /*egress_port=*/kSutEgressPortP4rtId,
              /*ip_version=*/sai::IpVersion::kIpv4And6,
              /*rewrite_options*/ kNextHopRewriteOptions)
          .AddMirrorSessionTableEntry(mirror_session_params)
          .AddMarkToMirrorAclEntry(
              {.ingress_port = kSutIngressPortP4rtId,
               .mirror_session_id = mirror_session_params.mirror_session_id})
          .LogPdEntries()
          .InstallDedupedEntities(*sut_p4_session_));

  // Set the config.
  SetConfigResponse set_config_response;
  ClientContext set_config_context;
  LOG(INFO) << "Set Config Request: " << absl::StrCat(set_config_request);
  Openapi::StubInterface *traffic_client = generic_testbed_->GetTrafficClient();
  ASSERT_OK(traffic_client->SetConfig(&set_config_context, set_config_request,
                                      &set_config_response));
  LOG(INFO) << "Set Config Response: " << absl::StrCat(set_config_response);

  // Get packet count for Mirror-To-Port.
  ASSERT_OK_AND_ASSIGN(uint64_t mirror_packets_mtp_pre,
                       GetInterfaceCounter("out-unicast-pkts",
                                           ixia_sut_link_.sut_mirror_interface,
                                           sut_gnmi_stub_.get()));
  ASSERT_OK_AND_ASSIGN(
      uint64_t mirror_packets_backup_mtp_pre,
      GetInterfaceCounter("out-unicast-pkts",
                          ixia_sut_link_.sut_mirror_backup_interface,
                          sut_gnmi_stub_.get()));
  LOG(INFO) << "Mirror-To-Port packets pre: " << mirror_packets_mtp_pre;
  LOG(INFO) << "Mirror-To-Backup Port packets pre: "
            << mirror_packets_backup_mtp_pre;

  // Start the traffic.
  ASSERT_OK(SetTrafficTransmissionState(
      *traffic_client, StateTrafficFlowTransmit::State::start));

  if (GetParam().nsf_reboot && GetParam().ssh_client_for_nsf) {
    ASSERT_OK(
        NsfRebootHelper(generic_testbed_.get(), GetParam().ssh_client_for_nsf));
  } else if (GetParam().nsf_reboot && !GetParam().ssh_client_for_nsf) {
    FAIL() << "ssh_client parameter needed for NSF Reboot is not provided";
  }

  LOG(INFO) << "Toggle interface started";
  ASSERT_OK(SetAdminStatus(sut_gnmi_stub_.get(),
                           ixia_sut_link_.sut_mirror_interface, "DOWN",
                           absl::Seconds(0)));
  LOG(INFO) << "Toggle interface ended";
  LOG(INFO) << "Total Traffic duration: " << kTrafficDurationLowTrafficRate;
  // Wait for Traffic to be sent.
  absl::SleepFor(kTrafficDurationLowTrafficRate);

  // Verify GNMI queue stats match packets received.
  absl::SleepFor(absl::Seconds(10));

  // Get packet count for Mirror-To-Port.
  ASSERT_OK_AND_ASSIGN(auto mirror_packets_mtp_post,
                       GetInterfaceCounter("out-unicast-pkts",
                                           ixia_sut_link_.sut_mirror_interface,
                                           sut_gnmi_stub_.get()));

  LOG(INFO) << "Mirror-To-Port packets post: " << mirror_packets_mtp_post;
  // Get packet count for Mirror-To-Port.
  ASSERT_OK_AND_ASSIGN(
      auto mirror_packets_backup_post,
      GetInterfaceCounter("out-unicast-pkts",
                          ixia_sut_link_.sut_mirror_backup_interface,
                          sut_gnmi_stub_.get()));

  LOG(INFO) << "Mirror-To-Backup-Port packets post: "
            << mirror_packets_backup_post;

  int64_t total_mirrored_packets =
      (mirror_packets_mtp_post - mirror_packets_mtp_pre) +
      (mirror_packets_backup_post - mirror_packets_backup_mtp_pre);
  LOG(INFO) << "Total packets:" << kTotalFramesTrafficLowTrafficRate;
  LOG(INFO) << "Total mirrored packets: " << total_mirrored_packets;
  LOG(INFO) << "Packets not mirrored: "
            << kTotalFramesTrafficLowTrafficRate - total_mirrored_packets;
  // Verify drop duration is within acceptable limits.
  int drop_duration_ms =
      (kTotalFramesTrafficLowTrafficRate - total_mirrored_packets) *
      kFrameSize * 1000 / kBytesPerSecondLowTrafficRate;
  LOG(INFO) << "Mirror Failover duration (ms): " << drop_duration_ms;
  EXPECT_LE(drop_duration_ms, 500) << "Drop duration exceeds 500ms";
  EXPECT_OK(SetAdminStatus(sut_gnmi_stub_.get(),
                           ixia_sut_link_.sut_mirror_interface, "UP",
                           absl::Seconds(0)));
}

TEST_P(PuntQoSTestWithIxia, MulticastReplicationToCpu) {

  const absl::flat_hash_map<std::string, thinkit::InterfaceInfo>
      sut_interface_info = generic_testbed_->GetSutInterfaceInfo();
  ASSERT_TRUE(sut_interface_info.contains(ixia_sut_link_.sut_rx_interface));

  const auto src_mac =
      sut_interface_info.at(ixia_sut_link_.sut_rx_interface).peer_mac_address;
  const auto dest_mac = netaddr::MacAddress(0x33, 0x33, 0, 0, 0, 1);
  const auto source_ip = netaddr::Ipv6Address(0x1000, 0, 0, 0, 0, 0, 0, 1);
  const auto dest_ip = netaddr::Ipv6Address(0xff00, 0, 0, 0, 0, 0, 0, 1);

  // Create config.
  SetConfigRequest set_config_request;
  otg::Config *config = set_config_request.mutable_config();

  // Add ports.
  AddPorts(*config, ixia_sut_link_.ixia_tx_interface,
           ixia_sut_link_.ixia_rx_interface, ixia_sut_link_.ixia_tx_loc,
           ixia_sut_link_.ixia_rx_loc);

  // Create flow.
  otg::Flow &flow =
      CreateFlow(*config, ixia_sut_link_.ixia_tx_interface,
                 ixia_sut_link_.ixia_rx_interface, "punt_qos_flow");

  SetFlowSize(flow, kFrameSize);
  SetFlowRatePps(flow, 1000000);

  // Add ethernet header.
  AddEthernetHeader(flow, src_mac, dest_mac.ToString());

  // Add IPv6 header.
  otg::FlowIpv6 &ip_packet =
      AddIPv6Header(flow, source_ip.ToString(), dest_ip.ToString());
  SetIPv6Priority(ip_packet, 0, 0);

  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(GetParam().p4info));
  ASSERT_OK_AND_ASSIGN(const std::string sut_ingress_port_p4rt_id,
                       gutil::FindOrStatus(p4rt_id_by_interface_,
                                           ixia_sut_link_.sut_rx_interface));
  ASSERT_OK_AND_ASSIGN(const std::string sut_egress_port1_p4rt_id,
                       gutil::FindOrStatus(p4rt_id_by_interface_,
                                           ixia_sut_link_.sut_tx_interface));
  ASSERT_OK_AND_ASSIGN(
      const std::string sut_egress_port2_p4rt_id,
      gutil::FindOrStatus(p4rt_id_by_interface_,
                          ixia_sut_link_.sut_mirror_interface));

  ASSERT_OK(pdpi::ClearEntities(*sut_p4_session_));
  ASSERT_OK(
      sai::EntryBuilder()
          .AddVrfEntry("kVrf")
          .AddEntryAdmittingAllPacketsToL3()
          .AddPreIngressAclTableEntry("kVrf")
          .AddMulticastGroupEntry(
              1,
              {
                  sai::Replica{.egress_port = sut_egress_port1_p4rt_id,
                               .instance = 0},
                  sai::Replica{.egress_port = sut_egress_port2_p4rt_id,
                               .instance = 1},
                  sai::Replica{.egress_port = GetParam().cpu_port_id,
                               .instance = 2},
                  sai::Replica{.egress_port = GetParam().cpu_port_id,
                               .instance = 3},
                  sai::Replica{.egress_port = GetParam().cpu_port_id,
                               .instance = 4},
              })
          .AddMrifEntryRewritingSrcMac(sut_egress_port1_p4rt_id,
                                       /*instance=*/0,
                                       netaddr::MacAddress(1, 0, 0, 0, 0, 0))
          .AddMrifEntryRewritingSrcMac(sut_egress_port2_p4rt_id,
                                       /*instance=*/1,
                                       netaddr::MacAddress(1, 0, 0, 0, 0, 0))
          .AddMrifEntryRewritingSrcMac(GetParam().cpu_port_id,
                                       /*instance=*/2,
                                       netaddr::MacAddress(1, 0, 0, 0, 0, 0))
          .AddMrifEntryRewritingSrcMac(GetParam().cpu_port_id,
                                       /*instance=*/3,
                                       netaddr::MacAddress(1, 0, 0, 0, 0, 0))
          .AddMrifEntryRewritingSrcMac(GetParam().cpu_port_id,
                                       /*instance=*/4,
                                       netaddr::MacAddress(1, 0, 0, 0, 0, 0))
          .AddMulticastRoute(
              "kVrf", netaddr::Ipv6Address(0xff00, 0, 0, 0, 0, 0, 0, 1), 1)
          .AddIngressAclMirrorAndRedirectEntry(sai::SetCpuQueueAndCancelCopy{
              .cpu_queue = GetParam().cpu_replication_queue,
          })
          .InstallDedupedEntities(*sut_p4_session_));

  // Set the config.
  SetConfigResponse set_config_response;
  ClientContext set_config_context;
  LOG(INFO) << "Set Config Request: " << absl::StrCat(set_config_request);
  Openapi::StubInterface *traffic_client = generic_testbed_->GetTrafficClient();
  ASSERT_OK(traffic_client->SetConfig(&set_config_context, set_config_request,
                                      &set_config_response));
  LOG(INFO) << "Set Config Response: " << absl::StrCat(set_config_response);

  if (GetParam().nsf_reboot && GetParam().ssh_client_for_nsf) {
    ASSERT_OK(
        NsfRebootHelper(generic_testbed_.get(), GetParam().ssh_client_for_nsf));
  } else if (GetParam().nsf_reboot && !GetParam().ssh_client_for_nsf) {
    FAIL() << "ssh_client parameter needed for NSF Reboot is not provided";
  }

  absl::SleepFor(absl::Seconds(15));

  // Get cpu averages before test.
  ASSERT_OK_AND_ASSIGN(double cpu_average_pre, GetCpuAverage(*sut_gnmi_stub_));

  // Get packet count on CPU queue.
  ASSERT_OK_AND_ASSIGN(
      QueueCounters initial_cpu_queue_counters,
      GetGnmiQueueCounters("CPU", GetParam().cpu_replication_queue,
                           *sut_gnmi_stub_));

  // Start the traffic.
  ASSERT_OK(SetTrafficTransmissionState(
      *traffic_client, StateTrafficFlowTransmit::State::start));

  absl::SleepFor(absl::Seconds(15));
  
  // Verify CPU usage is within 15% of baseline.
  ASSERT_OK_AND_ASSIGN(double cpu_average, GetCpuAverage(*sut_gnmi_stub_));
  LOG(INFO) << "CPU average pre: " << cpu_average_pre;
  LOG(INFO) << "CPU average post: " << cpu_average;
  EXPECT_LT(cpu_average, cpu_average_pre + 15);

  // Get packet count on CPU queue.
  ASSERT_OK_AND_ASSIGN(
      QueueCounters post_cpu_queue_counters,
      GetGnmiQueueCounters("CPU", GetParam().cpu_replication_queue,
                           *sut_gnmi_stub_));

  // Verify packets to CPU port are being tail dropped.
  ASSERT_GT(post_cpu_queue_counters.num_packets_transmitted,
            initial_cpu_queue_counters.num_packets_transmitted);
  ASSERT_GT(post_cpu_queue_counters.num_packets_dropped,
            initial_cpu_queue_counters.num_packets_dropped);

  auto delta_cpu_queue_counters =
      post_cpu_queue_counters - initial_cpu_queue_counters;
  LOG(INFO) << "CPU queue: " << GetParam().cpu_replication_queue;
  LOG(INFO) << "CPU queue delta: " << delta_cpu_queue_counters;

  // Stop traffic
  ASSERT_OK(SetTrafficTransmissionState(*traffic_client,
                                        StateTrafficFlowTransmit::State::stop));
}

}  // namespace
}  // namespace pins_test
