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

#include "tests/qos/pfc_test.h"

#include <cstdint>
#include <cstdlib>
#include <memory>
#include <optional>
#include <ostream>
#include <string>
#include <tuple>
#include <vector>

#include "absl/algorithm/container.h"
#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/status.h"  // IWYU pragma: keep to avoid ClangTidy complaining about this.
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"  // IWYU pragma: keep to avoid ClangTidy complaining about this.
#include "gutil/gutil/testing.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/ixia_helper.h"
#include "p4_pdpi/netaddr/ipv4_address.h"
#include "p4_pdpi/netaddr/mac_address.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"
#include "tests/forwarding/util.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "tests/qos/qos_test_util.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/proto/generic_testbed.pb.h"
#include "thinkit/switch.h"

namespace pins_test {

// Structure represents the information needed to log the test results.
struct PfcLogInfo {
  int dscp;
  std::string queue;
  int priority;
  int pause_quanta;
};

// Overloading the ostream operator for printing PfcLogInfo
std::ostream &operator<<(std::ostream &os, const PfcLogInfo &info) {
  os << "====== DSCP: " << info.dscp << ", Queue: " << info.queue
     << ", PFC Priority: " << info.priority
     << ", Pause Quantas: " << info.pause_quanta << " =====";
  return os;
}

constexpr int kDefaultFrameSize = 1500;

namespace {
// Compute the pause duration using pause quanta and link speed.
absl::Duration GetPauseDuration(int pause_quanta,
                                int64_t sut_interface_bits_per_second) {
  constexpr int kPauseQuantaBits = 512;
  return absl::Nanoseconds((kPauseQuantaBits * pause_quanta) /
                           (sut_interface_bits_per_second / 1'000'000'000));
}
}  // namespace

// Function  will try and find 2 Ixia links for ingress and 1 for egress such
// that ingress ports have speed at least that of egress port.
absl::StatusOr<IxiaLinks> GetIxiaLinks(thinkit::GenericTestbed &testbed,
                                       gnmi::gNMI::StubInterface &gnmi_stub) {
  IxiaLinks links;
  // Pick 3 SUT ports connected to the Ixia, 2 for receiving test packets and
  // 1 for forwarding them back. We use the faster links for injecting packets
  // so we can oversubsribe the egress port.
  LOG(INFO) << "picking test packet links";
  ASSIGN_OR_RETURN(std::vector<ixia::IxiaLink> ready_links,
                   ixia::GetReadyIxiaLinks(testbed, gnmi_stub));
  absl::c_sort(ready_links, [&](auto &x, auto &y) -> bool {
    return x.sut_interface_bits_per_second < y.sut_interface_bits_per_second;
  });
  RET_CHECK(ready_links.size() >= 3)
      << "Test requires at least 3 SUT ports connected to an Ixia";
  const auto [kEgressLink, kIngressLink1, kIngressLink2] =
      std::make_tuple(ready_links[0], ready_links[1], ready_links[2]);
  RET_CHECK(kEgressLink.sut_interface_bits_per_second <=
            kIngressLink1.sut_interface_bits_per_second);
  RET_CHECK(kEgressLink.sut_interface_bits_per_second <=
            kIngressLink2.sut_interface_bits_per_second);
  links.ingress_links[0] = kIngressLink1;
  links.ingress_links[1] = kIngressLink2;
  links.egress_link = kEgressLink;

  return links;
}

const sai::NexthopRewriteOptions kNextHopRewriteOptions = {
    .src_mac_rewrite = netaddr::MacAddress(0x66, 0x55, 0x44, 0x33, 0x22, 0x11),
    .dst_mac_rewrite = netaddr::MacAddress(2, 2, 2, 2, 2, 2),
};

void PfcTestWithIxia::SetUp() {
  // Initialize Biglab Testbed.
  GetParam().testbed_interface->SetUp();

  // Initialize Ixia.
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

  thinkit::Switch &sut = generic_testbed_->Sut();

  ASSERT_OK_AND_ASSIGN(gnmi_stub_, sut.CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(std::string sut_gnmi_config,
                       pins_test::GetGnmiConfig(*gnmi_stub_));
  EXPECT_OK(generic_testbed_->Environment().StoreTestArtifact(
      "gnmi_config.json", sut_gnmi_config));

  EXPECT_OK(generic_testbed_->Environment().StoreTestArtifact(
      "p4info.textproto", *GetParam().p4info));

  // Configure SUT.
  ASSERT_OK_AND_ASSIGN(sut_p4rt_session_,
                       pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
                           sut, std::nullopt, GetParam().p4info));

  // Flow details.
  const auto dest_mac = netaddr::MacAddress(02, 02, 02, 02, 02, 02);
  const auto pfc_dmac = netaddr::MacAddress(0x01, 0x80, 0xc2, 0x00, 0x00, 0x01);
  const auto source_mac = netaddr::MacAddress(00, 01, 02, 03, 04, 05);
  const auto source_ip = netaddr::Ipv4Address(192, 168, 10, 1);
  const auto dest_ip = netaddr::Ipv4Address(172, 0, 0, 1);

  const absl::flat_hash_map<std::string, thinkit::InterfaceInfo>
      interface_info = generic_testbed_->GetSutInterfaceInfo();

  ASSERT_OK_AND_ASSIGN(ixia_links_,
                       GetIxiaLinks(*generic_testbed_, *gnmi_stub_));

  std::string ixia_interface = ixia_links_.ingress_links[0].ixia_interface;
  std::string sut_interface = ixia_links_.ingress_links[0].sut_interface;
  std::string ixia_rx_interface = ixia_links_.egress_link.ixia_interface;
  std::string sut_egress_interface = ixia_links_.egress_link.sut_interface;

  LOG(INFO) << absl::StrFormat(
      "Test packet route: [Ixia: %s] => [SUT: %s] -> [SUT: %s] => [Ixia: %s]",
      ixia_interface, sut_interface, sut_egress_interface, ixia_rx_interface);

  // Save initial PFC Rx enable state.
  ASSERT_OK_AND_ASSIGN(kInitialPfcRxEnable,
                       GetPortPfcRxEnable(sut_egress_interface, *gnmi_stub_));
  // Enable PFC Rx on egress port
  ASSERT_OK(SetPortPfcRxEnable(sut_egress_interface,
                               /*port_pfc_rx_enable=*/"true", *gnmi_stub_));

  // We will perform the following steps with Ixia:
  // Setup main Ixia forwarded traffic.
  // Setup PFC traffic.
  ASSERT_OK_AND_ASSIGN(ixia::IxiaPortInfo ixia_port,
                       ixia::ExtractPortInfo(ixia_interface));

  ASSERT_OK_AND_ASSIGN(ixia::IxiaPortInfo ixia_rx_port,
                       ixia::ExtractPortInfo(ixia_rx_interface));

  ASSERT_OK_AND_ASSIGN(
      ixia_connection_reference_,
      pins_test::ixia::IxiaConnect(ixia_port.hostname, *generic_testbed_));

  ASSERT_OK_AND_ASSIGN(
      std::string kIxiaSrcPortHandle,
      pins_test::ixia::IxiaVport(ixia_connection_reference_, ixia_port.card,
                                 ixia_port.port, *generic_testbed_));

  ASSERT_OK_AND_ASSIGN(
      std::string kIxiaDstPortHandle,
      pins_test::ixia::IxiaVport(ixia_connection_reference_, ixia_rx_port.card,
                                 ixia_rx_port.port, *generic_testbed_));

  main_traffic_.traffic_name = "Main traffic";
  ASSERT_OK_AND_ASSIGN(
      main_traffic_.traffic_item,
      ixia::SetUpTrafficItem(kIxiaSrcPortHandle, kIxiaDstPortHandle,
                             main_traffic_.traffic_name, *generic_testbed_));
  port_speed_bytes_per_second_ =
      ixia_links_.egress_link.sut_interface_bits_per_second / 8;
  const int kIngressLineRateFramesPerSecond =
      0.95 * port_speed_bytes_per_second_ / kDefaultFrameSize;
  main_traffic_parameters_ = ixia::TrafficParameters{
      .frame_size_in_bytes = kDefaultFrameSize,
      .traffic_speed = ixia::FramesPerSecond{kIngressLineRateFramesPerSecond},
      .src_mac = source_mac,
      .dst_mac = dest_mac,
      .ip_parameters = ixia::Ipv4TrafficParameters{
          .src_ipv4 = source_ip,
          .dst_ipv4 = dest_ip,
          // Set ECN 0 to avoid RED drops.
          .priority = ixia::IpPriority{.dscp = 0, .ecn = 0},
      }};
  ASSERT_OK(ixia::SetTrafficParameters(
      main_traffic_.traffic_item, main_traffic_parameters_, *generic_testbed_));

  pfc_traffic_parameters_ = ixia::TrafficParameters{
      .frame_size_in_bytes = 64,
      .traffic_speed = ixia::FramesPerSecond{100},
      .src_mac = source_mac,
      .dst_mac = pfc_dmac,
      .pfc_parameters = ixia::PfcTrafficParameters{
          .priority_enable_vector = 0x00,
          .pause_quanta_per_queue = {0xffff, 0xffff, 0xffff, 0xffff, 0xffff,
                                     0xffff, 0xffff, 0xffff}}};

  pfc_traffic_.traffic_name = "PFC traffic";
  ASSERT_OK_AND_ASSIGN(
      pfc_traffic_.traffic_item,
      ixia::SetUpTrafficItem(kIxiaDstPortHandle, kIxiaSrcPortHandle,
                             pfc_traffic_.traffic_name, *generic_testbed_));
  ASSERT_OK(ixia::SetTrafficParameters(
      pfc_traffic_.traffic_item, pfc_traffic_parameters_, *generic_testbed_));

  // Construct forwarding entry and install.
  // Get P4RT ID of the SUT egress port.
  absl::flat_hash_map<std::string, std::string> p4rt_id_by_interface;
  ASSERT_OK_AND_ASSIGN(p4rt_id_by_interface,
                       GetAllInterfaceNameToPortId(*gnmi_stub_));
  ASSERT_OK_AND_ASSIGN(
      const std::string kSutEgressPortP4rtId,
      gutil::FindOrStatus(p4rt_id_by_interface, sut_egress_interface));
  ASSERT_OK(sai::EntryBuilder()
                .AddEntriesForwardingIpPacketsToGivenPort(
                    /*egress_port=*/kSutEgressPortP4rtId,
                    /*ip_version=*/sai::IpVersion::kIpv4And6,
                    /*rewrite_options*/ kNextHopRewriteOptions)
                .LogPdEntries()
                .InstallDedupedEntities(*sut_p4rt_session_));
}

void PfcTestWithIxia::TearDown() {
  ASSERT_OK(
      ixia::DeleteTrafficItem(main_traffic_.traffic_item, *generic_testbed_));
  ASSERT_OK(
      ixia::DeleteTrafficItem(pfc_traffic_.traffic_item, *generic_testbed_));
  // Restore PFC Rx enable state.
  ASSERT_OK(SetPortPfcRxEnable(ixia_links_.egress_link.sut_interface,
                               /*port_pfc_rx_enable=*/kInitialPfcRxEnable,
                               *gnmi_stub_));
  GetParam().testbed_interface->TearDown();
}

// Utility function to get queue counters change on
// back to back counter update cycle.
absl::StatusOr<QueueCounters> GetQueueCountersChange(
    absl::string_view port, absl::string_view queue,
    gnmi::gNMI::StubInterface &gnmi) {
  // Wait for at least one queue counter cycle (10 seconds).
  absl::SleepFor(absl::Seconds(15));
  // Read counters of the target queue.
  ASSIGN_OR_RETURN(const pins_test::QueueCounters queue_counters_pre,
                   GetGnmiQueueCounters(/*port=*/port,
                                        /*queue=*/queue, gnmi));
  absl::SleepFor(absl::Seconds(15));
  // Read counters of the target queue.
  ASSIGN_OR_RETURN(const pins_test::QueueCounters queue_counters_post,
                   GetGnmiQueueCounters(/*port=*/port,
                                        /*queue=*/queue, gnmi));
  return queue_counters_post - queue_counters_pre;
}

// The purpose of this test is to verify that PFC Rx is working correctly.
// We test this by sending line rate forwarded traffic from SUT Port A -> SUT
// Port B and PFC traffic from SUT Port B -> SUT Port A. We expect the SUT to
// pause the queue corresponding to the PFC traffic for the duration of the
// pause time configured in the PFC traffic parameters.
TEST_P(PfcTestWithIxia, PfcRxWithNoPacketDrops) {
  // Pause duration in units of time for 512 bits.
  for (const auto pause_quanta : {0x3ff, 0x1fff, 0xffff}) {
    for (const auto [priority, queue] : *GetParam().queue_by_pfc_priority) {
      PfcLogInfo log_info = {
          .dscp = GetParam().dscp_by_queue->at(queue),
          .queue = queue,
          .priority = priority,
          .pause_quanta = pause_quanta,
      };
      SCOPED_TRACE(log_info);
      LOG(INFO) << "\n\n " << log_info;

      // Setup main traffic DSCP.
      ixia::Ipv4TrafficParameters &ip_params =
          std::get<ixia::Ipv4TrafficParameters>(
              main_traffic_parameters_.ip_parameters.value());
      ip_params.priority->dscp = GetParam().dscp_by_queue->at(queue);
      ASSERT_OK(ixia::SetTrafficParameters(
          main_traffic_.traffic_item, main_traffic_parameters_,
          *generic_testbed_, /*is_update=*/true));

      // Setup PFC traffic priority and pause duration for the target queue.
      pfc_traffic_parameters_.pfc_parameters->priority_enable_vector =
          1 << priority;
      for (int i = 0; i < kNumQueues; ++i) {
        if (i == priority) {
          pfc_traffic_parameters_.pfc_parameters->pause_quanta_per_queue[i] =
              pause_quanta;
        } else {
          pfc_traffic_parameters_.pfc_parameters->pause_quanta_per_queue[i] = 0;
        }
      }

      LOG(INFO) << "SUT interface bits per second: "
                << ixia_links_.egress_link.sut_interface_bits_per_second;

      pfc_traffic_parameters_.frame_count = 1;

      ASSERT_OK(ixia::SetTrafficParameters(
          pfc_traffic_.traffic_item, pfc_traffic_parameters_, *generic_testbed_,
          /*is_update=*/true));

      // Wait for queue to be empty. Try up to 3 times waiting for the queue
      // counters to stabilize.
      pins_test::QueueCounters queue_counters_before_test;
      EXPECT_OK(pins::TryUpToNTimes(5, /*delay=*/absl::Seconds(30), [&] {
        // Read counters of the target queue.
        ASSIGN_OR_RETURN(
            queue_counters_before_test,
            GetGnmiQueueCounters(/*port=*/ixia_links_.egress_link.sut_interface,
                                 /*queue=*/queue, *gnmi_stub_));
        if (queue_counters_before_test.max_periodic_queue_len <=
            kDefaultFrameSize) {
          return absl::OkStatus();
        }
        return absl::InternalError(absl::Substitute(
            "Max periodic queue len is not 0, $0",
            queue_counters_before_test.max_periodic_queue_len));
      }));

      // Occasionally the Ixia API cannot keep up and starting traffic
      // fails, so we try up to 3 times.
      ASSERT_OK(pins::TryUpToNTimes(3, /*delay=*/absl::Seconds(1), [&] {
        return ixia::StartTraffic(
            {main_traffic_.traffic_item, pfc_traffic_.traffic_item},
            ixia_connection_reference_, *generic_testbed_,
            /*run_in_parallel=*/false);
      }));

      // Wait for the pause duration and then stop PFC traffic.
      absl::Duration pause_duration = GetPauseDuration(
          pause_quanta, ixia_links_.egress_link.sut_interface_bits_per_second);
      absl::SleepFor(pause_duration);
      ASSERT_OK(
          ixia::StopTraffic(pfc_traffic_.traffic_item, *generic_testbed_));

      QueueCounters queue_counters_after_test, delta_counters;

      // Watermarks are updated every 10 seconds, hence we wait up to 20 seconds
      // to get 2 new watermark reads (in case the first one is cleared).
      EXPECT_OK(pins::TryUpToNTimes(5, /*delay=*/absl::Seconds(5), [&] {
        // Read counters of the target queue.
        ASSIGN_OR_RETURN(
            queue_counters_after_test,
            GetGnmiQueueCounters(/*port=*/ixia_links_.egress_link.sut_interface,
                                 /*queue=*/queue, *gnmi_stub_));

        uint64_t expected_watermark =
            (absl::ToInt64Nanoseconds(pause_duration) *
             port_speed_bytes_per_second_) /
            1'000'000'000;
        LOG(INFO) << "queue_counters_after_test.max_periodic_queue_len: "
                  << queue_counters_after_test.max_periodic_queue_len
                  << " .max_queue_len: "
                  << queue_counters_after_test.max_queue_len
                  << " expected watermark: " << expected_watermark;
        const int absolute_error =
            queue_counters_after_test.max_periodic_queue_len -
            expected_watermark;
        const double relative_error_percent =
            100. * absolute_error / expected_watermark;
        constexpr double tolerance_percent = 27;  // +-27% tolerance.
        if (std::abs(relative_error_percent) <= tolerance_percent) {
          LOG(INFO) << "observed watermark matches expected watermark "
                       "(error: "
                    << relative_error_percent << "%)";
          return absl::OkStatus();
        }
        return absl::InternalError(absl::Substitute(
            "observed watermark of $0 is not within $1% of the queue $2 PIR of "
            "$3 (error = $4%)",
            queue_counters_after_test.max_periodic_queue_len, tolerance_percent,
            queue, expected_watermark, relative_error_percent));
      }));
      delta_counters = queue_counters_after_test - queue_counters_before_test;
      EXPECT_EQ(delta_counters.num_packets_dropped, 0);

      // Wait for queue counters to stabilize and then stop main traffic.
      ASSERT_OK(
          ixia::StopTraffic(main_traffic_.traffic_item, *generic_testbed_));
      LOG(INFO) << "-- stopped " << main_traffic_.traffic_name;
    }
  }
}

TEST_P(PfcTestWithIxia, PfcWatchdog) {
  for (auto [prio, queue] : *GetParam().queue_by_pfc_priority) {
    LOG(INFO) << "\n\n====== DSCP: " << GetParam().dscp_by_queue->at(queue)
              << ", Queue: " << queue << ", PFC Priority: " << prio
              << " ======";
    // Setup main traffic DSCP.
    ixia::Ipv4TrafficParameters &ip_params =
        std::get<ixia::Ipv4TrafficParameters>(
            main_traffic_parameters_.ip_parameters.value());
    ip_params.priority->dscp = GetParam().dscp_by_queue->at(queue);
    ASSERT_OK(ixia::SetTrafficParameters(
        main_traffic_.traffic_item, main_traffic_parameters_, *generic_testbed_,
        /*is_update=*/true));

    // Setup PFC traffic priority.
    pfc_traffic_parameters_.pfc_parameters->priority_enable_vector = 1 << prio;

    // Calculate PFC frame rate required for deadlock.
    LOG(INFO) << "SUT interface bits per second: "
              << ixia_links_.egress_link.sut_interface_bits_per_second;

    const int kPauseQuantaBits = 512;
    const int kPauseQuantas = 0xffff;
    uint64_t pause_duration_ns =
        (kPauseQuantaBits * kPauseQuantas) /
        (ixia_links_.egress_link.sut_interface_bits_per_second / 1'000'000'000);
    int rate_of_pfc_frames = 1'000'000'000 / pause_duration_ns;
    LOG(INFO) << "Rate of PFC frames (pps): " << rate_of_pfc_frames;

    for (bool create_deadlock : {true, false}) {
      LOG(INFO) << "==== PFC Deadlock: " << create_deadlock << " ====";
      if (create_deadlock) {
        pfc_traffic_parameters_.traffic_speed =
            ixia::FramesPerSecond{rate_of_pfc_frames + 100};
      } else {
        pfc_traffic_parameters_.traffic_speed =
            ixia::FramesPerSecond{rate_of_pfc_frames - 100};
      }
      ASSERT_OK(ixia::SetTrafficParameters(
          pfc_traffic_.traffic_item, pfc_traffic_parameters_, *generic_testbed_,
          /*is_update=*/true));

      // Read counters of the target queue.
      pins_test::QueueCounters queue_counters_before_test;
      ASSERT_OK(pins::TryUpToNTimes(5, /*delay=*/absl::Seconds(30), [&] {
        // Read counters of the target queue.
        ASSIGN_OR_RETURN(
            queue_counters_before_test,
            GetGnmiQueueCounters(/*port=*/ixia_links_.egress_link.sut_interface,
                                 /*queue=*/queue, *gnmi_stub_));
        LOG(INFO) << "Queue counters before test: "
                  << queue_counters_before_test;
        // Wait till max periodic queue length is negligible.
        if (queue_counters_before_test.max_periodic_queue_len <=
            kDefaultFrameSize) {
          return absl::OkStatus();
        }
        return absl::InternalError("Max periodic queue len is not 0");
      }));
      LOG(INFO) << "-- starting " << main_traffic_.traffic_name;
      LOG(INFO) << "-- starting " << pfc_traffic_.traffic_name;
      // Occasionally the Ixia API cannot keep up and starting traffic
      // fails, so we try up to 3 times.
      ASSERT_OK(pins::TryUpToNTimes(3, /*delay=*/absl::Seconds(1), [&] {
        return ixia::StartTraffic(
            {main_traffic_.traffic_item, pfc_traffic_.traffic_item},
            ixia_connection_reference_, *generic_testbed_);
      }));

      // Wait for deadlock detection time.
      absl::SleepFor(GetParam().deadlock_detection_time +
                     GetParam().pfc_wd_poll_time);

      if (create_deadlock) {
        // TODO: Assert WD counters incremented by 1

        // Assert DROP COUNTERS ARE NOT INCREMENTING anymore
        ASSERT_OK_AND_ASSIGN(QueueCounters queue_counters_delta,
                             GetQueueCountersChange(
                                 /*port=*/ixia_links_.egress_link.sut_interface,
                                 /*queue=*/queue, *gnmi_stub_));
        EXPECT_EQ(queue_counters_delta.num_packets_dropped, 0);
      } else {
        // TODO: Assert WD counters did not increment.

        // Assert DROP COUNTERS ARE INCREMENTING.
        ASSERT_OK_AND_ASSIGN(QueueCounters queue_counters_delta,
                             GetQueueCountersChange(
                                 /*port=*/ixia_links_.egress_link.sut_interface,
                                 /*queue=*/queue, *gnmi_stub_));
        ASSERT_OK(pins::TryUpToNTimes(3, /*delay=*/absl::Seconds(5), [&] {
          if (queue_counters_delta.num_packets_dropped > 0) {
            return absl::OkStatus();
          }
          return absl::InternalError("Drops are not incrementing");
        }));
      }
      ASSERT_OK(
          ixia::StopTraffic(pfc_traffic_.traffic_item, *generic_testbed_));
      LOG(INFO) << "-- stopped " << pfc_traffic_.traffic_name;

      // Wait for deadlock restoration time + pfc_wd_poll_time.
      absl::SleepFor(GetParam().deadlock_restoration_time +
                     GetParam().pfc_wd_poll_time);
      // Read counters of the target queue.
      ASSERT_OK_AND_ASSIGN(
          const pins_test::QueueCounters queue_counters_after_test,
          GetGnmiQueueCounters(/*port=*/ixia_links_.egress_link.sut_interface,
                               /*queue=*/queue, *gnmi_stub_));

      auto delta_counters =
          queue_counters_after_test - queue_counters_before_test;
      LOG(INFO) << "Delta counters: " << delta_counters;

      auto drop_duration =
          (delta_counters.num_packets_dropped * kDefaultFrameSize +
           queue_counters_after_test.max_periodic_queue_len) *
          1000 / port_speed_bytes_per_second_;
      LOG(INFO) << ((create_deadlock)
                        ? "Drop duration before deadlock was detected(ms): "
                        : "Drop duration due to PFC pause (ms): ")
                << drop_duration;
      ASSERT_OK(
          ixia::StopTraffic(main_traffic_.traffic_item, *generic_testbed_));
      LOG(INFO) << "-- stopped " << main_traffic_.traffic_name;
    }
  }
}

}  // namespace pins_test
