// Copyright 2022 Google LLC
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

#include "tests/qos/frontpanel_qos_test.h"

#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <memory>
#include <optional>
#include <sstream>
#include <thread>  // NOLINT
#include <vector>

#include "absl/cleanup/cleanup.h"
#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_replace.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"

#include "dvaas/test_vector.pb.h"
#include "gutil/collections.h"
#include "gutil/proto.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/ixia_helper.h"
#include "lib/utils/json_utils.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/netaddr/ipv4_address.h"
#include "p4_pdpi/netaddr/ipv6_address.h"
#include "p4_pdpi/netaddr/mac_address.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_pdpi/pd.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "tests/forwarding/util.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "tests/qos/packet_in_receiver.h"
#include "tests/qos/qos_test_util.h"
#include "thinkit/generic_testbed.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace pins_test {

using ::json_yang::FormatJsonBestEffort;
using ::testing::Eq;
using ::testing::Field;
using ::testing::ResultOf;

template <class T> std::string ToString(const T &t) {
  std::stringstream ss;
  ss << t;
  return ss.str();
}

// Connects to Ixia on the given testbed and returns a string handle identifying
// the connection (aka "topology ref").
absl::StatusOr<std::string> ConnectToIxia(thinkit::GenericTestbed &testbed) {
  ASSIGN_OR_RETURN(auto gnmi_stub, testbed.Sut().CreateGnmiStub());
  ASSIGN_OR_RETURN(std::vector<IxiaLink> ready_links,
                   GetReadyIxiaLinks(testbed, *gnmi_stub));
  if (ready_links.empty()) {
    return gutil::UnavailableErrorBuilder() << "no Ixia-to-SUT link up";
  }
  absl::string_view ixia_interface = ready_links[0].ixia_interface;
  ASSIGN_OR_RETURN(ixia::IxiaPortInfo ixia_port_info,
                   ixia::ExtractPortInfo(ixia_interface));
  ASSIGN_OR_RETURN(
      std::string ixia_connection_handle,
      pins_test::ixia::IxiaConnect(ixia_port_info.hostname, testbed));
  return ixia_connection_handle;
}

// Installs the given table `entries` using the given P4Runtime session,
// respecting dependencies between entries by sequencing them into batches
// according to `p4info`.
absl::Status InstallPdTableEntries(const sai::TableEntries &entries,
                                   const pdpi::IrP4Info &p4info,
                                   pdpi::P4RuntimeSession &p4rt_session) {
  std::vector<p4::v1::TableEntry> pi_entries;
  for (const sai::TableEntry &entry : entries.entries()) {
    ASSIGN_OR_RETURN(pi_entries.emplace_back(),
                     pdpi::PartialPdTableEntryToPiTableEntry(p4info, entry));
  }
  return pdpi::InstallPiTableEntries(&p4rt_session, p4info, pi_entries);
}
absl::Status InstallPdTableEntries(const sai::TableEntries &entries,
                                   const p4::config::v1::P4Info &p4info,
                                   pdpi::P4RuntimeSession &p4rt_session) {
  ASSIGN_OR_RETURN(pdpi::IrP4Info ir_p4info, pdpi::CreateIrP4Info(p4info));
  return InstallPdTableEntries(entries, ir_p4info, p4rt_session);
}

// Returns a set of table entries that will cause a switch to forward all L3
// packets unconditionally out of the given port.
absl::StatusOr<sai::TableEntries>
ConstructEntriesToForwardAllTrafficToGivenPort(absl::string_view p4rt_port_id) {
  // By convention, we use link local IPv6 addresses as neighbor IDs.
  const std::string kNeighborId =
      netaddr::MacAddress(2, 2, 2, 2, 2, 2).ToLinkLocalIpv6Address().ToString();
  return gutil::ParseTextProto<sai::TableEntries>(absl::Substitute(
      R"pb(
        entries {
          l3_admit_table_entry {
            match {}  # Wildcard.
            action { admit_to_l3 {} }
            priority: 1
          }
        }
        entries {
          acl_pre_ingress_table_entry {
            match {}  # Wildcard.
            action { set_vrf { vrf_id: "vrf" } }
            priority: 1
          }
        }
        entries {
          vrf_table_entry {
            match { vrf_id: "vrf" }
            action { no_action {} }
          }
        }
        entries {
          ipv4_table_entry {
            match { vrf_id: "vrf" }
            action { set_nexthop_id { nexthop_id: "nexthop" } }
          }
        }
        entries {
          ipv6_table_entry {
            match { vrf_id: "vrf" }
            action { set_nexthop_id { nexthop_id: "nexthop" } }
          }
        }
        entries {
          nexthop_table_entry {
            match { nexthop_id: "nexthop" }
            action {
              set_ip_nexthop { router_interface_id: "rif" neighbor_id: "$0" }
            }
          }
        }
        entries {
          router_interface_table_entry {
            match { router_interface_id: "rif" }
            action {
              set_port_and_src_mac { port: "$1" src_mac: "66:55:44:33:22:11" }
            }
          }
        }
        entries {
          neighbor_table_entry {
            match { router_interface_id: "rif" neighbor_id: "$0" }
            action { set_dst_mac { dst_mac: "02:02:02:02:02:02" } }
          }
        }
      )pb",
      kNeighborId, p4rt_port_id));
}

// The purpose of this test is to verify that:
// - Incoming IP packets are mapped to queues according to their DSCP.
// - Queue peak information rates (PIRs) are enforced.
// - Queue egress counters increment correctly.
//
// We test this (for each DSCP, for IPv4 & IPv6) by sending test packets of a
// fixed DSCP at line rate, observing the rate at which the SUT forwards them,
// and inferring which queue was used by cross checking against the PIRs of the
// queues, which we configure to be exponentially spaced.
TEST_P(FrontpanelQosTest,
       PacketsGetMappedToCorrectQueuesBasedOnDscpAndQueuePeakRatesAreEnforced) {
  LOG(INFO) << "-- Test started ----------------------------------------------";
  // Pick a testbed with SUT connected to an Ixia on 2 ports, so we can
  // oversubscribe switch egress port.
  auto requirements = gutil::ParseProtoOrDie<thinkit::TestRequirements>(
      R"pb(
        interface_requirements { count: 2 interface_mode: TRAFFIC_GENERATOR }
      )pb");
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<thinkit::GenericTestbed> testbed,
      GetParam().testbed_interface->GetTestbedWithRequirements(requirements));

  // Pick 2 SUT ports connected to the Ixia, one for receiving test packets and
  // one for forwarding them back.
  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, testbed->Sut().CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(std::vector<IxiaLink> ready_links,
                       GetReadyIxiaLinks(*testbed, *gnmi_stub));
  ASSERT_GE(ready_links.size(), 2)
      << "Test requires at least 2 SUT ports connected to an Ixia";
  const std::string kIxiaSrcPort = ready_links[0].ixia_interface;
  const std::string kIxiaDstPort = ready_links[1].ixia_interface;
  const std::string kSutIngressPort = ready_links[0].sut_interface;
  const std::string kSutEgressPort = ready_links[1].sut_interface;
  LOG(INFO) << absl::StrFormat(
      "Test packet route: [Ixia: %s] => [SUT: %s] -> [SUT: %s] => [Ixia: %s]",
      kIxiaSrcPort, kSutIngressPort, kSutEgressPort, kIxiaDstPort);
  ASSERT_OK_AND_ASSIGN(
      const std::string kSutEgressPortScheduler,
      GetSchedulerPolicyNameByEgressPort(kSutEgressPort, *gnmi_stub));
  absl::flat_hash_map<std::string, std::string> p4rt_id_by_interface;
  ASSERT_OK_AND_ASSIGN(p4rt_id_by_interface,
                       GetAllInterfaceNameToPortId(*gnmi_stub));
  ASSERT_OK_AND_ASSIGN(
      const std::string kSutEgressPortP4rtId,
      gutil::FindOrStatus(p4rt_id_by_interface, kSutEgressPort));

  // Configure the switch to send all incomming packets out of the chosen egress
  // port.
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt,
      ConfigureSwitchAndReturnP4RuntimeSession(
          testbed->Sut(), /*gnmi_config=*/std::nullopt, GetParam().p4info));
  ASSERT_OK_AND_ASSIGN(
      const sai::TableEntries kTableEntries,
      ConstructEntriesToForwardAllTrafficToGivenPort(kSutEgressPortP4rtId));
  ASSERT_OK(testbed->Environment().StoreTestArtifact("pd_entries.textproto",
                                                     kTableEntries));
  ASSERT_OK(InstallPdTableEntries(kTableEntries, GetParam().p4info, *sut_p4rt));

  // Fix test parameters and PIRs (peak information rates, in bytes
  // per second) for each DSCP.
  constexpr int64_t kTestFrameSizeInBytes = 1000;               // 1 KB
  constexpr int64_t kTestFrameCount = 30'000'000;               // 30 GB
  constexpr int64_t kTestFramesPerSecond = kTestFrameCount / 3; // for 3 s
  constexpr int64_t kTestFrameSpeedInBytesPerSecond =           // 10 GB/s
      kTestFramesPerSecond * kTestFrameSizeInBytes;
  // We use exponentially spaced PIRs, with a base rate that's high enough for
  // buffers to drain quickly. That way we don't have to drain buffers manually
  // between test traffic flows.
  constexpr int64_t kPirBaseSpeedInBytesPerSecond = 40'000'000; // 40 MB/s.
  const absl::flat_hash_map<std::string, int64_t> kPirByQueueName = {
      {"BE1", 1 * kPirBaseSpeedInBytesPerSecond},
      {"AF1", 2 * kPirBaseSpeedInBytesPerSecond},
      {"AF2", 4 * kPirBaseSpeedInBytesPerSecond},
      {"AF3", 8 * kPirBaseSpeedInBytesPerSecond},
      {"LLQ1", 16 * kPirBaseSpeedInBytesPerSecond},
      {"LLQ2", 32 * kPirBaseSpeedInBytesPerSecond},
      // TODO: Also test strict queues once reconfiguring them is
      // supported.
      // {"AF4", 64 * kPirBaseSpeedInBytesPerSecond},
      // {"NC1", 128 * kPirBaseSpeedInBytesPerSecond},
  };

  // Ensure the test parameters are compatible with the testbed.
  ASSERT_OK_AND_ASSIGN(
      const int64_t kSutIngressPortSpeedInBitsPerSecond,
      GetPortSpeedInBitsPerSecond(kSutIngressPort, *gnmi_stub));
  ASSERT_OK_AND_ASSIGN(const int64_t kSutEgressPortSpeedInBitsPerSecond,
                       GetPortSpeedInBitsPerSecond(kSutEgressPort, *gnmi_stub));
  ASSERT_LE(kTestFrameSpeedInBytesPerSecond,
            kSutIngressPortSpeedInBitsPerSecond / 8)
      << "ingress port is too slow to sustain test packet speed";
  ASSERT_LE(kTestFrameSpeedInBytesPerSecond,
            kSutEgressPortSpeedInBitsPerSecond / 8)
      << "egress port is too slow to sustain test packet speed";
  for (const auto &[queue, pir] : kPirByQueueName) {
    ASSERT_GE(kTestFrameSpeedInBytesPerSecond, 2 * pir)
        << "test packet speed is too low to meaningfully exceed PIR";
  }

  // Before we update the scheduler config, save the current config and prepare
  // to restore it at the end of the test.
  ASSERT_OK_AND_ASSIGN(
      const std::string kInitialSchedulerConfig,
      GetSchedulerPolicyConfig(kSutEgressPortScheduler, *gnmi_stub));
  const auto kRestoreSchedulerConfig = absl::Cleanup([&] {
    // TODO: The switch does not currently accept its own config
    // on the write path, we need to fix it first. Remove this workaround once
    // the issue is addressed.
    std::string fixed_config = absl::StrReplaceAll(kInitialSchedulerConfig,
                                                   {
                                                       {R"(,"weight":"0")", ""},
                                                   });
    EXPECT_OK(UpdateSchedulerPolicyConfig(kSutEgressPortScheduler, fixed_config,
                                          *gnmi_stub))
        << "failed to restore initial scheduler config -- switch config may be "
           "corrupted, causing subsequent test to fail";
  });
  // Update scheduler config.
  {
    absl::flat_hash_map<std::string, SchedulerParameters> params;
    for (auto &[queue, pir] : kPirByQueueName) {
      params[queue].peak_information_rate = pir;
      // To avoid a large initial burst of forwarded packets when we start the
      // test packet flow, we use a minimally-sized token buffer. This is to
      // ensure that the observed information rate will closely matche the peak
      // information rate. See RFC 2698 for details.
      params[queue].excess_burst_size = kTestFrameSizeInBytes;
      // TODO: Consider picking this uniformly from [0, PIR] instead.
      params[queue].committed_information_rate = 0;
      params[queue].committed_burst_size = 0;
    }
    ASSERT_OK(SetSchedulerPolicyParameters(kSutEgressPortScheduler, params,
                                           *gnmi_stub));
  }
  // Dump initial and modified configs, to ease debugging.
  ASSERT_OK(testbed->Environment().StoreTestArtifact(
      absl::StrCat(kSutEgressPortScheduler, "_before_update.json"),
      FormatJsonBestEffort(kInitialSchedulerConfig)));
  ASSERT_OK_AND_ASSIGN(
      std::string updated_scheduler_config,
      GetSchedulerPolicyConfig(kSutEgressPortScheduler, *gnmi_stub));
  ASSERT_OK(testbed->Environment().StoreTestArtifact(
      absl::StrCat(kSutEgressPortScheduler, "_after_update.json"),
      FormatJsonBestEffort(updated_scheduler_config)));

  // Connect to Ixia and fix global parameters.
  ASSERT_OK_AND_ASSIGN(const std::string kIxiaHandle, ConnectToIxia(*testbed));
  ASSERT_OK_AND_ASSIGN(const std::string kIxiaSrcPortHandle,
                       ixia::IxiaVport(kIxiaHandle, kIxiaSrcPort, *testbed));
  ASSERT_OK_AND_ASSIGN(const std::string kIxiaDstPortHandle,
                       ixia::IxiaVport(kIxiaHandle, kIxiaDstPort, *testbed));

  // Actual testing -- inject test IPv4 and IPv6 packets for each DSCP, and
  // check the behavior is as eexpted.
  constexpr int kMaxDscp = 63;
  for (int dscp = 0; dscp <= kMaxDscp; ++dscp) {
    SCOPED_TRACE(absl::StrCat("DSCP = ", dscp));
    for (bool is_ipv4 : {true, false}) {
      SCOPED_TRACE(absl::StrCat("IP version: ", is_ipv4 ? "IPv4" : "IPv6"));

      // Figure out which queue we will be targeting and some queue parameters.
      ASSERT_OK_AND_ASSIGN(
          const std::string kTargetQueue,
          GetQueueNameByDscpAndPort(dscp, kSutEgressPort, *gnmi_stub));
      // TODO(b/230107242: Test strict queues once that is supported.
      if (kTargetQueue == "AF4" || kTargetQueue == "NC1") {
        LOG(WARNING) << "skipping test for unuspported queue '" << kTargetQueue
                     << "'";
        continue;
      }
      ASSERT_OK_AND_ASSIGN(const int kTargetQueuePir,
                           gutil::FindOrStatus(kPirByQueueName, kTargetQueue));
      ASSERT_OK_AND_ASSIGN(
          const QueueCounters kInitialQueueCounters,
          GetGnmiQueueCounters(kSutEgressPort, kTargetQueue, *gnmi_stub));

      // Configure & start test packet flow.
      const std::string kTrafficName =
          absl::StrCat((is_ipv4 ? "IPv4" : "IPv6"), " traffic for DSCP ", dscp,
                       ", targeting queue ", kTargetQueue,
                       " with PIR = ", kTargetQueuePir, " bytes/second");
      SCOPED_TRACE(kTrafficName);
      ASSERT_OK_AND_ASSIGN(const std::string kIxiaTrafficHandle,
                           ixia::SetUpTrafficItem(kIxiaSrcPortHandle,
                                                  kIxiaDstPortHandle,
                                                  kTrafficName, *testbed));
      auto delete_traffic_item = absl::Cleanup([&, kIxiaTrafficHandle] {
        ASSERT_OK(ixia::DeleteTrafficItem(kIxiaTrafficHandle, *testbed));
      });
      auto traffix_parameters = ixia::TrafficParameters{
          .frame_count = kTestFrameCount,
          .frame_size_in_bytes = kTestFrameSizeInBytes,
          .traffic_speed = ixia::FramesPerSecond{kTestFramesPerSecond},
      };
      if (is_ipv4) {
        traffix_parameters.ip_parameters = ixia::Ipv4TrafficParameters{
            .src_ipv4 = netaddr::Ipv4Address(192, 168, 2, dscp + 1),
            .dst_ipv4 = netaddr::Ipv4Address(172, 0, 0, dscp + 1),
            // Set ECN 0 to avoid RED drops.
            .priority = ixia::IpPriority{.dscp = dscp, .ecn = 1},
        };
      } else {
        traffix_parameters.ip_parameters = ixia::Ipv6TrafficParameters{
            .src_ipv6 =
                netaddr::Ipv6Address(0x1000, 0, 0, 0, 0, 0, 0, dscp + 1),
            .dst_ipv6 =
                netaddr::Ipv6Address(0x2000, 0, 0, 0, 0, 0, 0, dscp + 1),
            // Set ECN 0 to avoid RED drops.
            .priority = ixia::IpPriority{.dscp = dscp, .ecn = 0},
        };
      }
      LOG(INFO) << "-- starting " << kTrafficName;
      ASSERT_OK(ixia::SetTrafficParameters(kIxiaTrafficHandle,
                                           traffix_parameters, *testbed));
      // Occasionally the Ixia API cannot keep up and starting traffic fails,
      // so we try up to 3 times.
      ASSERT_OK(pins::TryUpToNTimes(3, /*delay=*/absl::Seconds(1), [&] {
        return ixia::StartTraffic(kIxiaTrafficHandle, kIxiaHandle, *testbed);
      }));
      const absl::Duration kTrafficDuration =
          absl::Seconds(kTestFrameCount / kTestFramesPerSecond);
      LOG(INFO) << "traffic started, waiting for " << kTrafficDuration
                << " to complete";
      absl::SleepFor(kTrafficDuration);

      // Check observed traffic rate against target queue PIR.
      ASSERT_OK_AND_ASSIGN(
          const ixia::TrafficItemStats kIxiaTrafficStats,
          ixia::GetTrafficItemStats(kIxiaHandle, kTrafficName, *testbed));
      const int kObservedTrafficRate =
          ixia::BytesPerSecondReceived(kIxiaTrafficStats);
      LOG(INFO) << "observed traffic rate (bytes/second): "
                << kObservedTrafficRate;
      const int kAbsoluteError = kObservedTrafficRate - kTargetQueuePir;
      const double kRelativeErrorPercent =
          100. * kAbsoluteError / kTargetQueuePir;
      constexpr double kTolerancePercent = 10; // +-10% tolerance.
      if (std::abs(kRelativeErrorPercent) <= kTolerancePercent) {
        LOG(INFO)
            << "observed traffic rate matches expected traffic rate (error: "
            << kRelativeErrorPercent << "%)";
      } else {
        ADD_FAILURE() << "observed traffic rate of " << kObservedTrafficRate
                      << " bytes/second is not within " << kTolerancePercent
                      << "% of the PIR of the queue '" << kTargetQueue
                      << "' targeted by traffic (PIR = " << kTargetQueuePir
                      << " bytes/second, error = " << kRelativeErrorPercent
                      << "%)";
      }

      // Verify that the target egress queue counters incremented.
      const absl::Time kDeadline = absl::Now() + kMaxQueueCounterUpdateTime;
      LOG(INFO) << "polling queue counters (this may take up to "
                << kMaxQueueCounterUpdateTime << ")";
      QueueCounters final_counters, delta_counters;
      do {
        ASSERT_OK_AND_ASSIGN(
            final_counters,
            GetGnmiQueueCounters(kSutEgressPort, kTargetQueue, *gnmi_stub));
        delta_counters = final_counters - kInitialQueueCounters;
      } while (TotalPacketsForQueue(delta_counters) <
                   kIxiaTrafficStats.num_tx_frames() &&
               absl::Now() < kDeadline);
      LOG(INFO) << "queue counters incremented by " << delta_counters;
      SCOPED_TRACE(absl::StrCat("Counters for queue ", kTargetQueue,
                                " did not change as expected within ",
                                ToString(kMaxQueueCounterUpdateTime),
                                " after injecting/receiving back ",
                                kIxiaTrafficStats.num_tx_frames(), "/",
                                kIxiaTrafficStats.num_rx_frames(),
                                " test packets from/at the Ixia.\nBefore: ",
                                ToString(kInitialQueueCounters),
                                "\nAfter :", ToString(final_counters)));
      EXPECT_THAT(delta_counters,
                  ResultOf(TotalPacketsForQueue,
                           Eq(kIxiaTrafficStats.num_tx_frames())));
      EXPECT_THAT(delta_counters, Field(&QueueCounters::num_packets_transmitted,
                                        Eq(kIxiaTrafficStats.num_rx_frames())));
    }
  }
  LOG(INFO) << "-- Test done -------------------------------------------------";
}

struct EcnTestPacketCounters {
  absl::Mutex mutex;
  int num_packets_punted ABSL_GUARDED_BY(mutex) = 0;
  int num_packets_ecn_marked ABSL_GUARDED_BY(mutex) = 0;
};

void ResetEcnTestPacketCounters(EcnTestPacketCounters &packet_receive_info) {
  absl::MutexLock lock(&packet_receive_info.mutex);
  packet_receive_info.num_packets_punted = 0;
  packet_receive_info.num_packets_ecn_marked = 0;
}

// Set up the switch to forward inbound packets to the egress port using
// default route in VRF. The rules will forward all matching packets matching
// source MAC address to the egress port specified.
//
// Also set up a Copy rule to CPU to punt egress packets to test for
// any inspection.
//
absl::Status SetUpForwardingAndCopyEgressToCpu(
    absl::string_view out_port, absl::string_view source_mac,
    absl::string_view dest_mac, const p4::config::v1::P4Info &p4info,
    pdpi::P4RuntimeSession &p4_session) {
  constexpr absl::string_view kVrfId = "vrf-80";
  constexpr absl::string_view kRifOutId = "router-interface";
  constexpr absl::string_view kNextHopId = "nexthop-1";
  constexpr absl::string_view kNeighborIdv6 = "fe80::002:02ff:fe02:0202";
  const absl::string_view kNeighborId = kNeighborIdv6;

  std::vector<sai::TableEntry> pd_entries;
  ASSIGN_OR_RETURN(pd_entries.emplace_back(),
                   gutil::ParseTextProto<sai::TableEntry>(absl::Substitute(
                       R"pb(
                         vrf_table_entry {
                           match { vrf_id: "$0" }
                           action { no_action {} }
                         })pb",
                       kVrfId)));
   ASSIGN_OR_RETURN(
      pd_entries.emplace_back(),
      gutil::ParseTextProto<sai::TableEntry>(absl::Substitute(
          R"pb(
            router_interface_table_entry {
              match { router_interface_id: "$0" }
              action {
                set_port_and_src_mac { port: "$1" src_mac: "66:55:44:33:22:11" }
              }
            }
          )pb",
          kRifOutId, out_port)));

   ASSIGN_OR_RETURN(
      pd_entries.emplace_back(),
      gutil::ParseTextProto<sai::TableEntry>(absl::Substitute(
          R"pb(
            neighbor_table_entry {
              match { router_interface_id: "$0" neighbor_id: "$1" }
              action { set_dst_mac { dst_mac: "02:02:02:02:02:02" } }
            }
          )pb",
          kRifOutId, kNeighborId)));

   ASSIGN_OR_RETURN(
      pd_entries.emplace_back(),
      gutil::ParseTextProto<sai::TableEntry>(absl::Substitute(
          R"pb(
            nexthop_table_entry {
              match { nexthop_id: "$2" }
              action {
                set_ip_nexthop { router_interface_id: "$0" neighbor_id: "$1" }
              }
            }
          )pb",
          kRifOutId, kNeighborId, kNextHopId)));

   ASSIGN_OR_RETURN(pd_entries.emplace_back(),
                   gutil::ParseTextProto<sai::TableEntry>(absl::Substitute(
                       R"pb(
                         ipv4_table_entry {
                           match { vrf_id: "$0" }
                           action { set_nexthop_id { nexthop_id: "$1" } }
                         }
                       )pb",
                       kVrfId, kNextHopId)));

   ASSIGN_OR_RETURN(pd_entries.emplace_back(),
                   gutil::ParseTextProto<sai::TableEntry>(absl::Substitute(
                       R"pb(
                         ipv6_table_entry {
                           match { vrf_id: "$0" }
                           action { set_nexthop_id { nexthop_id: "$1" } }
                         }
                       )pb",
                       kVrfId, kNextHopId)));

   ASSIGN_OR_RETURN(
      pd_entries.emplace_back(),
      gutil::ParseTextProto<sai::TableEntry>(absl::Substitute(
          R"pb(
            acl_pre_ingress_table_entry {
              match { src_mac { value: "$0" mask: "ff:ff:ff:ff:ff:ff" } }
              action { set_vrf { vrf_id: "$1" } }
              priority: 1
            }
          )pb",
          source_mac, kVrfId)));

   ASSIGN_OR_RETURN(
      pd_entries.emplace_back(),
      gutil::ParseTextProto<sai::TableEntry>(
          R"pb(
            acl_ingress_table_entry {
              match {
                dst_mac { value: "02:02:02:02:02:02" mask: "ff:ff:ff:ff:ff:ff" }
              }
              action { acl_copy { qos_queue: "2" } }
              priority: 1
            }
          )pb"));

   ASSIGN_OR_RETURN(
      pd_entries.emplace_back(),
      gutil::ParseTextProto<sai::TableEntry>(absl::Substitute(
          R"pb(
            l3_admit_table_entry {
              match { dst_mac { value: "$0" mask: "FF:FF:FF:FF:FF:FF" } }
              action { admit_to_l3 {} }
              priority: 1
            }
          )pb",
          dest_mac)));

   // Clear table entries
  RETURN_IF_ERROR(pdpi::ClearTableEntries(&p4_session));

    ASSIGN_OR_RETURN(auto ir_p4info, pdpi::CreateIrP4Info(p4info));
  std::vector<p4::v1::TableEntry> pi_entries;
  for (const auto &pd_entry : pd_entries) {
    ASSIGN_OR_RETURN(p4::v1::TableEntry pi_entry,
                     pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, pd_entry),
                     _.SetPrepend()
                         << "Failed in PD table conversion to PI, entry: "
                         << pd_entry.DebugString() << " error: ");
    pi_entries.push_back(pi_entry);
  }

  return (pdpi::InstallPiTableEntries(&p4_session, ir_p4info, pi_entries));
}

bool IsEcnMarked(const packetlib::Packet &packet) {
  if (packet.headers_size() >= 2 &&
      ((packet.headers(1).has_ipv4_header() &&
        packet.headers(1).ipv4_header().ecn() == "0x3") ||
       (packet.headers(1).has_ipv6_header() &&
        packet.headers(1).ipv6_header().ecn() == "0x3"))) {
    return true;
  }
  return false;
}

struct EcnTestIxiaSetUpResult {
  // Ixia reference URLs to topology.
  std::string topology_ref;
  // Ixia reference URLs to traffic.
  std::vector<std::string> traffic_refs;
};

absl::StatusOr<EcnTestIxiaSetUpResult> SetUpIxiaForEcnTest(
    const std::string kIxiaTxPort1, const std::string kIxiaTxPort2,
    const std::string kIxiaRxPort, thinkit::GenericTestbed &testbed) {
  // Extract Ixia chassis, card and port information from the Ixia interface
  // info.
  ASSIGN_OR_RETURN(ixia::IxiaPortInfo ixia_port1,
                   ixia::ExtractPortInfo(kIxiaTxPort1));

  ASSIGN_OR_RETURN(ixia::IxiaPortInfo ixia_port2,
                   ixia::ExtractPortInfo(kIxiaTxPort2));

  ASSIGN_OR_RETURN(ixia::IxiaPortInfo ixia_port3,
                   ixia::ExtractPortInfo(kIxiaRxPort));

  // Connect to Ixia.
  ASSIGN_OR_RETURN(std::string topology_ref,
                   pins_test::ixia::IxiaConnect(ixia_port1.hostname, testbed));
  
  // Get Ixia reference to Ixia ports.
  ASSIGN_OR_RETURN(std::string vport1_ref,
                   pins_test::ixia::IxiaVport(topology_ref, ixia_port1.card,
                                              ixia_port1.port, testbed));

  ASSIGN_OR_RETURN(std::string vport2_ref,
                   pins_test::ixia::IxiaVport(topology_ref, ixia_port2.card,
                                              ixia_port2.port, testbed));

  ASSIGN_OR_RETURN(std::string vport3_ref,
                   pins_test::ixia::IxiaVport(topology_ref, ixia_port3.card,
                                              ixia_port3.port, testbed));

  std::vector<std::string> traffic_refs;
  // Set up traffic items with source and destination ports.
  ASSIGN_OR_RETURN(
      traffic_refs.emplace_back(),
      pins_test::ixia::SetUpTrafficItem(vport1_ref, vport3_ref, testbed));
  
  ASSIGN_OR_RETURN(
      traffic_refs.emplace_back(),
      pins_test::ixia::SetUpTrafficItem(vport2_ref, vport3_ref, testbed));
  return EcnTestIxiaSetUpResult{
      .topology_ref = topology_ref,
      .traffic_refs = traffic_refs,
  };
}

// This test verifies ECN marking due to configured WRED profile on port
// queue. The test verifies the following:
// 1. Switch marks Congestion Encountered bits in the ECN field for
//    ECN capable traffic, when an egress port queue usage exceeds the
//    threshold of the queue management profile configured for the queue.
// 2. No marking when queue usage drops.
// 3. The test also verifies that switch does not mark non-ECN capable traffic
//    even when threshold for queue usage exceeds.
TEST_P(FrontpanelQosTest, TestWredEcnMarking) {
  // Pick a testbed with an Ixia Traffic Generator.
  auto requirements =
      gutil::ParseProtoOrDie<thinkit::TestRequirements>(
          R"pb(interface_requirements {
                 count: 3
                 interface_mode: TRAFFIC_GENERATOR
               })pb");

  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<thinkit::GenericTestbed> testbed,
      GetParam().testbed_interface->GetTestbedWithRequirements(requirements));

  // Set up P4Runtime session.
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<pdpi::P4RuntimeSession> sut_p4_session,
      pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
          testbed->Sut(), /*gnmi_config=*/absl::nullopt, GetParam().p4info));

  // Hook up to GNMI.
  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, testbed->Sut().CreateGnmiStub());

  // Get Ixia connected links.
  const absl::flat_hash_map<std::string, thinkit::InterfaceInfo>
      interface_info = testbed->GetSutInterfaceInfo();
  ASSERT_OK_AND_ASSIGN(std::vector<IxiaLink> ready_links,
                       GetReadyIxiaLinks(*testbed, *gnmi_stub));
  ASSERT_GE(ready_links.size(), 3)
      << "Test requires at least 3 SUT ports connected to an Ixia";

  const std::string kIxiaTxPort1 = ready_links[0].ixia_interface;
  const std::string kSutInPort1 = ready_links[0].sut_interface;
  
  const std::string kIxiaTxPort2 = ready_links[1].ixia_interface;
  const std::string kSutInPort2 = ready_links[1].sut_interface;

  const std::string kIxiaRxPort = ready_links[2].ixia_interface;
  const std::string kSutOutPort = ready_links[2].sut_interface;
      
  // Set the egress port to loopback mode
  // Configure the switch egress port as loopback as we want to loopback the
  // egress packets to test receiver for inspecting the packets.
  EXPECT_OK(SetPortLoopbackMode(false, kSutInPort1, *gnmi_stub));
  EXPECT_OK(SetPortLoopbackMode(false, kSutInPort2, *gnmi_stub));
  EXPECT_OK(SetPortLoopbackMode(true, kSutOutPort, *gnmi_stub));
  absl::Cleanup loopback_cleaner = [&kSutOutPort, &gnmi_stub] {
    EXPECT_OK(SetPortLoopbackMode(false, kSutOutPort, *gnmi_stub));
  };

  // Look up the port IDs used by P4RT for the SUT interfaces
  absl::flat_hash_map<std::string, std::string> port_id_by_interface;
  ASSERT_OK_AND_ASSIGN(port_id_by_interface,
                       GetAllInterfaceNameToPortId(*gnmi_stub));

  ASSERT_OK_AND_ASSIGN(const std::string kSutInPort1Id,
                       gutil::FindOrStatus(port_id_by_interface, kSutInPort1));

  ASSERT_OK_AND_ASSIGN(const std::string kSutInPort2Id,
                       gutil::FindOrStatus(port_id_by_interface, kSutInPort2));

  ASSERT_OK_AND_ASSIGN(std::string kSutOutPortId,
                       gutil::FindOrStatus(port_id_by_interface, kSutOutPort));

  // Listen for punted packets from the SUT.
  EcnTestPacketCounters packet_receive_info;

  ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(GetParam().p4info));

  PacketInReceiver sut_packet_receiver(
      *sut_p4_session, [&](const p4::v1::StreamMessageResponse pi_response) {
        sai::StreamMessageResponse pd_response;
        ASSERT_OK(pdpi::PiStreamMessageResponseToPd(ir_p4info, pi_response,
                                                    &pd_response))
            << " packet in PI to PD failed: " << pi_response.DebugString();
        ASSERT_TRUE(pd_response.has_packet())
            << " received unexpected stream message for packet in: "
            << pd_response.DebugString();
        packetlib::Packet packet =
            packetlib::ParsePacket(pd_response.packet().payload());

	absl::MutexLock lock(&packet_receive_info.mutex);
        // Check if the ECN field of IP header is marked for congestion.
        // Congestion encountered is represented by bits "11" (0x3)
        if (IsEcnMarked(packet)) {
          packet_receive_info.num_packets_ecn_marked++;
        }
        packet_receive_info.num_packets_punted++;
      });

  // We will perform the following base steps with Ixia:
  // Set up 2 Ixia traffic items.
  // Set up source mac and destination mac address.
  // Set initial frame rates for the 2 items.

  // Flow details.
  const auto kSourceMac =
      netaddr::MacAddress(0x00, 0x01, 0x02, 0x03, 0x04, 0x05);
  const auto kDestMac = netaddr::MacAddress(0x02, 0x02, 0x02, 0x02, 0x02, 0x01);
  const auto kSourceIpv4 = netaddr::Ipv4Address(192, 168, 0, 1);
  const auto kDestIpv4 = netaddr::Ipv4Address(172, 0, 0, 1);

  const auto kSourceIpv6 =
      netaddr::Ipv6Address(0x1000, 0, 0, 0, 0, 0, 0, 0x1);  // 1000::1
  const auto kDestIpv6 =
      netaddr::Ipv6Address(0x2000, 0, 0, 0, 0, 0, 0, 0x1);  // 2000::1

  ASSERT_OK_AND_ASSIGN(
      EcnTestIxiaSetUpResult ixia_setup_result,
      SetUpIxiaForEcnTest(kIxiaTxPort1, kIxiaTxPort2, kIxiaRxPort, *testbed));

  ASSERT_EQ(ixia_setup_result.traffic_refs.size(), 2)
      << "Test requires 2 traffic streams";

  // Set up flow for Traffic 1.

  // Get port speed in bits per second.
  ASSERT_OK_AND_ASSIGN(int64_t in_port1_speed_bps,
                       GetPortSpeedInBitsPerSecond(kSutInPort1, *gnmi_stub));

  constexpr int kDefaultFrameSizeinBytes = 1514;

  double frame_rate_at_line_speed_of_in_port1 =
      in_port1_speed_bps / (kDefaultFrameSizeinBytes * 8);

  absl::string_view traffic_ref1 = ixia_setup_result.traffic_refs[0];
  absl::string_view traffic_ref2 = ixia_setup_result.traffic_refs[1];

  ASSERT_OK(pins_test::ixia::SetFrameSize(traffic_ref1,
                                          kDefaultFrameSizeinBytes, *testbed));

  ASSERT_OK(pins_test::ixia::SetSrcMac(traffic_ref1, kSourceMac.ToString(),
                                       *testbed));

  ASSERT_OK(
      pins_test::ixia::SetDestMac(traffic_ref1, kDestMac.ToString(), *testbed));

  // Set up flow for Traffic 2.
 
  // Get port speed in bits per second.
  ASSERT_OK_AND_ASSIGN(auto in_port2_speed,
                       GetPortSpeedInBitsPerSecond(kSutInPort2, *gnmi_stub));

  uint64_t frame_rate_at_line_speed_of_in_port2 =
      in_port2_speed / (kDefaultFrameSizeinBytes * 8);
  ASSERT_OK(pins_test::ixia::SetFrameRate(
      traffic_ref2, frame_rate_at_line_speed_of_in_port2, *testbed));
  ASSERT_OK(pins_test::ixia::SetFrameSize(traffic_ref2,
                                          kDefaultFrameSizeinBytes, *testbed));

  ASSERT_OK(pins_test::ixia::SetSrcMac(traffic_ref2, kSourceMac.ToString(),
                                       *testbed));

  ASSERT_OK(
      pins_test::ixia::SetDestMac(traffic_ref2, kDestMac.ToString(), *testbed));

  // Get DSCP-to-queue mapping from switch config.
  using QueueNameByDscp = absl::flat_hash_map<int, std::string>;
  ASSERT_OK_AND_ASSIGN(std::optional<QueueNameByDscp> queue_name_by_ipv4_dscp,
                       ParseIpv4DscpToQueueMapping(kSutOutPort));
  ASSERT_OK_AND_ASSIGN(std::optional<QueueNameByDscp> queue_name_by_ipv6_dscp,
		       ParseIpv4DscpToQueueMapping(kSutOutPort));
  const std::string kDefaultQueueName = "BE1";

  // Set up the switch to forward inbound packets to the egress port
  EXPECT_OK(SetUpForwardingAndCopyEgressToCpu(
      kSutOutPortId, kSourceMac.ToString(), kDestMac.ToString(),
      GetParam().p4info, *sut_p4_session));

   // Test ECN marking for IPv4 then IPv6 traffic.
  for (bool is_ipv4 : {false, true}) {
    // Test for ECT and non-ECT traffic
    for (bool is_ect : {false, true}) {
      // 1. Start with no congestion
      // 2. Increase traffic to mimic congestion and then
      // 3. Decrease traffic to drain congestion.
      for (bool is_congestion : {false, true, false}) {
        LOG(INFO) << "========================";
        if (is_ipv4) {
          ASSERT_OK(pins_test::ixia::AppendIPv4(traffic_ref1, *testbed));
          ASSERT_OK(pins_test::ixia::SetSrcIPv4(
              traffic_ref1, kSourceIpv4.ToString(), *testbed));
          ASSERT_OK(pins_test::ixia::SetDestIPv4(
              traffic_ref1, kDestIpv4.ToString(), *testbed));
          ASSERT_OK(pins_test::ixia::AppendIPv4(traffic_ref2, *testbed));
          ASSERT_OK(pins_test::ixia::SetSrcIPv4(
              traffic_ref2, kSourceIpv4.ToString(), *testbed));
          ASSERT_OK(pins_test::ixia::SetDestIPv4(
              traffic_ref2, kDestIpv4.ToString(), *testbed));
        } else {
          ASSERT_OK(pins_test::ixia::AppendIPv6(traffic_ref1, *testbed));
          ASSERT_OK(pins_test::ixia::SetSrcIPv6(
              traffic_ref1, kSourceIpv6.ToString(), *testbed));
          ASSERT_OK(pins_test::ixia::SetDestIPv6(
              traffic_ref1, kDestIpv6.ToString(), *testbed));
          ASSERT_OK(pins_test::ixia::AppendIPv6(traffic_ref2, *testbed));
          ASSERT_OK(pins_test::ixia::SetSrcIPv6(
              traffic_ref2, kSourceIpv6.ToString(), *testbed));
          ASSERT_OK(pins_test::ixia::SetDestIPv6(
              traffic_ref2, kDestIpv6.ToString(), *testbed));
        }

	 constexpr int kDscp = 8;
        // ECN field (2bits): ECN capable     = "10"
        //                    Non ECN capable = "00"
        constexpr int kEcnCapableBits = 0b10;
        constexpr int kNonEcnCapableBits = 0b00;

	ASSERT_OK(pins_test::ixia::SetIpPriority(
            traffic_ref1, kDscp, is_ect ? kEcnCapableBits : kNonEcnCapableBits,
            is_ipv4, *testbed));
        ASSERT_OK(pins_test::ixia::SetIpPriority(
            traffic_ref2, kDscp, is_ect ? kEcnCapableBits : kNonEcnCapableBits,
            is_ipv4, *testbed));

	if (is_congestion) {
          // When setting frame rate in frames per second
          // lets add by 1, to be just above line rate.
          ASSERT_OK(pins_test::ixia::SetFrameRate(
              traffic_ref1, frame_rate_at_line_speed_of_in_port1 + 1,
              *testbed));

          // TODO : kWredMaxThresholdInBytes is currently
          // hardcoded in test. Get configured threshold configured from
          // switch.
          constexpr int kWredMaxThresholdInBytes = 80000;
          // Send additional packets (twice the threshold) from second port,
          // to ensure threshold is crossed.
          ASSERT_OK(pins_test::ixia::SetFrameCount(
              traffic_ref2,
              (kWredMaxThresholdInBytes * 2 / kDefaultFrameSizeinBytes),
              *testbed));
        } else {
          // Set traffic to 80 percent of line rate.
          ASSERT_OK(pins_test::ixia::SetFrameRate(
              traffic_ref1, frame_rate_at_line_speed_of_in_port1 * 80 / 100,
              *testbed));

	   // Do not send traffic-2 as we do not want congestion.
          ASSERT_OK(pins_test::ixia::SetFrameCount(traffic_ref2, 0, *testbed));
        }

	std::string target_queue = kDefaultQueueName;
        if (queue_name_by_ipv4_dscp.has_value()) {
          target_queue = gutil::FindOrDefault(*queue_name_by_ipv4_dscp, kDscp,
                                              kDefaultQueueName);
        } else if (queue_name_by_ipv6_dscp.has_value()) {
          target_queue = gutil::FindOrDefault(*queue_name_by_ipv6_dscp, kDscp,
                                              kDefaultQueueName);
        }

	 // Read counters of the target queue.
        ASSERT_OK_AND_ASSIGN(
            const QueueCounters queue_counters_before_test_packet,
            GetGnmiQueueCounters(/*port=*/kSutOutPort, /*queue=*/target_queue,
                                 *gnmi_stub));
        ASSERT_OK(pins::TryUpToNTimes(3, /*delay=*/absl::Seconds(1), [&] {
          return pins_test::ixia::StartTraffic(ixia_setup_result.traffic_refs,
                                               ixia_setup_result.topology_ref,
                                               *testbed);
        }));

	// Time to allow initial burst and to reach steady state queue usage.
        constexpr absl::Duration kCongestionTime = absl::Seconds(2);

        // Time period to examine egress packets for ECN marking.
        constexpr absl::Duration kStatsCollectionTime = absl::Seconds(5);

        // Wait for traffic to buffer.
        absl::SleepFor(kCongestionTime);

	ResetEcnTestPacketCounters(packet_receive_info);
        absl::SleepFor(kStatsCollectionTime);

        {
          // We will be verifying for congestion bit in sampled packets
          // received at Receiver.
          absl::MutexLock lock(&packet_receive_info.mutex);
          LOG(INFO) << "Congestion : " << (is_congestion ? "true" : "false");
          LOG(INFO) << "IPv4 : " << (is_ipv4 ? "true" : "false");
          LOG(INFO) << "ECT : " << (is_ect ? "true" : "false");
          LOG(INFO) << "Packets received: "
                    << packet_receive_info.num_packets_punted;
          LOG(INFO) << "ECN marked Packets: "
                    << packet_receive_info.num_packets_ecn_marked;

          if (is_congestion && is_ect) {
            // TODO: Currently we are unable to keep queue usage
            // constantly above threshold. The queue usage starts going down in
            // a few seconds. Till we understand this, we will allow for
            // tolerance in packets marked for ECN.
            constexpr float kTolerancePercent = 20.0;
            if (testbed->Environment().MaskKnownFailures()) {
              // Egress packets must be ECN marked. Tolerance of 20%.
              ASSERT_GE(packet_receive_info.num_packets_ecn_marked,
                        packet_receive_info.num_packets_punted *
                            (1 - kTolerancePercent / 100));
            } else {
              // All egress packets must be ECN marked.
              ASSERT_EQ(packet_receive_info.num_packets_punted,
                        packet_receive_info.num_packets_ecn_marked);
            }
          } else {
            // No egress packets must be ECN marked.
            ASSERT_EQ(packet_receive_info.num_packets_ecn_marked, 0);
          }
        }
        ASSERT_OK(pins_test::ixia::StopTraffic(ixia_setup_result.traffic_refs,
                                               *testbed));

	// Wait for a bit to collect queue statistics.
        constexpr absl::Duration kQueueStatsWaitTime = absl::Seconds(5);
        absl::SleepFor(kQueueStatsWaitTime);

	// Read counters of the target queue.
        ASSERT_OK_AND_ASSIGN(
            const QueueCounters queue_counters_after_test_packet,
            GetGnmiQueueCounters(/*port=*/kSutOutPort, /*queue=*/target_queue,
                                 *gnmi_stub));

	// This test expects WRED config to only mark packets and not drop.
        // Expect no drops in target queue and queue transmit counter
        // increments.
        EXPECT_EQ(queue_counters_after_test_packet.num_packets_dropped,
                  queue_counters_before_test_packet.num_packets_dropped);

        EXPECT_GT(queue_counters_after_test_packet.num_packets_transmitted,
                  queue_counters_before_test_packet.num_packets_transmitted);
      }
    }
  }
}
}  // namespace pins_test
