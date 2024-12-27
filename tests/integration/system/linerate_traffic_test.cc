// Copyright 2024 Google LLC
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

#include "tests/integration/system/linerate_traffic_test.h"

#include <algorithm>
#include <cmath>
#include <complex>
#include <cstdint>
#include <cstdlib>
#include <limits>
#include <memory>
#include <optional>
#include <sstream>
#include <string>
#include <thread>  // NOLINT
#include <tuple>
#include <vector>

#include "absl/cleanup/cleanup.h"
#include "absl/container/btree_set.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/collections.h"
#include "gutil/proto.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/ixia_helper.h"
#include "lib/ixia_helper.pb.h"
#include "lib/utils/json_utils.h"
#include "lib/validator/validator_lib.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/internal/ordered_map.h"
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

namespace pins_test {

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
// - Incoming IP packets are all forwarded by the switch.
TEST_P(LineRateTrafficTest, PortToPortLineRateTrafficTest) {
  // Pick a testbed with SUT connected to an Ixia on 2 ports, one ingress and
  // one egress port.
  auto requirements = gutil::ParseProtoOrDie<thinkit::TestRequirements>(
      R"pb(
        interface_requirements { count: 2 interface_mode: TRAFFIC_GENERATOR }
      )pb");
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<thinkit::GenericTestbed> testbed,
      GetParam().testbed_interface->GetTestbedWithRequirements(requirements));

  // Set test case ID.
  testbed->Environment().SetTestCaseID("d40fa538-a779-44ba-97e8-ac5ed86f66e2");

  // Check switch is ready before starting tests.
  ASSERT_OK(SwitchReady(testbed->Sut()))
      << "Switch ready checks failed before traffic test";

  // Pick 2 SUT ports connected to the Ixia, one for ingress and one for egress.
  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, testbed->Sut().CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(std::vector<ixia::IxiaLink> ready_links,
                       ixia::GetReadyIxiaLinks(*testbed, *gnmi_stub));
  ASSERT_GE(ready_links.size(), 2)
      << "Test requires at least 2 SUT ports connected to an Ixia";
  const std::string kIxiaSrcPort = ready_links[0].ixia_interface;
  const std::string kIxiaDstPort = ready_links[1].ixia_interface;
  const std::string kSutIngressPort = ready_links[0].sut_interface;
  const std::string kSutEgressPort = ready_links[1].sut_interface;
  LOG(INFO) << absl::StrFormat(
      "Test packet route: [Ixia: %s] => [SUT: %s] -> [SUT: %s] => [Ixia: %s]",
      kIxiaSrcPort, kSutIngressPort, kSutEgressPort, kIxiaDstPort);

  absl::flat_hash_map<std::string, std::string> p4rt_id_by_interface;
  ASSERT_OK_AND_ASSIGN(p4rt_id_by_interface,
                       GetAllInterfaceNameToPortId(*gnmi_stub));
  ASSERT_OK_AND_ASSIGN(
      const std::string kSutEgressPortP4rtId,
      gutil::FindOrStatus(p4rt_id_by_interface, kSutEgressPort));

  // Configure the switch to send all incoming packets out of the chosen egress
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

  // Fix test parameters.
  constexpr int64_t kTestFrameSizeInBytes = 5000;     // 5 KB
  constexpr int64_t kTestFrameCount = 3'000'000'000;  // 15 TB
  // 100% for long durations seems to create loss due to PPM mismatch.
  constexpr int64_t kPercentageLineRate = 98;  // 98%

  LOG(INFO) << "Test Parameters: \nTest Frame Count: " << kTestFrameCount
            << "\nTest Frame Size (Bytes): " << kTestFrameSizeInBytes
            << "\nLine Rate: " << kPercentageLineRate;

  ASSERT_OK_AND_ASSIGN(
      const int64_t kSutIngressPortSpeedInBitsPerSecond,
      GetPortSpeedInBitsPerSecond(kSutIngressPort, *gnmi_stub));

  // Connect to Ixia and fix global parameters.
  ASSERT_OK_AND_ASSIGN(const std::string kIxiaHandle,
                       ixia::ConnectToIxia(*testbed));
  ASSERT_OK_AND_ASSIGN(const std::string kIxiaSrcPortHandle,
                       ixia::IxiaVport(kIxiaHandle, kIxiaSrcPort, *testbed));
  ASSERT_OK_AND_ASSIGN(const std::string kIxiaDstPortHandle,
                       ixia::IxiaVport(kIxiaHandle, kIxiaDstPort, *testbed));

  // Run the test for IPv4 and then IPv6.
  for (bool is_ipv4 : {true, false}) {
    SCOPED_TRACE(absl::StrCat("IP version: ", is_ipv4 ? "IPv4" : "IPv6"));

    // Log counters for all queues on the egress port before starting.
    for (const std::string queue :
         {"BE1", "AF1", "AF2", "AF3", "LLQ1", "LLQ2", "AF4", "NC1"}) {
      ASSERT_OK_AND_ASSIGN(
          QueueCounters counters,
          GetGnmiQueueCounters(kSutEgressPort, queue, *gnmi_stub));
      LOG(INFO) << "Initial Counters for " << queue << ": " << counters;
    }

    // Configure & start test packet flow.
    const std::string kTrafficName =
        absl::StrCat((is_ipv4 ? "IPv4" : "IPv6"), " traffic at line rate");
    SCOPED_TRACE(kTrafficName);
    ASSERT_OK_AND_ASSIGN(
        const std::string kIxiaTrafficHandle,
        ixia::SetUpTrafficItem(kIxiaSrcPortHandle, kIxiaDstPortHandle,
                               kTrafficName, *testbed));
    auto delete_traffic_item = absl::Cleanup([&, kIxiaTrafficHandle] {
      ASSERT_OK(ixia::DeleteTrafficItem(kIxiaTrafficHandle, *testbed));
    });
    auto traffic_parameters = ixia::TrafficParameters{
        .frame_count = kTestFrameCount,
        .frame_size_in_bytes = kTestFrameSizeInBytes,
        .traffic_speed = ixia::PercentOfMaxLineRate{kPercentageLineRate},
    };
    if (is_ipv4) {
      traffic_parameters.ip_parameters = ixia::Ipv4TrafficParameters{
          .src_ipv4 = netaddr::Ipv4Address(192, 168, 2, 1),
          .dst_ipv4 = netaddr::Ipv4Address(172, 0, 0, 1),
      };
    } else {
      traffic_parameters.ip_parameters = ixia::Ipv6TrafficParameters{
          .src_ipv6 = netaddr::Ipv6Address(0x1000, 0, 0, 0, 0, 0, 0, 1),
          .dst_ipv6 = netaddr::Ipv6Address(0x2000, 0, 0, 0, 0, 0, 0, 1),
      };
    }
    LOG(INFO) << "Starting " << kTrafficName;
    ASSERT_OK(ixia::SetTrafficParameters(kIxiaTrafficHandle, traffic_parameters,
                                         *testbed));
    // Occasionally the Ixia API cannot keep up and starting traffic fails,
    // so we try up to 3 times.
    ASSERT_OK(pins::TryUpToNTimes(3, /*delay=*/absl::Seconds(1), [&] {
      return ixia::StartTraffic(kIxiaTrafficHandle, kIxiaHandle, *testbed);
    }));

    // Calculate the duration taken to send the traffic in test parameters with
    // a buffer.
    const auto kTestTrafficInBits = kTestFrameCount * kTestFrameSizeInBytes * 8;
    const auto kLineRate =
        kPercentageLineRate * 0.01 * kSutIngressPortSpeedInBitsPerSecond;
    const absl::Duration kTrafficDuration =
        absl::Seconds(kTestTrafficInBits / kLineRate) + absl::Seconds(120);
    LOG(INFO) << "Traffic started, waiting for " << kTrafficDuration
              << " to complete";
    absl::SleepFor(kTrafficDuration);

    ASSERT_OK_AND_ASSIGN(
        const ixia::TrafficItemStats kIxiaTrafficStats,
        ixia::GetTrafficItemStats(kIxiaHandle, kTrafficName, *testbed));

    // Log counters for all queues on the egress port after.
    for (const std::string queue :
         {"BE1", "AF1", "AF2", "AF3", "LLQ1", "LLQ2", "AF4", "NC1"}) {
      ASSERT_OK_AND_ASSIGN(
          QueueCounters counters,
          GetGnmiQueueCounters(kSutEgressPort, queue, *gnmi_stub));
      LOG(INFO) << "Counters for " << queue << ": " << counters;
    }
    EXPECT_EQ(kIxiaTrafficStats.num_tx_frames(),
              kIxiaTrafficStats.num_rx_frames())
        << "Tx and Rx frames are not the same. Packets lost: "
        << kIxiaTrafficStats.num_tx_frames() - kIxiaTrafficStats.num_rx_frames()
        << ". Stats: " << kIxiaTrafficStats.DebugString();

    ASSERT_OK(SwitchReady(testbed->Sut()))
        << "Switch ready checks failed after traffic test";
  }
}
}  // namespace pins_test
