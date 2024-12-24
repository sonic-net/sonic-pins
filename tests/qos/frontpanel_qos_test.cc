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

#include <memory>
#include <thread>  // NOLINT
#include <vector>

#include "absl/cleanup/cleanup.h"
#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/time.h"

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/collections.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/ixia_helper.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/netaddr/ipv4_address.h"
#include "p4_pdpi/netaddr/ipv6_address.h"
#include "p4_pdpi/netaddr/mac_address.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_pdpi/pd.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "dvaas/test_vector.pb.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "tests/qos/packet_in_receiver.h"
#include "tests/qos/qos_test_util.h"

namespace pins_test {

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

TEST_P(FrontpanelQosTest, PacketsGetMappedToCorrectQueuesBasedOnDscp) {
  // Pick a testbed with SUT connected to an Ixia on 2 ports, so we can
  // oversubscribe switch egress port.
  auto requirements = gutil::ParseProtoOrDie<thinkit::TestRequirements>(
      R"pb(
        interface_requirements { count: 2 interface_mode: TRAFFIC_GENERATOR }
      )pb");
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<thinkit::GenericTestbed> testbed,
      GetParam().testbed_interface->GetTestbedWithRequirements(requirements));

  // TODO: actual testing.
}

// Set up the switch to forward inbound packets to the egress port using default
// route in VRF.
// The rules will forward all matching packets matching source MAC address
// to the egress port specified.
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
                set_nexthop { router_interface_id: "$0" neighbor_id: "$1" }
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
  
  return EcnTestIxiaSetUpResult{.topology_ref = topology_ref,
                                .traffic_refs = traffic_refs};
} 

// This test verifies ECN marking due to configured WRED profile on port queue.
// The test verifies the following:
// 1. Switch marks Congestion Encountered bits in the ECN field for
//    ECN capable traffic, when an egress port queue usage exceeds the threshold
//    of the queue management profile configured for the queue.
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
                       GetAllInterfaceNameToPortId(GetParam().gnmi_config));

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
          // hardcoded in test. Get configured threshold configured from switch.
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

	ASSERT_OK(pins_test::ixia::StartTraffic(ixia_setup_result.traffic_refs,
                                                ixia_setup_result.topology_ref,
                                                *testbed));

	// Time to allow initial burst and to reach steady state queue usage.
        constexpr absl::Duration kCongestionTime = absl::Seconds(2);

        // Time period to examine egress packets for ECN marking.
        constexpr absl::Duration kStatsCollectionTime = absl::Seconds(5);

        // Wait for traffic to buffer.
        absl::SleepFor(kCongestionTime);

	ResetEcnTestPacketCounters(packet_receive_info);
        absl::SleepFor(kStatsCollectionTime);

	{
          // We will be verifying for congestion bit in sampled packets received
          // at Receiver.
          absl::MutexLock lock(&packet_receive_info.mutex);
          LOG(INFO) << "Congestion : " << (is_congestion ? "true" : "false");
          LOG(INFO) << "IPv4 : " << (is_ipv4 ? "true" : "false");
          LOG(INFO) << "ECT : " << (is_ect ? "true" : "false");
          LOG(INFO) << "Packets received: "
                    << packet_receive_info.num_packets_punted;
          LOG(INFO) << "ECN marked Packets: "
                    << packet_receive_info.num_packets_ecn_marked;

	  if (is_congestion && is_ect) {
            // All egress packets must be ECN marked.
            ASSERT_EQ(packet_receive_info.num_packets_punted,
                      packet_receive_info.num_packets_ecn_marked);
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
        EXPECT_EQ(queue_counters_after_test_packet.num_packet_dropped,
                  queue_counters_before_test_packet.num_packet_dropped);

	EXPECT_GT(queue_counters_after_test_packet.num_packets_transmitted,
                  queue_counters_before_test_packet.num_packets_transmitted);
      }
    }
  }
}
}  // namespace pins_test
