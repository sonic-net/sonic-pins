// Copyright (c) 2024, Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "tests/integration/system/packet_forwarding_tests.h"

#include <memory>
#include <new>
#include <optional>
#include <string>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/flags/flag.h"
#include "absl/numeric/int128.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/synchronization/mutex.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "lib/basic_traffic/basic_p4rt_util.h"
#include "lib/basic_traffic/basic_traffic.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/p4rt/p4rt_programming_context.h"
#include "lib/utils/generic_testbed_utils.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.pb.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "tests/lib/p4info_helper.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "thinkit/control_device.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/proto/generic_testbed.pb.h"
#include "thinkit/switch.h"

namespace pins_test {
namespace {

constexpr int kMtu[] = {1500, 5000, 9000};

// Test packet proto message sent from control switch to sut.
constexpr absl::string_view kTestPacket = R"pb(
  headers {
    ethernet_header {
      ethernet_destination: "02:03:04:05:06:07"
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
      protocol: "0x11"
      ipv4_source: "1.2.3.4"
      ipv4_destination: "$0"
    }
  }
  headers { udp_header { source_port: "0x0000" destination_port: "0x0000" } }
  payload: "Basic L3 test packet")pb";

absl::StatusOr<p4::config::v1::P4Info> GetP4InfoFromParamOrSUT(
    const pins_test::PacketForwardingTestParams& params, thinkit::Switch& sut) {
  static const auto* const kP4Info =
      new auto([&]() -> absl::StatusOr<p4::config::v1::P4Info> {
        if (params.p4_info.has_value()) {
          return *params.p4_info;
        }
        return pins::GetP4InfoFromSUT(sut);
      }());
  return *kP4Info;
}

// Pushes the P4 Info to SUT if the param push_p4_info is set to true and
// returns the P4 Runtime Session
absl::StatusOr<std::unique_ptr<pdpi::P4RuntimeSession>> P4InfoPush(
    bool push_p4_info, const p4::config::v1::P4Info& p4_info,
    thinkit::GenericTestbed& testbed) {
  std::optional<p4::config::v1::P4Info> p4info = std::nullopt;
  if (push_p4_info) {
    p4info = p4_info;
  }
  return ConfigureSwitchAndReturnP4RuntimeSession(
      testbed.Sut(), /*gnmi_config=*/std::nullopt, p4info);
}

TEST_P(PacketForwardingTestFixture, PacketForwardingTest) {
  thinkit::TestRequirements requirements =
      gutil::ParseProtoOrDie<thinkit::TestRequirements>(
          R"pb(interface_requirements {
                 count: 2
                 interface_mode: CONTROL_INTERFACE
               })pb");

  ASSERT_OK_AND_ASSIGN(auto testbed, GetTestbedWithRequirements(requirements));

  std::vector<InterfaceLink> control_links =
      FromTestbed(GetAllControlLinks, *testbed);

  ASSERT_OK_AND_ASSIGN(auto stub, testbed->Sut().CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(auto port_id_by_interface,
                       GetAllInterfaceNameToPortId(*stub));

  // Set the `source_link` to the first SUT control link.
  const InterfaceLink& source_link = control_links[0];
  ASSERT_OK_AND_ASSIGN(
      std::string source_port_id_value,
      gutil::FindOrStatus(port_id_by_interface, source_link.sut_interface));

  // Set the `destination_link` to the second SUT control link.
  const InterfaceLink& destination_link = control_links[1];
  ASSERT_OK_AND_ASSIGN(std::string destination_port_id_value,
                       gutil::FindOrStatus(port_id_by_interface,
                                           destination_link.sut_interface));

  LOG(INFO) << "Source port: " << source_link.sut_interface
            << " port id: " << source_port_id_value;
  LOG(INFO) << "Destination port: " << destination_link.sut_interface
            << " port id: " << destination_port_id_value;

  ASSERT_OK_AND_ASSIGN(p4::config::v1::P4Info p4_info,
                       GetP4InfoFromParamOrSUT(GetParam(), testbed->Sut()));
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<pdpi::P4RuntimeSession> p4_session,
                       P4InfoPush(GetParam().push_p4_info, p4_info, *testbed));
  // Set up a route between the source and destination interfaces.
  ASSERT_OK_AND_ASSIGN(auto port_id_from_sut_interface,
                       GetAllInterfaceNameToPortId(*stub));
  ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(p4_info));
  P4rtProgrammingContext p4rt_context(p4_session.get(),
                                      pdpi::SetMetadataAndSendPiWriteRequest);
  ASSERT_OK(basic_traffic::ProgramRoutes(
      p4rt_context.GetWriteRequestFunction(), ir_p4info,
      port_id_from_sut_interface,
      {{.ingress_interface = source_link.sut_interface,
        .egress_interface = destination_link.sut_interface}}));

  int destination_port_id;
  ASSERT_TRUE(
      absl::SimpleAtoi(destination_port_id_value, &destination_port_id));

  // Make test packet based on destination port ID.
  const auto test_packet =
      gutil::ParseProtoOrDie<packetlib::Packet>(absl::Substitute(
          kTestPacket, basic_traffic::PortIdToIP(destination_port_id)));
  ASSERT_OK_AND_ASSIGN(std::string test_packet_data,
                       packetlib::SerializePacket(test_packet));

  absl::Mutex mutex;
  std::vector<std::string> received_packets;
  static constexpr int kPacketsToSend = 10;
  {
    ASSERT_OK_AND_ASSIGN(auto finalizer,
                         testbed.get()->ControlDevice().CollectPackets());

    LOG(INFO) << "Sending Packet to " << source_link.peer_interface;
    LOG(INFO) << "Test packet data: " << test_packet.DebugString();

    for (int i = 0; i < kPacketsToSend; i++) {
      // Send packet to SUT.
      ASSERT_OK(testbed->ControlDevice().SendPacket(source_link.peer_interface,
                                                    test_packet_data))
          << "failed to inject the packet.";
      LOG(INFO) << "SendPacket completed";
    }
    ASSERT_OK(finalizer->HandlePacketsFor(
        absl::Seconds(30),
        [&](absl::string_view interface, absl::string_view packet) {
          if (interface != destination_link.peer_interface) {
            return;
          }
          packetlib::Packet parsed_packet = packetlib::ParsePacket(packet);
          if (!absl::StrContains(parsed_packet.payload(),
                                 "Basic L3 test packet")) {
            return;
          }
          absl::MutexLock lock(&mutex);
          received_packets.push_back(std::string(packet));
        }));
  }
  EXPECT_EQ(received_packets.size(), kPacketsToSend);
}

using InterfaceCounters = absl::flat_hash_map<std::string, Counters>;

TEST_P(PacketForwardingTestFixture, AllPortsPacketForwardingTest) {
  thinkit::TestRequirements requirements =
      gutil::ParseProtoOrDie<thinkit::TestRequirements>(
          R"pb(interface_requirements {
                 count: 2
                 interface_mode: CONTROL_INTERFACE
               })pb");

  ASSERT_OK_AND_ASSIGN(auto testbed, GetTestbedWithRequirements(requirements));

  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, testbed->Sut().CreateGnmiStub());
  std::vector<std::string> sut_interfaces =
      GetSutInterfaces(FromTestbed(GetAllControlLinks, *testbed));

  ASSERT_OK_AND_ASSIGN(p4::config::v1::P4Info p4_info,
                       GetP4InfoFromParamOrSUT(GetParam(), testbed->Sut()));
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<pdpi::P4RuntimeSession> p4_session,
                       P4InfoPush(GetParam().push_p4_info, p4_info, *testbed));
  ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(p4_info));

  // Collect counters before the test.
  ASSERT_OK_AND_ASSIGN(InterfaceCounters pretraffic_counters,
                       GetAllInterfaceCounters(*gnmi_stub));

  const auto test_packet =
      gutil::ParseProtoOrDie<packetlib::Packet>(kTestPacket);
  ASSERT_OK_AND_ASSIGN(
      auto statistics,
      basic_traffic::SendTraffic(*testbed, p4_session.get(), ir_p4info,
                                 basic_traffic::AllToAll(sut_interfaces),
                                 {test_packet}, absl::Minutes(5)));

  // Collate traffic statistics to dump to artifacts.
  std::string packet_statistics_csv =
      "ingress_interface,egress_interface,packets_sent,packets_received\n";
  for (const basic_traffic::TrafficStatistic& statistic : statistics) {
    absl::StrAppend(&packet_statistics_csv,
                    absl::StrJoin({statistic.interfaces.ingress_interface,
                                   statistic.interfaces.egress_interface,
                                   absl::StrCat(statistic.packets_sent),
                                   absl::StrCat(statistic.packets_received)},
                                  ","),
                    "\n");
    EXPECT_EQ(statistic.packets_sent, statistic.packets_received);
    EXPECT_EQ(statistic.packets_routed_incorrectly, 0);
  }
  EXPECT_OK(testbed->Environment().StoreTestArtifact("traffic_statistics.csv",
                                                     packet_statistics_csv));

  // Calculate counter differences and dump to artifacts.
  std::string sut_counters_csv = "interface,in_packets,out_packets\n";
  ASSERT_OK_AND_ASSIGN(InterfaceCounters posttraffic_counters,
                       GetAllInterfaceCounters(*gnmi_stub));
  for (const std::string& interface : sut_interfaces) {
    const Counters& pre = pretraffic_counters[interface];
    const Counters& post = posttraffic_counters[interface];
    absl::StrAppend(
        &sut_counters_csv,
        absl::StrJoin({interface, absl::StrCat(post.in_pkts - pre.in_pkts),
                       absl::StrCat(post.out_pkts - pre.out_pkts)},
                      ","),
        "\n");
  }
  EXPECT_OK(testbed->Environment().StoreTestArtifact("sut_counters.csv",
                                                     sut_counters_csv));
}

TEST_P(PacketForwardingTestFixture, MtuPacketForwardingTest) {
  thinkit::TestRequirements requirements =
      gutil::ParseProtoOrDie<thinkit::TestRequirements>(
          R"pb(interface_requirements {
                 count: 2
                 interface_mode: CONTROL_INTERFACE
               })pb");

  ASSERT_OK_AND_ASSIGN(auto testbed, GetTestbedWithRequirements(requirements));

  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, testbed->Sut().CreateGnmiStub());
  std::vector<std::string> sut_interfaces =
      GetSutInterfaces(FromTestbed(GetAllControlLinks, *testbed));

  ASSERT_OK_AND_ASSIGN(p4::config::v1::P4Info p4_info,
                       GetP4InfoFromParamOrSUT(GetParam(), testbed->Sut()));
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<pdpi::P4RuntimeSession> p4_session,
                       P4InfoPush(GetParam().push_p4_info, p4_info, *testbed));
  ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(p4_info));

  for (int mtu : kMtu) {
    // Collect counters before the test.
    ASSERT_OK_AND_ASSIGN(InterfaceCounters pretraffic_counters,
                         GetAllInterfaceCounters(*gnmi_stub));

    LOG(INFO) << "MTU: " << mtu;
    auto test_packet = gutil::ParseProtoOrDie<packetlib::Packet>(kTestPacket);
    ASSERT_OK(PadPacket(mtu, test_packet));
    LOG(INFO) << "Packet: " << test_packet.DebugString();
    ASSERT_OK_AND_ASSIGN(
        auto statistics,
        basic_traffic::SendTraffic(*testbed, p4_session.get(), ir_p4info,
                                   basic_traffic::AllToAll(sut_interfaces),
                                   {test_packet}, absl::Minutes(5)));

    // Collate traffic statistics to dump to artifacts.
    std::string packet_statistics_csv =
        "ingress_interface,egress_interface,packets_sent,packets_received\n";
    for (const basic_traffic::TrafficStatistic& statistic : statistics) {
      absl::StrAppend(&packet_statistics_csv,
                      absl::StrJoin({statistic.interfaces.ingress_interface,
                                     statistic.interfaces.egress_interface,
                                     absl::StrCat(statistic.packets_sent),
                                     absl::StrCat(statistic.packets_received)},
                                    ","),
                      "\n");
      EXPECT_EQ(statistic.packets_sent, statistic.packets_received);
      EXPECT_EQ(statistic.packets_routed_incorrectly, 0);
    }
    EXPECT_OK(testbed->Environment().StoreTestArtifact(
        absl::StrCat("traffic_statistics_mtu", mtu, ".csv"),
        packet_statistics_csv));

    // Calculate counter differences and dump to artifacts.
    std::string sut_counters_csv = "interface,in_packets,out_packets\n";
    ASSERT_OK_AND_ASSIGN(InterfaceCounters posttraffic_counters,
                         GetAllInterfaceCounters(*gnmi_stub));
    for (const std::string& interface : sut_interfaces) {
      const Counters& pre = pretraffic_counters[interface];
      const Counters& post = posttraffic_counters[interface];
      absl::StrAppend(
          &sut_counters_csv,
          absl::StrJoin({interface, absl::StrCat(post.in_pkts - pre.in_pkts),
                         absl::StrCat(post.out_pkts - pre.out_pkts)},
                        ","),
          "\n");
    }
    EXPECT_OK(testbed->Environment().StoreTestArtifact(
        absl::StrCat("sut_counters_mtu", mtu, ".csv"), sut_counters_csv));
  }
}

}  // namespace
}  // namespace pins_test
