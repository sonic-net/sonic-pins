#include <optional>

#include "absl/cleanup/cleanup.h"
#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "lib/ixia_helper.h"
#include "lib/ixia_helper.pb.h"
#include "p4_infra/netaddr/mac_address.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4_infra/p4_pdpi/pd.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "tests/forwarding/util.h"
#include "tests/gnmi/ethcounter_ixia_test.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "tests/qos/qos_test_util.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/proto/generic_testbed.pb.h"
#include "thinkit/switch.h"

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
ConstructEntriesToForwardAllTrafficToGivenPort(std::string_view p4rt_port_id) {
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

absl::StatusOr<ResultWithTimestamp> GetGnmiPortStatAndTimestamp(
    std::string_view stat_name, std::string_view iface,
    gnmi::gNMI::StubInterface *gnmi_stub) {
  std::string ops_state_path;
  std::string ops_parse_str;

  if (absl::StartsWith(stat_name, "ipv4-")) {
    std::string_view name = stat_name.substr(5);
    ops_state_path = absl::StrCat(
        "interfaces/interface[name=", iface,
        "]subinterfaces/subinterface[index=0]/ipv4/state/counters/", name);
    ops_parse_str = absl::StrCat("openconfig-if-ip:", name);
  } else if (absl::StartsWith(stat_name, "ipv6-")) {
    std::string_view name = stat_name.substr(5);
    ops_state_path = absl::StrCat(
        "interfaces/interface[name=", iface,
        "]subinterfaces/subinterface[index=0]/ipv6/state/counters/", name);
    ops_parse_str = absl::StrCat("openconfig-if-ip:", name);
  } else {
    ops_state_path = absl::StrCat("interfaces/interface[name=", iface,
                                  "]/state/counters/", stat_name);
    ops_parse_str = absl::StrCat("openconfig-interfaces:", stat_name);
  }

  return GetGnmiStatePathAndTimestamp(gnmi_stub, ops_state_path, ops_parse_str);
}

constexpr absl::Duration kCounterPollInterval = absl::Seconds(30);
// Tolerance = 1% timestamp accuracy +
//             1% (Ixia clock drift + switch queueing variance) +
//             2% test tolerance.
constexpr float kTolerancePercent = .04;

TEST_P(CountersTestFixture, PortCountersTimestamp) {
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
  testbed->Environment().SetTestCaseID("0858826a-092f-448f-b2ba-44603b2c0eeb");

  // Pick 2 SUT ports connected to the Ixia, one for receiving test packets and
  // one for forwarding them back.
  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, testbed->Sut().CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(std::vector<ixia::IxiaLink> ready_links,
                       ixia::GetReadyIxiaLinks(*testbed, *gnmi_stub));
  ASSERT_GE(ready_links.size(), 2)
      << "Test requires at least 2 SUT ports connected to an Ixia";
  const std::string ixia_src_port = ready_links[0].ixia_interface;
  const std::string ixia_dst_port = ready_links[1].ixia_interface;
  const std::string sut_ingress_port = ready_links[0].sut_interface;
  const std::string sut_egress_port = ready_links[1].sut_interface;
  LOG(INFO) << absl::StrFormat(
      "Test packet route: [Ixia: %s] => [SUT: %s] -> [SUT: %s] => [Ixia: %s]",
      ixia_src_port, sut_ingress_port, sut_egress_port, ixia_dst_port);

  // Connect to Ixia and fix some parameters.
  ASSERT_OK_AND_ASSIGN(const std::string ixia_handle,
                       ixia::ConnectToIxia(*testbed));
  ASSERT_OK_AND_ASSIGN(const std::string ixia_src_port_handle,
                       ixia::IxiaVport(ixia_handle, ixia_src_port, *testbed));
  ASSERT_OK_AND_ASSIGN(const std::string ixia_dst_port_handle,
                       ixia::IxiaVport(ixia_handle, ixia_dst_port, *testbed));

  // Configure & start test packet flow.
  ASSERT_OK_AND_ASSIGN(
      const std::string ixia_traffic_handle,
      ixia::SetUpTrafficItem(ixia_src_port_handle, ixia_dst_port_handle,
                             "Port counter traffic", *testbed));
  auto delete_traffic_item = absl::Cleanup([&, ixia_traffic_handle] {
    ASSERT_OK(ixia::DeleteTrafficItem(ixia_traffic_handle, *testbed));
  });

  constexpr int64_t kTestFrameSizeInBytes = 1000;  // 1 KB
  const int64_t traffic_rate_in_bits_per_second =
      ready_links[0].sut_interface_bits_per_second * 0.9;
  const int test_frames_per_second =
      (traffic_rate_in_bits_per_second / 8) / kTestFrameSizeInBytes;

  auto traffix_parameters = ixia::TrafficParameters{
      .frame_size_in_bytes = kTestFrameSizeInBytes,
      .traffic_speed = ixia::FramesPerSecond{test_frames_per_second},
  };

  traffix_parameters.ip_parameters = ixia::Ipv4TrafficParameters{
      .src_ipv4 = netaddr::Ipv4Address(192, 168, 2, 0),
      .dst_ipv4 = netaddr::Ipv4Address(172, 0, 0, 0),
      .priority = ixia::IpPriority{.dscp = 0, .ecn = 0},
  };

  ASSERT_OK(ixia::SetTrafficParameters(ixia_traffic_handle, traffix_parameters,
                                       *testbed));
  // Occasionally the Ixia API cannot keep up and starting traffic fails,
  // so we try up to 3 times.
  ASSERT_OK(pins::TryUpToNTimes(3, /*delay=*/absl::Seconds(1), [&] {
    return ixia::StartTraffic(ixia_traffic_handle, ixia_handle, *testbed);
  }));

  ASSERT_OK_AND_ASSIGN(auto initial_packets,
                       GetGnmiPortStatAndTimestamp("in-pkts", sut_ingress_port,
                                                   gnmi_stub.get()));

  ResultWithTimestamp packets_before_test, packet_after_test;

  // Wait for counter timestamp to update at least once after traffic has
  // started.
  ASSERT_OK(pins::TryUpToNTimes(10, /*delay=*/absl::Seconds(1), [&] {
    ASSIGN_OR_RETURN(packets_before_test,
                     GetGnmiPortStatAndTimestamp("in-pkts", sut_ingress_port,
                                                 gnmi_stub.get()));
    if (packets_before_test.timestamp > initial_packets.timestamp &&
        packets_before_test.response != initial_packets.response) {
      return absl::OkStatus();
    }
    return absl::InternalError("Timestamp not updated yet.");
  }));

  int64_t packet_count_before_test, packet_count_after_test;
  ASSERT_TRUE(absl::SimpleAtoi(StripQuotes(packets_before_test.response),
                               &packet_count_before_test));

  absl::SleepFor(kCounterPollInterval);

  ASSERT_OK_AND_ASSIGN(packet_after_test,
                       GetGnmiPortStatAndTimestamp("in-pkts", sut_ingress_port,
                                                   gnmi_stub.get()));

  ASSERT_TRUE(absl::SimpleAtoi(StripQuotes(packet_after_test.response),
                               &packet_count_after_test));

  LOG(INFO) << "Packets before test = " << packet_count_before_test;
  LOG(INFO) << "Packets after test = " << packet_count_after_test;

  int64_t bits_transmitted =
      (packet_count_after_test - packet_count_before_test) *
      kTestFrameSizeInBytes * 8;
  absl::Duration duration = absl::Nanoseconds(packet_after_test.timestamp -
                                              packets_before_test.timestamp);
  int64_t rate_in_bits_per_second =
      bits_transmitted / absl::ToDoubleSeconds(duration);

  LOG(INFO) << "Packets = "
            << packet_count_after_test - packet_count_before_test;
  LOG(INFO) << "Duration = " << duration;

  LOG(INFO) << "Observed rate = " << rate_in_bits_per_second;
  LOG(INFO) << "Send frame rate = " << test_frames_per_second;

  LOG(INFO) << "Rx traffic rate (bits/second): "
            << traffic_rate_in_bits_per_second;

  EXPECT_GE(rate_in_bits_per_second,
            traffic_rate_in_bits_per_second * (1 - kTolerancePercent));
  EXPECT_LE(rate_in_bits_per_second,
            traffic_rate_in_bits_per_second * (1 + kTolerancePercent));
}

TEST_P(CountersTestFixture, PortQueueCountersTimestamp) {
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
  testbed->Environment().SetTestCaseID("e4ad3e8f-f443-46e3-b8bd-e95b3f448a04");

  // Pick 2 SUT ports connected to the Ixia, one for receiving test packets and
  // one for forwarding them back.
  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, testbed->Sut().CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(std::vector<ixia::IxiaLink> ready_links,
                       ixia::GetReadyIxiaLinks(*testbed, *gnmi_stub));
  ASSERT_GE(ready_links.size(), 2)
      << "Test requires at least 2 SUT ports connected to an Ixia";
  const std::string ixia_src_port = ready_links[0].ixia_interface;
  const std::string ixia_dst_port = ready_links[1].ixia_interface;
  const std::string sut_ingress_port = ready_links[0].sut_interface;
  const std::string sut_egress_port = ready_links[1].sut_interface;
  LOG(INFO) << absl::StrFormat(
      "Test packet route: [Ixia: %s] => [SUT: %s] -> [SUT: %s] => [Ixia: %s]",
      ixia_src_port, sut_ingress_port, sut_egress_port, ixia_dst_port);

  absl::flat_hash_map<std::string, std::string> p4rt_id_by_interface;
  ASSERT_OK_AND_ASSIGN(p4rt_id_by_interface,
                       GetAllInterfaceNameToPortId(*gnmi_stub));
  ASSERT_OK_AND_ASSIGN(
      const std::string sut_egress_port_p4rt_id,
      gutil::FindOrStatus(p4rt_id_by_interface, sut_egress_port));

  // Configure the switch to send all incoming packets out of the chosen egress
  // port.
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt,
      ConfigureSwitchAndReturnP4RuntimeSession(
          testbed->Sut(), /*gnmi_config=*/std::nullopt, GetParam().p4_info));
  ASSERT_OK_AND_ASSIGN(
      const sai::TableEntries table_entries,
      ConstructEntriesToForwardAllTrafficToGivenPort(sut_egress_port_p4rt_id));
  const auto cleanup = absl::Cleanup([&] {
    EXPECT_OK(pdpi::ClearTableEntries(sut_p4rt.get()))
        << "failed to clean p4 entries";
  });
  ASSERT_OK(testbed->Environment().StoreTestArtifact("pd_entries.textproto",
                                                     table_entries));
  ASSERT_OK(
      InstallPdTableEntries(table_entries, GetParam().p4_info, *sut_p4rt));

  // Connect to Ixia and fix some parameters.
  ASSERT_OK_AND_ASSIGN(const std::string ixia_handle,
                       ixia::ConnectToIxia(*testbed));
  ASSERT_OK_AND_ASSIGN(const std::string ixia_src_port_handle,
                       ixia::IxiaVport(ixia_handle, ixia_src_port, *testbed));
  ASSERT_OK_AND_ASSIGN(const std::string ixia_dst_port_handle,
                       ixia::IxiaVport(ixia_handle, ixia_dst_port, *testbed));

  // Configure & start test packet flow.
  constexpr char kTrafficName[] = "Port queue counter traffic";
  ASSERT_OK_AND_ASSIGN(
      const std::string ixia_traffic_handle,
      ixia::SetUpTrafficItem(ixia_src_port_handle, ixia_dst_port_handle,
                             kTrafficName, *testbed));
  auto delete_traffic_item = absl::Cleanup([&, ixia_traffic_handle] {
    ASSERT_OK(ixia::DeleteTrafficItem(ixia_traffic_handle, *testbed));
  });

  constexpr int64_t kTestFrameSizeInBytes = 1000;  // 1 KB
  const int64_t traffic_rate_in_bits_per_second =
      ready_links[0].sut_interface_bits_per_second * 0.9;
  const int test_frames_per_second =
      (traffic_rate_in_bits_per_second / 8) / kTestFrameSizeInBytes;

  auto traffix_parameters = ixia::TrafficParameters{
      .frame_size_in_bytes = kTestFrameSizeInBytes,
      .traffic_speed = ixia::FramesPerSecond{test_frames_per_second},
  };

  constexpr int kDscp = 20;
  traffix_parameters.ip_parameters = ixia::Ipv4TrafficParameters{
      .src_ipv4 = netaddr::Ipv4Address(192, 168, 2, 0),
      .dst_ipv4 = netaddr::Ipv4Address(172, 0, 0, 0),
      .priority = ixia::IpPriority{.dscp = kDscp, .ecn = 0},
  };

  ASSERT_OK(ixia::SetTrafficParameters(ixia_traffic_handle, traffix_parameters,
                                       *testbed));
  // Occasionally the Ixia API cannot keep up and starting traffic fails,
  // so we try up to 3 times.
  ASSERT_OK(pins::TryUpToNTimes(3, /*delay=*/absl::Seconds(1), [&] {
    return ixia::StartTraffic(ixia_traffic_handle, ixia_handle, *testbed);
  }));

  // Get DSCP-to-queue mapping from switch config.
  using QueueNameByDscp = absl::flat_hash_map<int, std::string>;
  std::optional<QueueNameByDscp> queue_name_by_ipv4_dscp =
      GetParam().queue_by_dscp;
  std::optional<QueueNameByDscp> queue_name_by_ipv6_dscp =
      GetParam().queue_by_dscp;

  std::string target_queue = "BE1";
  if (queue_name_by_ipv4_dscp.has_value()) {
    target_queue = gutil::FindOrDefault(*queue_name_by_ipv4_dscp, kDscp, "BE1");
  } else if (queue_name_by_ipv6_dscp.has_value()) {
    target_queue = gutil::FindOrDefault(*queue_name_by_ipv6_dscp, kDscp, "BE1");
  }

  // Read counters of the target queue.
  ASSERT_OK_AND_ASSIGN(auto initial_packets,
                       GetGnmiQueueCounterWithTimestamp(
                           /*port=*/sut_egress_port, /*queue=*/target_queue,
                           "transmit-pkts", *gnmi_stub));

  ResultWithTimestamp packets_before_test, packets_after_test;

  // Wait for counter timestamp to update at least once after traffic has
  // started.
  ASSERT_OK(pins::TryUpToNTimes(20, /*delay=*/absl::Seconds(1), [&] {
    // Read counters of the target queue.
    ASSIGN_OR_RETURN(packets_before_test,
                     GetGnmiQueueCounterWithTimestamp(
                         /*port=*/sut_egress_port, /*queue=*/target_queue,
                         "transmit-pkts", *gnmi_stub));

    if (packets_before_test.timestamp > initial_packets.timestamp &&
        packets_before_test.response != initial_packets.response) {
      return absl::OkStatus();
    }
    return absl::InternalError("Timestamp not updated yet.");
  }));

  int64_t packet_count_before_test, packet_count_after_test;
  ASSERT_TRUE(absl::SimpleAtoi(StripQuotes(packets_before_test.response),
                               &packet_count_before_test));

  absl::SleepFor(kCounterPollInterval);

  // Read counters of the target queue.
  ASSERT_OK_AND_ASSIGN(packets_after_test,
                       GetGnmiQueueCounterWithTimestamp(
                           /*port=*/sut_egress_port, /*queue=*/target_queue,
                           "transmit-pkts", *gnmi_stub));

  ASSERT_TRUE(absl::SimpleAtoi(StripQuotes(packets_after_test.response),
                               &packet_count_after_test));

  LOG(INFO) << "Packets before test = " << packet_count_before_test;
  LOG(INFO) << "Packets after test = " << packet_count_after_test;

  int64_t bits_transmitted =
      (packet_count_after_test - packet_count_before_test) *
      kTestFrameSizeInBytes * 8;
  absl::Duration duration = absl::Nanoseconds(packets_after_test.timestamp -
                                              packets_before_test.timestamp);
  int64_t rate_in_bits_per_second =
      bits_transmitted / absl::ToDoubleSeconds(duration);

  // Check observed traffic rate against target queue PIR.
  ASSERT_OK_AND_ASSIGN(
      const ixia::TrafficItemStats ixia_traffic_stats,
      ixia::GetTrafficItemStats(ixia_handle, kTrafficName, *testbed));
  LOG(INFO) << "Packets = "
            << packet_count_after_test - packet_count_before_test;
  LOG(INFO) << "Duration = " << duration;

  LOG(INFO) << "Observed rate = " << rate_in_bits_per_second;
  LOG(INFO) << "Send frame rate = " << traffic_rate_in_bits_per_second;
  const int64_t kRxTrafficRate =
      ixia::BytesPerSecondReceived(ixia_traffic_stats) * 8;
  LOG(INFO) << "Rx traffic rate (bits/second): " << kRxTrafficRate;

  EXPECT_GE(rate_in_bits_per_second, kRxTrafficRate * (1 - kTolerancePercent));
  EXPECT_LE(rate_in_bits_per_second, kRxTrafficRate * (1 + kTolerancePercent));
}
}  // namespace pins_test
