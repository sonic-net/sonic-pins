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
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "artifacts/otg.grpc.pb.h"
#include "artifacts/otg.pb.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "grpcpp/client_context.h"
#include "gtest/gtest.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/utils/generic_testbed_utils.h"
#include "lib/utils/json_utils.h"
#include "lib/validator/validator_lib.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/internal/ordered_map.h"
#include "p4_infra/netaddr/ipv4_address.h"
#include "p4_infra/netaddr/ipv6_address.h"
#include "p4_infra/netaddr/mac_address.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/pd.h"
#include "p4_infra/p4_runtime/p4_runtime_session.h"
#include "p4_infra/packetlib/packetlib.h"
#include "p4_infra/packetlib/packetlib.pb.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "tests/forwarding/util.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "tests/qos/packet_in_receiver.h"
#include "tests/qos/qos_test_util.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/proto/generic_testbed.pb.h"

namespace pins_test {

using ::otg::Openapi;

// Installs the given table `entries` using the given P4Runtime session,
// respecting dependencies between entries by sequencing them into batches
// according to `p4info`.
absl::Status InstallPdTableEntries(const sai::TableEntries &entries,
                                   const pdpi::IrP4Info &p4info,
                                   p4_runtime::P4RuntimeSession &p4rt_session) {
  std::vector<p4::v1::TableEntry> pi_entries;
  for (const sai::TableEntry &entry : entries.entries()) {
    ASSIGN_OR_RETURN(pi_entries.emplace_back(),
                     pdpi::PartialPdTableEntryToPiTableEntry(p4info, entry));
  }
  return p4_runtime::InstallPiTableEntries(&p4rt_session, p4info, pi_entries);
}
absl::Status InstallPdTableEntries(const sai::TableEntries &entries,
                                   const p4::config::v1::P4Info &p4info,
                                   p4_runtime::P4RuntimeSession &p4rt_session) {
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
  ASSERT_OK_AND_ASSIGN(std::vector<InterfaceLink> up_links,
                       GetUpLinks(GetAllTrafficGeneratorLinks, *testbed));
  ASSERT_GE(up_links.size(), 2)
      << "Test requires at least 2 SUT ports connected to an Ixia";
  const std::string kIxiaSrcPort = up_links[0].peer_interface;
  const std::string kIxiaDstPort = up_links[1].peer_interface;
  const std::string kSutIngressPort = up_links[0].sut_interface;
  const std::string kSutEgressPort = up_links[1].sut_interface;
  const std::string kIxiaSrcLoc = up_links[0].peer_traffic_location;
  const std::string kIxiaDstLoc = up_links[1].peer_traffic_location;
  Openapi::StubInterface *traffic_client = testbed->GetTrafficClient();
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
      std::unique_ptr<p4_runtime::P4RuntimeSession> sut_p4rt,
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
  ASSERT_OK_AND_ASSIGN(
      const otg::Layer1::Speed::Enum kSutIngressPortSpeed,
      GetLayer1SpeedFromBitsPerSecond(kSutIngressPortSpeedInBitsPerSecond));

  // Calculate the duration to send the traffic along with the duration to wait.
  const int64_t kTestTrafficInBits =
      kTestFrameCount * kTestFrameSizeInBytes * 8;
  const double kLineRate =
      kPercentageLineRate / 100.0 * kSutIngressPortSpeedInBitsPerSecond;
  const absl::Duration kTrafficDuration =
      absl::Seconds(kTestTrafficInBits / kLineRate);
  const absl::Duration kWaitDuration = kTrafficDuration + absl::Seconds(120);

  // Run the test for IPv4 and then IPv6.
  for (bool is_ipv4 : {true, false}) {
    SCOPED_TRACE(absl::StrCat("IP version: ", is_ipv4 ? "IPv4" : "IPv6"));

    // Log counters for all queues on the egress port before starting.
    if (GetParam().log_counters) {
      for (const std::string queue :
           {"BE1", "AF1", "AF2", "AF3", "LLQ1", "LLQ2", "AF4", "NC1"}) {
        ASSERT_OK_AND_ASSIGN(
            QueueCounters counters,
            GetGnmiQueueCounters(kSutEgressPort, queue, *gnmi_stub));
        LOG(INFO) << "Initial Counters for " << queue << ": " << counters;
      }
    }

    //  Configure & start test packet flow.
    otg::SetConfigRequest set_config_req;
    otg::SetConfigResponse set_config_res;
    grpc::ClientContext set_config_ctx;
    otg::Config *config = set_config_req.mutable_config();
    const std::string kTrafficName =
        absl::StrCat((is_ipv4 ? "IPv4" : "IPv6"), " traffic at line rate");
    SCOPED_TRACE(kTrafficName);

    // Add traffic ports
    otg::Port *src_port = config->add_ports();
    otg::Port *dst_port = config->add_ports();
    src_port->set_name(kIxiaSrcPort);
    dst_port->set_name(kIxiaDstPort);
    src_port->set_location(kIxiaSrcLoc);
    dst_port->set_location(kIxiaDstLoc);

    // Add ports to layer1
    otg::Layer1 *layer1 = config->add_layer1();
    layer1->set_name("ly");
    layer1->add_port_names(kIxiaSrcPort);
    layer1->add_port_names(kIxiaDstPort);
    layer1->set_speed(kSutIngressPortSpeed);

    // Create a flow
    otg::Flow *flow = config->add_flows();
    flow->set_name(kTrafficName);

    // Set flow parameters
    flow->mutable_tx_rx()->set_choice(otg::FlowTxRx::Choice::port);
    flow->mutable_tx_rx()->mutable_port()->set_tx_name(kIxiaSrcPort);
    flow->mutable_tx_rx()->mutable_port()->set_rx_name(kIxiaDstPort);

    flow->mutable_size()->set_choice(otg::FlowSize::Choice::fixed);
    flow->mutable_size()->set_fixed(kTestFrameSizeInBytes);

    flow->mutable_rate()->set_choice(otg::FlowRate::Choice::percentage);
    flow->mutable_rate()->set_percentage(kPercentageLineRate);

    flow->mutable_duration()->set_choice(
        otg::FlowDuration::Choice::fixed_seconds);
    flow->mutable_duration()->mutable_fixed_seconds()->set_seconds(
        absl::ToDoubleSeconds(kTrafficDuration));

    // Craft packet (order of FlowHeaders determine order of packet headers on
    // wire).
    otg::FlowHeader *eth_packet = flow->add_packet();
    eth_packet->set_choice(otg::FlowHeader::Choice::ethernet);
    eth_packet->mutable_ethernet()->mutable_src()->set_choice(
        otg::PatternFlowEthernetSrc::Choice::value);
    eth_packet->mutable_ethernet()->mutable_dst()->set_choice(
        otg::PatternFlowEthernetDst::Choice::value);
    eth_packet->mutable_ethernet()->mutable_src()->set_value(
        netaddr::MacAddress(2, 2, 2, 2, 2, 2).ToString());
    eth_packet->mutable_ethernet()->mutable_dst()->set_value(
        netaddr::MacAddress(0, 1, 2, 3, 4, 5).ToString());

    if (is_ipv4) {
      otg::FlowHeader *ipv4 = flow->add_packet();
      ipv4->set_choice(otg::FlowHeader::Choice::ipv4);
      ipv4->mutable_ipv4()->mutable_src()->set_choice(
          otg::PatternFlowIpv4Src::Choice::value);
      ipv4->mutable_ipv4()->mutable_dst()->set_choice(
          otg::PatternFlowIpv4Dst::Choice::value);
      ipv4->mutable_ipv4()->mutable_src()->set_value(
          netaddr::Ipv4Address(192, 168, 2, 1).ToString());
      ipv4->mutable_ipv4()->mutable_dst()->set_value(
          netaddr::Ipv4Address(172, 0, 0, 1).ToString());
    } else {
      otg::FlowHeader *ipv6 = flow->add_packet();
      ipv6->set_choice(otg::FlowHeader::Choice::ipv6);
      ipv6->mutable_ipv6()->mutable_src()->set_choice(
          otg::PatternFlowIpv6Src::Choice::value);
      ipv6->mutable_ipv6()->mutable_dst()->set_choice(
          otg::PatternFlowIpv6Dst::Choice::value);
      ipv6->mutable_ipv6()->mutable_src()->set_value(
          netaddr::Ipv6Address(0x1000, 0, 0, 0, 0, 0, 0, 1).ToString());
      ipv6->mutable_ipv6()->mutable_dst()->set_value(
          netaddr::Ipv6Address(0x2000, 0, 0, 0, 0, 0, 0, 1).ToString());
    }

    // Set capture metrics
    flow->mutable_metrics()->set_enable(true);
    flow->mutable_metrics()->set_loss(false);
    flow->mutable_metrics()->set_timestamps(true);
    flow->mutable_metrics()->mutable_latency()->set_enable(true);
    flow->mutable_metrics()->mutable_latency()->set_mode(
        otg::FlowLatencyMetrics::Mode::cut_through);

    ASSERT_OK(traffic_client->SetConfig(&set_config_ctx, set_config_req,
                                        &set_config_res));

    LOG(INFO) << "Starting " << kTrafficName;
    otg::SetControlStateRequest set_state_req;
    otg::SetControlStateResponse set_state_res;
    grpc::ClientContext set_state_ctx;

    set_state_req.mutable_control_state()->set_choice(
        otg::ControlState::Choice::traffic);
    set_state_req.mutable_control_state()->mutable_traffic()->set_choice(
        otg::StateTraffic::Choice::flow_transmit);
    set_state_req.mutable_control_state()
        ->mutable_traffic()
        ->mutable_flow_transmit()
        ->set_state(otg::StateTrafficFlowTransmit::State::start);
    ASSERT_OK(traffic_client->SetControlState(&set_state_ctx, set_state_req,
                                              &set_state_res));

    LOG(INFO) << "Traffic started, waiting for " << kWaitDuration
              << " to complete";
    absl::SleepFor(kWaitDuration);

    // Get traffic flow metrics.
    otg::GetMetricsRequest get_metrics_req;
    otg::GetMetricsResponse get_metrics_res;
    grpc::ClientContext get_metrics_ctx;
    get_metrics_req.mutable_metrics_request()->set_choice(
        otg::MetricsRequest::Choice::flow);
    get_metrics_req.mutable_metrics_request()->mutable_flow()->add_flow_names(
        kTrafficName);
    ASSERT_OK(traffic_client->GetMetrics(&get_metrics_ctx, get_metrics_req,
                                         &get_metrics_res));

    // Log counters for all queues on the egress port after.
    if (GetParam().log_counters) {
      for (const std::string queue :
           {"BE1", "AF1", "AF2", "AF3", "LLQ1", "LLQ2", "AF4", "NC1"}) {
        ASSERT_OK_AND_ASSIGN(
            QueueCounters counters,
            GetGnmiQueueCounters(kSutEgressPort, queue, *gnmi_stub));
        LOG(INFO) << "Counters for " << queue << ": " << counters;
      }
    }

    ASSERT_EQ(get_metrics_res.metrics_response().flow_metrics_size(), 1);

    const otg::FlowMetric &traffic_stats =
        get_metrics_res.metrics_response().flow_metrics(0);

    EXPECT_EQ(traffic_stats.frames_tx(), traffic_stats.frames_rx())
        << "Tx and Rx frames are not the same. Packets lost: "
        << traffic_stats.frames_tx() - traffic_stats.frames_rx();

    // Check switch is ready at the end of the test.
    ASSERT_OK(SwitchReady(testbed->Sut()))
        << "Switch ready checks failed after traffic test";
  }
}
}  // namespace pins_test
