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
#include <functional>
#include <memory>
#include <optional>
#include <set>
#include <sstream>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

#include "absl/algorithm/container.h"
#include "absl/base/thread_annotations.h"
#include "absl/cleanup/cleanup.h"
#include "absl/container/btree_set.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/synchronization/mutex.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/optional.h"
#include "absl/types/span.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/ixia_helper.h"
#include "lib/ixia_helper.pb.h"
#include "lib/utils/json_utils.h"
#include "lib/validator/validator_lib.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/internal/ordered_map.h"
#include "p4_infra/netaddr/ipv4_address.h"
#include "p4_infra/netaddr/ipv6_address.h"
#include "p4_infra/netaddr/mac_address.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4_infra/p4_pdpi/p4_runtime_session_extras.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_infra/p4_pdpi/pd.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"
#include "tests/forwarding/util.h"
#include "tests/integration/system/nsf/interfaces/testbed.h"
#include "tests/integration/system/nsf/util.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "tests/qos/packet_in_receiver.h"
#include "tests/qos/qos_test_util.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/switch.h"

namespace pins_test {

using ::gutil::IsOkAndHolds;
using ::json_yang::FormatJsonBestEffort;
using ::testing::Contains;
using ::testing::Eq;
using ::testing::Field;
using ::testing::Ge;
using ::testing::Gt;
using ::testing::IsEmpty;
using ::testing::Le;
using ::testing::Not;
using ::testing::Pair;
using ::testing::ResultOf;

template <class T>
std::string ToString(const T &t) {
  std::stringstream ss;
  ss << t;
  return ss.str();
}

const sai::NexthopRewriteOptions kNextHopRewriteOptions = {
    .src_mac_rewrite = netaddr::MacAddress(0x66, 0x55, 0x44, 0x33, 0x22, 0x11),
    .dst_mac_rewrite = netaddr::MacAddress(2, 2, 2, 2, 2, 2),
};

// Type of an object that performs some cleanup logic in its destructor.
using Cleanup = decltype(absl::Cleanup{std::function<void()>()});

// Modifies the buffer config of the given `egress_port` such that all ports
// fairly share all space dynamically, and return a `Cleanup` object that
// restores the previous config when the object is destructed.
absl::StatusOr<Cleanup> ConfigureFairBufferConfigForPortUntilEndOfScope(
    absl::string_view egress_port, gnmi::gNMI::StubInterface &gnmi) {
  ASSIGN_OR_RETURN(const std::string kBufferProfileName,
                   GetBufferAllocationProfileByEgressPort(egress_port, gnmi));

  // Before we update the buffer config, save the current config and
  // prepare to restore it.
  ASSIGN_OR_RETURN(const std::string kInitialBufferConfig,
                   GetBufferAllocationProfileConfig(kBufferProfileName, gnmi));
  Cleanup cleanup = absl::Cleanup(std::function([=, &gnmi] {
    EXPECT_OK(UpdateBufferAllocationProfileConfig(kBufferProfileName,
                                                  kInitialBufferConfig, gnmi))
        << "failed to restore initial buffer config -- switch config may be "
           "corrupted, causing subsequent tests to fail";
  }));

  // Set fair buffer config.
  absl::flat_hash_map<std::string, BufferParameters>
      buffer_config_by_queue_name;
  ASSIGN_OR_RETURN(std::vector<std::string> queues,
                   GetQueuesByEgressPort(egress_port, gnmi));
  for (absl::string_view queue_name : queues) {
    buffer_config_by_queue_name[queue_name] = BufferParameters{
        .dedicated_buffer = 0,
        .use_shared_buffer = true,
        .shared_buffer_limit_type =
            "openconfig-qos:DYNAMIC_BASED_ON_SCALING_FACTOR",
        .dynamic_limit_scaling_factor = -3,
        .shared_static_limit = 0,
    };
  }
  RETURN_IF_ERROR(SetBufferConfigParameters(kBufferProfileName,
                                            buffer_config_by_queue_name, gnmi));

  return std::move(cleanup);
}

// Returns a set of table entries that will cause a switch to forward all L3
// multicast packets destined to provided mcast IP addresses out of the given
// port.
absl::StatusOr<std::vector<p4::v1::Entity>>
ConstructEntriesToForwardMcastTrafficToGivenPort(
    const pdpi::IrP4Info ir_p4info, std::string p4rt_port_id,
    netaddr::Ipv6Address ipv6_mcast_address[],
    netaddr::Ipv4Address ipv4_mcast_address[], int num_mcast_addresses) {
  constexpr absl::string_view kVrf = "vrf";
  constexpr int kMulticastGroupId = 42;
  ASSIGN_OR_RETURN(
      std::vector<p4::v1::Entity> pi_entities,
      sai::EntryBuilder()
          .AddVrfEntry(kVrf)
          .AddEntryAdmittingAllPacketsToL3()
	  .AddPreIngressAclTableEntry(kVrf)
          .AddMulticastGroupEntry(
              kMulticastGroupId,
              {
                  sai::Replica{.egress_port = p4rt_port_id, .instance = 0},
              })
	  .AddMrifEntryRewritingSrcMac(p4rt_port_id, /*instance=*/0,
                                       netaddr::MacAddress(1, 0, 0, 0, 0, 0))
          .LogPdEntries()
          .GetDedupedPiEntities(ir_p4info));
  std::vector<p4::v1::Entity> pi_route_entities;
  for (int i = 0; i < num_mcast_addresses; i++) {
    ASSIGN_OR_RETURN(
        pi_route_entities,
        sai::EntryBuilder()
            .AddMulticastRoute(kVrf, ipv6_mcast_address[i], kMulticastGroupId)
            .LogPdEntries()
            .GetDedupedPiEntities(ir_p4info));
    pi_entities.insert(pi_entities.end(), pi_route_entities.begin(),
                       pi_route_entities.end());
    ASSIGN_OR_RETURN(
        pi_route_entities,
        sai::EntryBuilder()
            .AddMulticastRoute(kVrf, ipv4_mcast_address[i], kMulticastGroupId)
            .LogPdEntries()
            .GetDedupedPiEntities(ir_p4info));
    pi_entities.insert(pi_entities.end(), pi_route_entities.begin(),
                       pi_route_entities.end());
  }

  return pi_entities;
}

// Returns a set of table entries that will cause a switch to forward all L3
// packets arriving at one of the two given ingress ports out of the given
// loopback port and also program a flow to punt ECN marked packets which are
// looped back to the CPU. Specific Requirements:
// - L3 admit entries to match on in ports as we do not want to reforward looped
// back packets
// - Punt all ECN marked packets which are looped back from egress port on highe
//   priority queue.
absl::StatusOr<sai::TableEntries>
ConstructEntriesToForwardAllTrafficToLoopbackPortAndCopyEcnPacketsToCPU(
    const pdpi::IrP4Info ir_p4info, absl::string_view p4rt_out_port_id,
    absl::string_view p4rt_in_port1_id, absl::string_view p4rt_in_port2_id,
    absl::string_view default_cpu_queue,
    absl::string_view high_priority_cpu_queue) {
  // By convention, we use link local IPv6 addresses as neighbor IDs.
  const std::string kNeighborId =
      netaddr::MacAddress(2, 2, 2, 2, 2, 2).ToLinkLocalIpv6Address().ToString();
  // L3 admit packets coming in only on the ingress ports. We do not want to
  // reforward looped back packets.
  std::string proto_base_table_entries = absl::Substitute(
      R"pb(
        entries {
          l3_admit_table_entry {
            match { in_port { value: "$2" } }
            action { admit_to_l3 {} }
            priority: 1
          }
        }
        entries {
          l3_admit_table_entry {
            match { in_port { value: "$3" } }
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
              unicast_set_port_and_src_mac {
                port: "$1"
                src_mac: "66:55:44:33:22:11"
              }
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
      kNeighborId, p4rt_out_port_id, p4rt_in_port1_id, p4rt_in_port2_id);

  // Punt ECN packets ingressing after packets are looped back.
  if (ir_p4info.tables_by_name().contains("acl_pre_ingress_metadata_table")) {
    // 1. Mark ECN packets in acl_pre_ingress_metadata_table.
    // 2. Punt all looped back packets (including non ECN marked packets) to CPU
    // in acl_ingress_table.
    // 3. Set ECN marked to higher priority CPU queue in acl_ingress_qos_table.
    return gutil::ParseTextProto<sai::TableEntries>(absl::StrCat(
        proto_base_table_entries,
        absl::Substitute(
            R"pb(
              entries {
                acl_pre_ingress_metadata_table_entry {
                  match {
                    is_ip { value: "0x1" }
                    ecn { value: "0x3" mask: "0x3" }
                  }
                  action { set_acl_metadata { acl_metadata: "0x06" } }
                  priority: 100
                }
              }
              entries {
                acl_ingress_table_entry {
                  match {
                    dst_mac {
                      value: "02:02:02:02:02:02"
                      mask: "ff:ff:ff:ff:ff:ff"
                    }
                    is_ip { value: "0x1" }
                  }
                  action { acl_copy { qos_queue: "$0" } }
                  priority: 1
                }
              }
              entries {
                acl_ingress_qos_table_entry {
                  match { acl_metadata { value: "0x06" mask: "0xff" } }
                  action {
                    set_qos_queue_and_cancel_copy_above_rate_limit {
                      qos_queue: "$1"
                    }
                  }
                  priority: 4400
                  meter_config { bytes_per_second: 5000 burst_bytes: 5000 }
                }
              }
            )pb",
            default_cpu_queue, high_priority_cpu_queue)));
  } else {
    // 1. Punt all ECN Marked packets in acl_ingress_table.
    return gutil::ParseTextProto<sai::TableEntries>(
        absl::StrCat(proto_base_table_entries +
                     absl::Substitute(
                         R"pb(
                           entries {
                             acl_ingress_table_entry {
                               match {
                                 dst_mac {
                                   value: "02:02:02:02:02:02"
                                   mask: "ff:ff:ff:ff:ff:ff"
                                 }
                                 is_ip { value: "0x1" }
                                 ecn { value: "0x3" mask: "0x3" }
                               }
                               action { acl_copy { qos_queue: "$0" } }
                               priority: 1
                             }
                           }
                         )pb",
                         default_cpu_queue)));
  }
}

// Structure represents SUTs connections to Ixia.
// The QoS tests expects 2 Ixia `ingress_links` connected to Ixia to which
// traffic will be injected in order to oversubscribe the single `egress_link`.
struct IxiaLinks {
  ixia::IxiaLink ingress_links[2];
  ixia::IxiaLink egress_link;
};

// Function returns Ixia connections to use for ingress and egress traffic
// If the device ports are specified as part of test parameters passed in,
// the function will use those ports to fetch Ixia link information,
// else we will try and find 2 Ixia links for ingress and 1 for egress such
// that ingress ports have speed at least that of egress port.
absl::StatusOr<IxiaLinks> GetIxiaLinks(
    thinkit::GenericTestbed &testbed, gnmi::gNMI::StubInterface &gnmi_stub,
    const pins_test::QosTestParams &qos_params) {
  IxiaLinks links;

  if (qos_params.ingress_ports[0].empty() ||
      qos_params.ingress_ports[1].empty() ||
      qos_params.egress_port_under_test.empty()) {
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
  } else {
    ASSIGN_OR_RETURN(
        links.ingress_links[0],
        ixia::GetIxiaLink(testbed, gnmi_stub, qos_params.ingress_ports[0]));
    ASSIGN_OR_RETURN(
        links.ingress_links[1],
        ixia::GetIxiaLink(testbed, gnmi_stub, qos_params.ingress_ports[1]));
    ASSIGN_OR_RETURN(links.egress_link,
                     ixia::GetIxiaLink(testbed, gnmi_stub,
                                       qos_params.egress_port_under_test));
  }
  return links;
}

// Like the function above but overloaded for BufferTestParams
absl::StatusOr<IxiaLinks> GetIxiaLinks(
    thinkit::GenericTestbed &testbed, gnmi::gNMI::StubInterface &gnmi_stub,
    const pins_test::BufferTestParams &qos_params) {
  IxiaLinks links;

  if (qos_params.default_params.ingress_ports[0].empty() ||
      qos_params.default_params.ingress_ports[1].empty() ||
      qos_params.default_params.egress_port_under_test.empty()) {
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
  } else {
    ASSIGN_OR_RETURN(
        links.ingress_links[0],
        ixia::GetIxiaLink(testbed, gnmi_stub,
                          qos_params.default_params.ingress_ports[0]));
    ASSIGN_OR_RETURN(
        links.ingress_links[1],
        ixia::GetIxiaLink(testbed, gnmi_stub,
                          qos_params.default_params.ingress_ports[1]));
    ASSIGN_OR_RETURN(
        links.egress_link,
        ixia::GetIxiaLink(testbed, gnmi_stub,
                          qos_params.default_params.egress_port_under_test));
  }
  return links;
}

// Returns a function that logs port debug information for both switches in a
// mirror testbed if the ports are down.
std::function<void()> MakeLogPortDebugInfoFunction(
    thinkit::GenericTestbed &testbed,
    absl::Span<const std::string> enabled_interfaces) {
  return [&testbed, enabled_interfaces] {
    if (absl::Status sut_port_status =
            pins_test::PortsUp(testbed.Sut(), enabled_interfaces);
        !sut_port_status.ok()) {
      LOG(WARNING) << sut_port_status;
    }
  };
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
  // Pick a testbed with SUT connected to an Ixia on 2 ports, one ingress and
  // one egress port.
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
  // Get Ixia connected links.
  ASSERT_OK_AND_ASSIGN(IxiaLinks links,
                       GetIxiaLinks(*testbed, *gnmi_stub, GetParam()));

  const std::string &kSutIngressPort = links.ingress_links[0].sut_interface;
  const std::string &kSutEgressPort = links.egress_link.sut_interface;

  const std::string &kIxiaSrcPort = links.ingress_links[0].ixia_interface;
  const std::string &kIxiaDstPort = links.egress_link.ixia_interface;

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

  // Configure the switch to send all incoming packets out of the chosen egress
  // port.
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt,
      ConfigureSwitchAndReturnP4RuntimeSession(
          testbed->Sut(), /*gnmi_config=*/std::nullopt, GetParam().p4info));
  netaddr::Ipv6Address kIpv6McastAddresses[64];
  netaddr::Ipv4Address kIpv4McastAddresses[64];
  for (int dscp = 0; dscp < 64; ++dscp) {
    kIpv6McastAddresses[dscp] =
        netaddr::Ipv6Address(0xff00, 0, 0, 0, 0, 0, 0, dscp + 1);
    kIpv4McastAddresses[dscp] = netaddr::Ipv4Address(224, 0, 0, dscp + 1);
  }
  ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(GetParam().p4info));
  if (GetParam().multicast_queue_by_dscp.has_value()) {
    ASSERT_OK_AND_ASSIGN(
        auto entries, ConstructEntriesToForwardMcastTrafficToGivenPort(
                          ir_p4info, kSutEgressPortP4rtId, kIpv6McastAddresses,
                          kIpv4McastAddresses, 64));
    ASSERT_OK(pdpi::InstallPiEntities(sut_p4rt.get(), ir_p4info, entries));
  }
  if (GetParam().queue_by_dscp.has_value()) {
    ASSERT_OK_AND_ASSIGN(std::vector<p4::v1::Entity> entities,
                         sai::EntryBuilder()
                             .AddEntriesForwardingIpPacketsToGivenPort(
                                 /*egress_port=*/kSutEgressPortP4rtId,
                                 /*ip_version=*/sai::IpVersion::kIpv4And6,
                                 /*rewrite_options*/ kNextHopRewriteOptions)
                             .LogPdEntries()
                             .GetDedupedPiEntities(ir_p4info));
    ASSERT_OK(pdpi::InstallPiEntities(sut_p4rt.get(), ir_p4info, entities));
  }

  // Fix test parameters and PIRs (peak information rates, in bytes
  // per second) for each DSCP.
  constexpr int64_t kTestFrameSizeInBytes = 1000;                // 1 KB
  constexpr int64_t kTestFrameCount = 30'000'000;                // 30 GB
  constexpr int64_t kTestFramesPerSecond = kTestFrameCount / 3;  // for 3 s
  constexpr int64_t kTestFrameSpeedInBytesPerSecond =            // 10 GB/s
      kTestFramesPerSecond * kTestFrameSizeInBytes;

  // Get strictly prioritized queues.
  ASSERT_OK_AND_ASSIGN(
      const absl::flat_hash_set<std::string> kStrictlyPrioritizedQueues,
      GetStrictlyPrioritizedQueuesMap(kSutEgressPortScheduler, *gnmi_stub));
  // We use exponentially spaced PIRs, with a base rate that's high enough for
  // buffers to drain quickly. That way we don't have to drain buffers manually
  // between test traffic flows.
  constexpr int64_t kPirBaseSpeedInBytesPerSecond = 20'000'000;  // 20 MB/s.
  absl::flat_hash_map<std::string, int64_t> kPirByQueueName;
  using DscpsByQueueName =
      std::optional<absl::flat_hash_map<std::string, std::vector<int>>>;
  DscpsByQueueName kDscpsByUnicastQueueName;
  DscpsByQueueName kDscpsByMulticastQueueName;

  // Before we update the scheduler config, save the current config and
  // prepare to restore it at the end of the test.
  ASSERT_OK_AND_ASSIGN(
      const std::string kInitialSchedulerConfig,
      GetSchedulerPolicyConfig(kSutEgressPortScheduler, *gnmi_stub));
  const auto kRestoreSchedulerConfig = absl::Cleanup([&] {
    EXPECT_OK(UpdateSchedulerPolicyConfig(kSutEgressPortScheduler,
                                          kInitialSchedulerConfig, *gnmi_stub))
        << "failed to restore initial scheduler config -- switch config may "
           "be "
           "corrupted, causing subsequent test to fail";
  });
  if (GetParam().queue_by_dscp.has_value()) {
    ASSERT_OK_AND_ASSIGN(kDscpsByUnicastQueueName,
                         GetQueueToDscpsMapping(*GetParam().queue_by_dscp));
  }
  if (GetParam().multicast_queue_by_dscp.has_value()) {
    ASSERT_OK_AND_ASSIGN(
        kDscpsByMulticastQueueName,
        GetQueueToDscpsMapping(*GetParam().multicast_queue_by_dscp));
  }

  std::vector<TestOperations> test_operations;

  test_operations.push_back(TestOperations::TrafficTest);

  for (const DscpsByQueueName kDscpsByQueueName :
       {kDscpsByUnicastQueueName, kDscpsByMulticastQueueName}) {
    if (!kDscpsByQueueName.has_value()) {
      continue;
    }

    bool testing_multicast = (kDscpsByQueueName == kDscpsByMulticastQueueName);

    int pirFactor = 1;
    for (const auto &queue : *kDscpsByQueueName) {
      // Skip queues that are strictly prioritized, as these do not support
      // reconfiguration today.
      if (!testing_multicast &&
          kStrictlyPrioritizedQueues.contains(queue.first)) {
        continue;
      }
      kPirByQueueName.insert(
          {queue.first, kPirBaseSpeedInBytesPerSecond * pirFactor});
      pirFactor *= 2;
    }

    // Ensure the test parameters are compatible with the testbed.
    ASSERT_OK_AND_ASSIGN(
        const int64_t kSutIngressPortSpeedInBitsPerSecond,
        GetPortSpeedInBitsPerSecond(kSutIngressPort, *gnmi_stub));
    ASSERT_OK_AND_ASSIGN(
        const int64_t kSutEgressPortSpeedInBitsPerSecond,
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

    // Update scheduler config.
    {
      absl::flat_hash_map<std::string, SchedulerParameters> params;
      for (auto &[queue, pir] : kPirByQueueName) {
        params[queue].peak_information_rate = pir;
        // To avoid a large initial burst of forwarded packets when we start the
        // test packet flow, we use a minimally-sized token buffer. This is to
        // ensure that the observed information rate will closely matche the
        // peak information rate. See RFC 2698 for details.
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

    constexpr int64_t kSpeed100g = 100000000000;
    constexpr int64_t kSpeed200g = 200000000000;

    if (kSutEgressPortSpeedInBitsPerSecond != kSpeed200g) {
      auto status = SetPortSpeedInBitsPerSecond(PortSpeed(kSpeed200g),
                                                kSutEgressPort, *gnmi_stub);
      if (!status.ok()) {
        LOG(WARNING) << "Failed to toggle port speed for : " << kSutEgressPort;
      }
      ASSERT_OK(SetPortSpeedInBitsPerSecond(
          PortSpeed(kSutEgressPortSpeedInBitsPerSecond), kSutEgressPort,
          *gnmi_stub));
    } else {
      auto status = SetPortSpeedInBitsPerSecond(PortSpeed(kSpeed100g),
                                                kSutEgressPort, *gnmi_stub);
      if (!status.ok()) {
        LOG(WARNING) << "Failed to toggle port speed for : " << kSutEgressPort;
      }
      ASSERT_OK(SetPortSpeedInBitsPerSecond(
          PortSpeed(kSutEgressPortSpeedInBitsPerSecond), kSutEgressPort,
          *gnmi_stub));
    }
    // Wait for any counters to reset on port speed change.
    absl::SleepFor(absl::Seconds(15));

    std::vector<std::string> required_interfaces = {kSutEgressPort};
    // Wait for all enabled interfaces to be up before sending packets.
    ASSERT_OK(pins_test::OnFailure(
        pins_test::WaitForCondition(pins_test::PortsUp, absl::Minutes(10),
                                    testbed->Sut(), required_interfaces,
                                    /*with_healthz=*/false),
        MakeLogPortDebugInfoFunction(*testbed, required_interfaces)))
        << "all required ports must be initialized on the SUT before sending "
           "test packets";
  }

  // Connect to Ixia and fix global parameters.
  ASSERT_OK_AND_ASSIGN(const std::string kIxiaHandle,
                       ixia::ConnectToIxia(*testbed));
  ASSERT_OK_AND_ASSIGN(const std::string kIxiaSrcPortHandle,
                       ixia::IxiaVport(kIxiaHandle, kIxiaSrcPort, *testbed));
  ASSERT_OK_AND_ASSIGN(const std::string kIxiaDstPortHandle,
                       ixia::IxiaVport(kIxiaHandle, kIxiaDstPort, *testbed));

  if (GetParam().nsf_reboot) {
    ASSERT_OK(NsfReboot(testbed.get()));
    test_operations.push_back(TestOperations::NsfRebootAndTrafficTest);
  }

  // Send traffic twice, once during NSF reboot and once post the reboot
  // to ensure the forwarding traffic is not disrupted.
  for (auto test_operation : test_operations) {
    if (test_operation == TestOperations::NsfRebootAndTrafficTest &&
        GetParam().ssh_client_for_nsf) {
      ASSERT_OK(
          WaitForNsfReboot(testbed.get(), *GetParam().ssh_client_for_nsf));
      LOG(INFO) << "NSF reboot complete, sending traffic again to ensure "
                   "the forwarding traffic is not disrupted.";
    }
    for (const DscpsByQueueName kDscpsByQueueName :
         {kDscpsByUnicastQueueName, kDscpsByMulticastQueueName}) {
      if (!kDscpsByQueueName.has_value()) {
        continue;
      }
      std::set<std::string> tested_queues;

      bool testing_multicast =
          (kDscpsByQueueName == kDscpsByMulticastQueueName);

      QueueCounters kInitialQueueCounters;
      Counters kInitialPortCounters;
      // Actual testing -- inject test IPv4 and IPv6 packets for each DSCP,
      // and check the behavior is as eexpted.
      constexpr int kMaxDscp = 63;
      for (int dscp = 0; dscp <= kMaxDscp; ++dscp) {
        SCOPED_TRACE(absl::StrCat("DSCP = ", dscp));
        for (bool is_ipv4 : {true, false}) {
          SCOPED_TRACE(absl::StrCat("IP version: ", is_ipv4 ? "IPv4" : "IPv6"));
          SCOPED_TRACE(absl::StrCat("testing_multicast: ", testing_multicast));
          bool not_after_nsf_reboot =
              !GetParam().nsf_reboot ||
              test_operation == TestOperations::NsfRebootAndTrafficTest;

          // Figure out which queue we will be targeting and some queue
          // parameters.
          ASSERT_OK_AND_ASSIGN(
              const std::string kTargetQueue,
              GetQueueNameByDscpAndPort(
                  dscp, kSutEgressPort, *gnmi_stub,
                  testing_multicast ? *GetParam().multicast_queue_by_dscp
                                    : *GetParam().queue_by_dscp));
          if (!testing_multicast &&
              kStrictlyPrioritizedQueues.contains(kTargetQueue)) {
            LOG(WARNING) << "skipping test for strict queue '" << kTargetQueue
                         << "'";
            continue;
          }

          // In order to optimize test run time for NSF scenario,
          // skip queues that have already been tested with a dscp value.
          if (GetParam().nsf_reboot &&
              tested_queues.find(kTargetQueue) != tested_queues.end()) {
            continue;
          }
          tested_queues.insert(kTargetQueue);
          ASSERT_OK_AND_ASSIGN(
              const int64_t kTargetQueuePir,
              gutil::FindOrStatus(kPirByQueueName, kTargetQueue));

          if (not_after_nsf_reboot) {
            // Get initial queue counters after NSF Reboot is complete since
            // gnmi calls cannot be made during NSF reboot.
            ASSERT_OK_AND_ASSIGN(
                kInitialQueueCounters,
                GetGnmiQueueCounters(kSutEgressPort, kTargetQueue, *gnmi_stub));
            ASSERT_OK_AND_ASSIGN(
                kInitialPortCounters,
                GetCountersForInterface(kSutEgressPort, *gnmi_stub));
          }
          // Configure & start test packet flow.
          const std::string kTrafficName =
              absl::StrCat((is_ipv4 ? "IPv4" : "IPv6"), " traffic for DSCP ",
                           dscp, ", targeting queue ", kTargetQueue,
                           " with PIR = ", kTargetQueuePir, " bytes/second");
          SCOPED_TRACE(kTrafficName);

          ASSERT_OK_AND_ASSIGN(
              const std::string kIxiaTrafficHandle,
              ixia::SetUpTrafficItem(kIxiaSrcPortHandle, kIxiaDstPortHandle,
                                     kTrafficName, *testbed));
          auto delete_traffic_item = absl::Cleanup([&, kIxiaTrafficHandle] {
            ASSERT_OK(ixia::DeleteTrafficItem(kIxiaTrafficHandle, *testbed));
          });
          auto traffix_parameters = ixia::TrafficParameters{
              .frame_count = kTestFrameCount,
              .frame_size_in_bytes = kTestFrameSizeInBytes,
              .traffic_speed = ixia::FramesPerSecond{kTestFramesPerSecond},
          };
          if (testing_multicast) {
            if (is_ipv4) {
              traffix_parameters.dst_mac =
                  netaddr::MacAddress(1, 0, 0x5e, 0, 0, dscp + 1);
              traffix_parameters.ip_parameters = ixia::Ipv4TrafficParameters{
                  .src_ipv4 = netaddr::Ipv4Address(192, 168, 2, dscp + 1),
                  .dst_ipv4 = kIpv4McastAddresses[dscp],
                  // Set ECN 0 to avoid RED drops.
                  .priority = ixia::IpPriority{.dscp = dscp, .ecn = 0},
              };
            } else {
              traffix_parameters.dst_mac =
                  netaddr::MacAddress(0x33, 0x33, 0, 0, 0, dscp + 1);
              traffix_parameters.ip_parameters = ixia::Ipv6TrafficParameters{
                  .src_ipv6 =
                      netaddr::Ipv6Address(0x1000, 0, 0, 0, 0, 0, 0, dscp + 1),
                  .dst_ipv6 = kIpv6McastAddresses[dscp],
                  // Set ECN 0 to avoid RED drops.
                  .priority = ixia::IpPriority{.dscp = dscp, .ecn = 0},
              };
            }
          } else {
            if (is_ipv4) {
              traffix_parameters.ip_parameters = ixia::Ipv4TrafficParameters{
                  .src_ipv4 = netaddr::Ipv4Address(192, 168, 2, dscp + 1),
                  .dst_ipv4 = netaddr::Ipv4Address(172, 0, 0, dscp + 1),
                  // Set ECN 0 to avoid RED drops.
                  .priority = ixia::IpPriority{.dscp = dscp, .ecn = 0},
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
          }
          LOG(INFO) << "-- starting " << kTrafficName;
          ASSERT_OK(ixia::SetTrafficParameters(kIxiaTrafficHandle,
                                               traffix_parameters, *testbed));

          // Occasionally the Ixia API cannot keep up and starting traffic
          // fails, so we try up to 3 times.
          ASSERT_OK(pins::TryUpToNTimes(3, /*delay=*/absl::Seconds(1), [&] {
            return ixia::StartTraffic(kIxiaTrafficHandle, kIxiaHandle,
                                      *testbed);
          }));
          const absl::Duration kTrafficDuration =
              absl::Seconds(kTestFrameCount / kTestFramesPerSecond);
          LOG(INFO) << "traffic started, waiting for " << kTrafficDuration
                    << " to complete";
          absl::SleepFor(kTrafficDuration);

          if (not_after_nsf_reboot) {
            // Check observed traffic rate against target queue PIR.
            ASSERT_OK_AND_ASSIGN(
                const ixia::TrafficItemStats kIxiaTrafficStats,
                ixia::GetTrafficItemStats(kIxiaHandle, kTrafficName, *testbed));
            const int64_t kObservedTrafficRate =
                ixia::BytesPerSecondReceived(kIxiaTrafficStats);
            LOG(INFO) << "observed traffic rate (bytes/second): "
                      << kObservedTrafficRate;
            const int64_t kAbsoluteError =
                kObservedTrafficRate - kTargetQueuePir;
            const double kRelativeErrorPercent =
                100. * kAbsoluteError / kTargetQueuePir;
            constexpr double kTolerancePercent = 10;  // +-10% tolerance.
            if (std::abs(kRelativeErrorPercent) <= kTolerancePercent) {
              LOG(INFO)
                  << "observed traffic rate matches expected traffic rate "
                     "(error: "
                  << kRelativeErrorPercent << "%)";
            } else {
              ADD_FAILURE()
                  << "observed traffic rate of " << kObservedTrafficRate
                  << " bytes/second is not within " << kTolerancePercent
                  << "% of the PIR of the queue '" << kTargetQueue
                  << "' targeted by traffic (PIR = " << kTargetQueuePir
                  << " bytes/second, error = " << kRelativeErrorPercent << "%)";
            }

            // Verify that the target egress queue counters incremented.
            const absl::Time kDeadline =
                absl::Now() + kMaxQueueCounterUpdateTime;
            LOG(INFO) << "polling queue counters (this may take up to "
                      << kMaxQueueCounterUpdateTime << ")";
            QueueCounters final_counters, delta_counters;
            do {
              ASSERT_OK_AND_ASSIGN(
                  final_counters,
                  GetGnmiQueueCounters(kSutEgressPort, kTargetQueue,
                                       *gnmi_stub));
              delta_counters = final_counters - kInitialQueueCounters;
            } while (TotalPacketsForQueue(delta_counters) <
                         kIxiaTrafficStats.num_tx_frames() &&
                     absl::Now() < kDeadline);
            ASSERT_OK_AND_ASSIGN(
                Counters final_port_counters,
                GetCountersForInterface(kSutEgressPort, *gnmi_stub));

            SCOPED_TRACE(
                absl::StrCat("port counters incremented by ",
                             kInitialPortCounters - final_port_counters));
            SCOPED_TRACE(
                absl::StrCat("Initial port counters: ", kInitialPortCounters));
            SCOPED_TRACE(
                absl::StrCat("Final port counters: ", final_port_counters));
            LOG(INFO) << "queue counters incremented by " << delta_counters;
            LOG(INFO) << "Queue Counters.\nBefore: "
                      << ToString(kInitialQueueCounters)
                      << "\nAfter :" << ToString(final_counters);

            SCOPED_TRACE(
                absl::StrCat("Counters for queue ", kTargetQueue,
                             " did not change as expected within ",
                             ToString(kMaxQueueCounterUpdateTime),
                             " after injecting/receiving back ",
                             kIxiaTrafficStats.num_tx_frames(), "/",
                             kIxiaTrafficStats.num_rx_frames(),
                             " test packets from/at the Ixia.\nBefore: ",
                             ToString(kInitialQueueCounters),
                             "\nAfter :", ToString(final_counters)));
            // Tolerance of 5% of packets for counter update delays, port drops,
            // etc.
            EXPECT_THAT(delta_counters,
                        ResultOf(TotalPacketsForQueue,
                                 Ge(kIxiaTrafficStats.num_tx_frames() * 0.95)));
            // Protocol packets such as LLDP/NDv6 can be transmitted via queue
            // during test. Add some tolerance to account for these packets.
            constexpr int kMaxToleratedExtraPackets = 5;
            EXPECT_THAT(delta_counters,
                        ResultOf(TotalPacketsForQueue,
                                 Le(kIxiaTrafficStats.num_tx_frames() +
                                    kMaxToleratedExtraPackets)));
            EXPECT_THAT(delta_counters,
                        Field(&QueueCounters::num_packets_transmitted,
                              Ge(kIxiaTrafficStats.num_rx_frames())));
            EXPECT_THAT(delta_counters,
                        Field(&QueueCounters::num_packets_transmitted,
                              Le(kIxiaTrafficStats.num_rx_frames() +
                                 kMaxToleratedExtraPackets)));
          }
        }
      }
    }
  }
  LOG(INFO) << "-- Test done -------------------------------------------------";
}

// The purpose of this test is to verify that weighted-round-robin-scheduled
// queues are scheduled proportionally to their weight. To test this, we inject
// two categories of traffic (all forwarded out of a single chosen egress port):
// - IPv{4,6} traffic for all round robin queues, in uniform amounts.
//   We expect each round robin queue to forward a portion of traffic that is
//   proportional to the queue's weight.
// - Auxilliary IPv4 traffic to a strictly prioritized queue, at 95% line rate.
//   This reduces the available bandwith for the round-robin-scheduled queues
//   to 5%, which ensures all round robin queues remain nonempty and the
//   scheduler is able to schedule packets based on weights assigned.
TEST_P(FrontpanelQosTest, WeightedRoundRobinWeightsAreRespected) {
  if (GetParam().multicast_queue_by_dscp.has_value()) {
    GTEST_SKIP() << "Multicast forwarding WIP";
  }
  LOG(INFO) << "-- Test started ----------------------------------------------";
  LOG(INFO) << "obtaining testbed handle";
  // Pick a testbed with SUT connected to an Ixia on 3 ports, so we can
  // oversubscribe a switch egress port.
  auto requirements = gutil::ParseProtoOrDie<thinkit::TestRequirements>(
      R"pb(
        interface_requirements { count: 3 interface_mode: TRAFFIC_GENERATOR }
      )pb");
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<thinkit::GenericTestbed> testbed,
      GetParam().testbed_interface->GetTestbedWithRequirements(requirements));


  thinkit::Switch &sut = testbed->Sut();
  // Pick 3 SUT ports connected to the Ixia, 2 for receiving test packets and
  // 1 for forwarding them back. We use the faster links for injecting packets
  // so we can oversubsribe the egress port. We inject the traffic for the
  // round-robin queues via one ingress port, and auxilliary traffic for a
  // strictly-prioritized queue via another ingress port.
  LOG(INFO) << "picking test packet links";
  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, sut.CreateGnmiStub());
  // Get Ixia connected links.
  ASSERT_OK_AND_ASSIGN(IxiaLinks links,
                       GetIxiaLinks(*testbed, *gnmi_stub, GetParam()));

  const std::string &kSutMainIngressPort = links.ingress_links[0].sut_interface;
  const std::string &kSutAuxiliayIngressPort =
      links.ingress_links[1].sut_interface;
  const std::string &kSutEgressPort = links.egress_link.sut_interface;
  const std::string &kIxiaMainSrcPort = links.ingress_links[0].ixia_interface;
  const std::string &kIxiaAuxiliarySrcPort =
      links.ingress_links[1].ixia_interface;
  const std::string &kIxiaDstPort = links.egress_link.ixia_interface;

  LOG(INFO) << absl::StrFormat(
      "Test packet routes:"
      "\n- Main traffic: "
      "[Ixia: %s] == %.1f Gbps => [SUT: %s] -> [SUT: %s] == %.1f Gbps => "
      "[Ixia: %s]"
      "\n- Background traffic: "
      "[Ixia: %s] == %.1f Gbps => [SUT: %s] -> [SUT: %s] == %.1f Gbps => "
      "[Ixia: %s]",
      kIxiaMainSrcPort,
      links.ingress_links[0].sut_interface_bits_per_second / 1'000'000'000.,
      kSutMainIngressPort, kSutEgressPort,
      links.egress_link.sut_interface_bits_per_second / 1'000'000'000.,
      kIxiaDstPort, kIxiaAuxiliarySrcPort,
      links.ingress_links[1].sut_interface_bits_per_second / 1'000'000'000.,
      kSutAuxiliayIngressPort, kSutEgressPort,
      links.egress_link.sut_interface_bits_per_second / 1'000'000'000.,
      kIxiaDstPort);
  ASSERT_OK_AND_ASSIGN(
      const std::string kSutEgressPortSchedulerPolicy,
      GetSchedulerPolicyNameByEgressPort(kSutEgressPort, *gnmi_stub));
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
  ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(GetParam().p4info));
  ASSERT_OK_AND_ASSIGN(std::vector<p4::v1::Entity> entities,
                       sai::EntryBuilder()
                           .AddEntriesForwardingIpPacketsToGivenPort(
                               /*egress_port=*/kSutEgressPortP4rtId,
                               /*ip_version=*/sai::IpVersion::kIpv4And6,
                               /*rewrite_options*/ kNextHopRewriteOptions)
                           .LogPdEntries()
                           .GetDedupedPiEntities(ir_p4info));
  ASSERT_OK(pdpi::InstallPiEntities(sut_p4rt.get(), ir_p4info, entities));

  // Figure out which DSCPs to use for each queue.
  using DscpsByQueueName = absl::flat_hash_map<std::string, std::vector<int>>;
  ASSERT_OK_AND_ASSIGN(const DscpsByQueueName kDscpsByQueueName,
                       GetQueueToDscpsMapping(*GetParam().queue_by_dscp));

  // Identify round-robin queues and their weights.
  using WeightByQueueName = absl::flat_hash_map<std::string, int64_t>;
  ASSERT_OK_AND_ASSIGN(WeightByQueueName weights_by_queue_name,
                       GetSchedulerPolicyWeightsByQueue(
                           kSutEgressPortSchedulerPolicy, *gnmi_stub));

  // Remove queues which are not present in the dscp map passed in.
  for (auto iterator = weights_by_queue_name.begin();
       iterator != weights_by_queue_name.end();) {
    auto iterator_copy = iterator++;
    if (!kDscpsByQueueName.contains(iterator_copy->first)) {
      weights_by_queue_name.erase(iterator_copy);
    }
  }
  if (weights_by_queue_name.size() < 2) {
    GTEST_SKIP() << "test pre-condition violated: expected at least 2 queues "
                    "with round-robin schedulers";
  }
  absl::btree_set<int> weights;
  for (auto &[_, weight] : weights_by_queue_name) weights.insert(weight);
  if (weights.size() < 2) {
    GTEST_SKIP() << "test pre-condition violated: expected at least 2 "
                    "different round-robin weights, but found only "
                 << weights.size() << ": " << absl::StrJoin(weights, ", ");
  }
  LOG(INFO)
      << "Testing the following queues and associated round-robin weights:\n- "
      << absl::StrJoin(weights_by_queue_name, "\n- ",
                       [](std::string *out, auto &queue_and_weight) {
                         absl::StrAppendFormat(out, "%s - weight %d",
                                               queue_and_weight.first,
                                               queue_and_weight.second);
                       });

  // Pick a queue/DSCP that is strictly prioritized over the round robin queues.
  ASSERT_OK_AND_ASSIGN(
      const std::vector<std::string> kStrictlyPrioritizedQueues,
      GetStrictlyPrioritizedQueuesInDescendingOrderOfPriority(
          kSutEgressPortSchedulerPolicy, *gnmi_stub));
  ASSERT_THAT(kStrictlyPrioritizedQueues, Not(IsEmpty()));

  std::optional<std::string> strictly_prioritized_queue;
  bool found_strictly_prioritized_queue = false;
  for (const std::string &strict_queue : kStrictlyPrioritizedQueues) {
    if (gutil::FindOrStatus(kDscpsByQueueName, strict_queue).ok()) {
      strictly_prioritized_queue = strict_queue;
      found_strictly_prioritized_queue = true;
      break;
    }
  }
  ASSERT_TRUE(found_strictly_prioritized_queue)
      << "Could not find a strictly prioritized queue with dscp mapping";
  ASSERT_OK_AND_ASSIGN(
      const std::vector<int> kStrictlyPrioritizedIpv4Dscps,
      gutil::FindOrStatus(kDscpsByQueueName, *strictly_prioritized_queue));
  ASSERT_THAT(kStrictlyPrioritizedIpv4Dscps, Not(IsEmpty()));
  const int kStrictlyPrioritizedIpv4Dscp = kStrictlyPrioritizedIpv4Dscps.at(0);

  // Before we update the scheduler config, save the current config and
  // prepare to restore it at the end of the test.
  ASSERT_OK_AND_ASSIGN(
      const std::string kInitialSchedulerConfig,
      GetSchedulerPolicyConfig(kSutEgressPortSchedulerPolicy, *gnmi_stub));
  const auto kRestoreSchedulerConfig = absl::Cleanup([&] {
    EXPECT_OK(UpdateSchedulerPolicyConfig(kSutEgressPortSchedulerPolicy,
                                          kInitialSchedulerConfig, *gnmi_stub))
        << "failed to restore initial scheduler config -- switch config may be "
           "corrupted, causing subsequent test to fail";
  });

  // Configure fair buffer profile (until the end of the test) so we can ignore
  // buffer carving effects.
  ASSERT_OK_AND_ASSIGN(Cleanup restore_buffer_config,
                       ConfigureFairBufferConfigForPortUntilEndOfScope(
                           kSutEgressPort, *gnmi_stub));

  // Set lower & upper bounds (CIRs/PIRs) such that:
  // - Round-robin-scheduled queues are not rate limited.
  // - Auxilliary traffic to strictly prioritized queue uses at most 95% of
  //   egress link capacity.
  LOG(INFO) << "configuring scheduler parameters";
  // Rates are in bytes/second.
  const int64_t kEgressLineRateInBytesPerSecond =
      links.egress_link.sut_interface_bits_per_second / 8;
  const int64_t kStrictlyPrioritizedPir = .95 * kEgressLineRateInBytesPerSecond;
  {
    absl::flat_hash_map<std::string, SchedulerParameters> params_by_queue_name;
    for (auto &[queue_name, _] : weights_by_queue_name) {
      params_by_queue_name[queue_name].committed_information_rate = 0;
      params_by_queue_name[queue_name].peak_information_rate =
          kEgressLineRateInBytesPerSecond;
    }
    params_by_queue_name[*strictly_prioritized_queue].peak_information_rate =
        kStrictlyPrioritizedPir;
    ASSERT_OK(SetSchedulerPolicyParameters(kSutEgressPortSchedulerPolicy,
                                           params_by_queue_name, *gnmi_stub));
    // Dump initial and modified configs, to ease debugging.
    ASSERT_OK(testbed->Environment().StoreTestArtifact(
        absl::StrCat(kSutEgressPortSchedulerPolicy, "_before_update.json"),
        FormatJsonBestEffort(kInitialSchedulerConfig)));
    ASSERT_OK_AND_ASSIGN(
        std::string updated_scheduler_config,
        GetSchedulerPolicyConfig(kSutEgressPortSchedulerPolicy, *gnmi_stub));
    ASSERT_OK(testbed->Environment().StoreTestArtifact(
        absl::StrCat(kSutEgressPortSchedulerPolicy, "_after_update.json"),
        FormatJsonBestEffort(updated_scheduler_config)));
  }

  // Connect to Ixia and fix some parameters.
  LOG(INFO) << "configuring Ixia traffic";
  ASSERT_OK_AND_ASSIGN(const std::string kIxiaHandle,
                       ixia::ConnectToIxia(*testbed));
  ASSERT_OK_AND_ASSIGN(
      const std::string kIxiaMainSrcPortHandle,
      ixia::IxiaVport(kIxiaHandle, kIxiaMainSrcPort, *testbed));
  ASSERT_OK_AND_ASSIGN(
      const std::string kIxiaAuxiliarySrcPortHandle,
      ixia::IxiaVport(kIxiaHandle, kIxiaAuxiliarySrcPort, *testbed));
  ASSERT_OK_AND_ASSIGN(const std::string kIxiaDstPortHandle,
                       ixia::IxiaVport(kIxiaHandle, kIxiaDstPort, *testbed));
  constexpr int kFrameSizeInBytes = 1000;
  const int kFramesPerSecondAtLineRate =
      .99 * kEgressLineRateInBytesPerSecond / kFrameSizeInBytes;

  // Configue IPv4 and IPv6 traffic items to all round-robin queues.
  std::vector<std::string> traffic_items;
  absl::flat_hash_map<std::string, std::string> queue_by_traffic_item_name;
  const int kNumRoundRobinTrafficItems = 2 * weights_by_queue_name.size();
  for (auto &[queue_name, weight] : weights_by_queue_name) {
    for (bool ipv4 : {true, false}) {
      ASSERT_THAT(kDscpsByQueueName,
                  Contains(Pair(Eq(queue_name), Not(IsEmpty()))));
      const int kDscp = kDscpsByQueueName.at(queue_name).at(0);
      const std::string kTrafficName = absl::StrFormat(
          "IPv%d packets with DSCP %d targeting queue '%s' with weight %d",
          ipv4 ? 4 : 6, kDscp, queue_name, weight);
      ixia::TrafficParameters traffic_params{
          .frame_size_in_bytes = kFrameSizeInBytes,
          .traffic_speed =
              ixia::FramesPerSecond{.frames_per_second =
                                        kFramesPerSecondAtLineRate /
                                        kNumRoundRobinTrafficItems},
      };
      if (ipv4) {
        traffic_params.ip_parameters = ixia::Ipv4TrafficParameters{
            .priority = ixia::IpPriority{.dscp = kDscp},
        };
      } else {
        traffic_params.ip_parameters = ixia::Ipv6TrafficParameters{
            .priority = ixia::IpPriority{.dscp = kDscp},
        };
      }
      ASSERT_OK_AND_ASSIGN(
          std::string traffic_item,
          ixia::SetUpTrafficItem(kIxiaMainSrcPortHandle, kIxiaDstPortHandle,
                                 kTrafficName, *testbed));
      ASSERT_OK(
          ixia::SetTrafficParameters(traffic_item, traffic_params, *testbed));
      traffic_items.push_back(traffic_item);
      queue_by_traffic_item_name[kTrafficName] = queue_name;
    }
  }
  // Set up auxilliary traffic to strictly prioritized queue.
  const std::string kAuxiliaryTrafficName = absl::StrFormat(
      "Auxiliary IPv4 packets with DSCP %d targeting strictly prioritized "
      "queue '%s' with PIR = %d bytes/second",
      kStrictlyPrioritizedIpv4Dscp, *strictly_prioritized_queue,
      kStrictlyPrioritizedPir);
  ASSERT_OK_AND_ASSIGN(
      const std::string kAuxilliaryTrafficItem,
      ixia::SetUpTrafficItem(kIxiaAuxiliarySrcPortHandle, kIxiaDstPortHandle,
                             kAuxiliaryTrafficName, *testbed));
  ASSERT_OK(ixia::SetTrafficParameters(
      kAuxilliaryTrafficItem,
      ixia::TrafficParameters{
          .frame_size_in_bytes = kFrameSizeInBytes,
          .traffic_speed = ixia::FramesPerSecond{kFramesPerSecondAtLineRate},
          .ip_parameters =
              ixia::Ipv4TrafficParameters{
                  .priority =
                      ixia::IpPriority{.dscp = kStrictlyPrioritizedIpv4Dscp},
              },
      },
      *testbed));
  traffic_items.push_back(kAuxilliaryTrafficItem);

  if (GetParam().nsf_reboot) {
    // Traffic is verified only once after NSF Reboot is complete.
    ASSERT_OK(DoNsfRebootAndWaitForSwitchReadyOrRecover(
        testbed.get(), *GetParam().ssh_client_for_nsf));
    // Create a new P4rt session after NSF Reboot
    ASSERT_OK_AND_ASSIGN(sut_p4rt, pdpi::P4RuntimeSession::Create(sut));
  }
  // Start traffic.
  Counters kInitialPortCounters;
  ASSERT_OK_AND_ASSIGN(kInitialPortCounters,
                       GetCountersForInterface(kSutEgressPort, *gnmi_stub));
  LOG(INFO) << "starting traffic";
  ASSERT_OK(ixia::StartTraffic(traffic_items, kIxiaHandle, *testbed));
  auto stop_traffic = absl::Cleanup(
      [&] { ASSERT_OK(ixia::StopTraffic(traffic_items, *testbed)); });
  LOG(INFO) << "traffic started -- sleeping for 3 second";
  absl::SleepFor(absl::Seconds(3));
  LOG(INFO) << "clearing table entries to limit buffer drainage after "
               "traffic is stopped";

  ASSERT_OK(pdpi::ClearEntities(*sut_p4rt));
  LOG(INFO) << "table entries cleared; stopping traffic";
  std::move(stop_traffic).Invoke();

  // Obtain traffic stats, and ensure traffic got forwarded according to
  // weights.
  ASSERT_OK_AND_ASSIGN(const ixia::TrafficStats kTrafficStats,
                       ixia::GetAllTrafficItemStats(kIxiaHandle, *testbed));

  ASSERT_OK_AND_ASSIGN(Counters final_port_counters,
                       GetCountersForInterface(kSutEgressPort, *gnmi_stub));

  SCOPED_TRACE(absl::StrCat("port counters incremented by ",
                            final_port_counters - kInitialPortCounters));
  SCOPED_TRACE(absl::StrCat("Initial port counters: ", kInitialPortCounters));
  SCOPED_TRACE(absl::StrCat("Final port counters: ", final_port_counters));
  absl::flat_hash_map<std::string, int64_t> num_rx_frames_by_queue;
  for (auto &[traffic_item_name, stats] :
       Ordered(kTrafficStats.stats_by_traffic_item())) {
    if (traffic_item_name == kAuxiliaryTrafficName) continue;
    ASSERT_OK_AND_ASSIGN(
        std::string queue,
        gutil::FindOrStatus(queue_by_traffic_item_name, traffic_item_name));
    num_rx_frames_by_queue[queue] += stats.num_rx_frames();
  }
  int64_t total_num_rx_frames = 0;
  for (auto &[_, rx] : num_rx_frames_by_queue) total_num_rx_frames += rx;
  int64_t total_weight = 0;
  for (auto &[_, weight] : weights_by_queue_name) total_weight += weight;
  for (auto &[queue, num_rx_frames] : num_rx_frames_by_queue) {
    ASSERT_OK_AND_ASSIGN(int64_t weight,
                         gutil::FindOrStatus(weights_by_queue_name, queue));
    const double kExpectedFraction = 1. * weight / total_weight;
    // If received packets are 0, then the fraction is 0 (can't divide by 0).
    const double kActualFraction =
        total_num_rx_frames == 0 ? 0 : 1. * num_rx_frames / total_num_rx_frames;
    const double kAbsoluteError = kActualFraction - kExpectedFraction;
    const double kRelativeErrorPercent =
        100. * kAbsoluteError / kExpectedFraction;
    const double kAcceptableErrorPercent = 10;
    LOG(INFO) << "'" << queue << "' transmitted " << (kActualFraction * 100)
              << "% of forwarded round-robin traffic (expected: "
              << (kExpectedFraction * 100)
              << "%, error: " << kRelativeErrorPercent << "%)";
    EXPECT_LE(std::abs(kRelativeErrorPercent), kAcceptableErrorPercent)
        << "expected '" << queue << "' to transmit "
        << (kExpectedFraction * 100)
        << "% of the forwarded round-robin traffic; instead, it "
           "transmitted "
        << (kActualFraction * 100)
        << "% of the forwarded traffic (error: " << kRelativeErrorPercent
        << "%)";
  }
  LOG(INFO) << "-- Test done -------------------------------------------------";
}

// The purpose of this test is to verify that strict queues are strictly
// prioritized over all lower-priority queues.
// We test one strict "queue under test" at a time by injecting two types of
// traffic:
// - Main traffic: IPv{4,6} packets targetting the strict queue, at >= 100%
//   egress line rate.
// - Background traffic: mixed IPv{4,6} packets targetting all queues, at 100%
//   egress line rate overall.
//
// We then verify that the queue under test forwards traffic at a rate
//   R = egress line rate - background traffic rate to higher priority queues
//                        - sum of CIRs of other queues
// where the CIRs are chosen low enough to be fully saturated by the background
// traffic. We repeat this for CIRs = 0 and CIRs > 0.
TEST_P(FrontpanelQosTest, StrictQueuesAreStrictlyPrioritized) {
  LOG(INFO) << "-- Test started ----------------------------------------------";
  LOG(INFO) << "obtaining testbed handle";
  // Pick a testbed with SUT connected to an Ixia on 3 ports, so we can
  // oversubscribe a switch egress port.
  auto requirements = gutil::ParseProtoOrDie<thinkit::TestRequirements>(
      R"pb(
        interface_requirements { count: 3 interface_mode: TRAFFIC_GENERATOR }
      )pb");
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<thinkit::GenericTestbed> testbed,
      GetParam().testbed_interface->GetTestbedWithRequirements(requirements));

  // Pick 3 SUT ports connected to the Ixia, 2 for receiving test packets and
  // 1 for forwarding them back. We use the faster links for injecting packets
  // so we can oversubsribe the egress port. We inject the traffic for the
  // round-robin queues via one ingress port, and auxilliary traffic for a
  // strictly-prioritized queue via another ingress port.
  LOG(INFO) << "picking test packet links";
  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, testbed->Sut().CreateGnmiStub());
  // Get Ixia connected links.
  ASSERT_OK_AND_ASSIGN(IxiaLinks links,
                       GetIxiaLinks(*testbed, *gnmi_stub, GetParam()));

  const std::string &kSutMainTrafficInPort =
      links.ingress_links[0].sut_interface;
  const std::string &kSutBackgroundTrafficInPort =
      links.ingress_links[1].sut_interface;
  const std::string &kSutEgressPort = links.egress_link.sut_interface;
  const std::string &kIxiaMainTrafficSrcPort =
      links.ingress_links[0].ixia_interface;
  const std::string &kIxiaBackgroundTrafficSrcPort =
      links.ingress_links[1].ixia_interface;
  const std::string &kIxiaDstPort = links.egress_link.ixia_interface;
  LOG(INFO) << absl::StrFormat(
      "Test packet routes:"
      "\n- Main traffic: "
      "[Ixia: %s] == %.1f Gbps => [SUT: %s] -> [SUT: %s] == %.1f Gbps => "
      "[Ixia: %s]"
      "\n- Background traffic: "
      "[Ixia: %s] == %.1f Gbps => [SUT: %s] -> [SUT: %s] == %.1f Gbps => "
      "[Ixia: %s]",
      kIxiaMainTrafficSrcPort,
      links.ingress_links[0].sut_interface_bits_per_second / 1'000'000'000.,
      kSutMainTrafficInPort, kSutEgressPort,
      links.egress_link.sut_interface_bits_per_second / 1'000'000'000.,
      kIxiaDstPort, kIxiaBackgroundTrafficSrcPort,
      links.ingress_links[1].sut_interface_bits_per_second / 1'000'000'000.,
      kSutBackgroundTrafficInPort, kSutEgressPort,
      links.egress_link.sut_interface_bits_per_second / 1'000'000'000.,
      kIxiaDstPort);
  ASSERT_OK_AND_ASSIGN(
      const std::string kSutEgressPortSchedulerPolicy,
      GetSchedulerPolicyNameByEgressPort(kSutEgressPort, *gnmi_stub));
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
  ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(GetParam().p4info));
  netaddr::Ipv6Address kIpv6McastAddresses[64];
  netaddr::Ipv4Address kIpv4McastAddresses[64];
  for (int dscp = 0; dscp < 64; ++dscp) {
    kIpv6McastAddresses[dscp] =
        netaddr::Ipv6Address(0xff00, 0, 0, 0, 0, 0, 0, dscp + 1);
    kIpv4McastAddresses[dscp] = netaddr::Ipv4Address(224, 0, 0, dscp + 1);
  }

  using DscpsByQueueName = absl::flat_hash_map<std::string, std::vector<int>>;
  std::optional<DscpsByQueueName> kDscpsByQueueName;
  bool testing_multicast = false;
  if (GetParam().multicast_queue_by_dscp.has_value()) {
    ASSERT_OK_AND_ASSIGN(
        auto entries, ConstructEntriesToForwardMcastTrafficToGivenPort(
                          ir_p4info, kSutEgressPortP4rtId, kIpv6McastAddresses,
                          kIpv4McastAddresses, /*num_mcast_addresses=*/64));
    ASSERT_OK(pdpi::InstallPiEntities(sut_p4rt.get(), ir_p4info, entries));
    ASSERT_OK_AND_ASSIGN(
        kDscpsByQueueName,
        GetQueueToDscpsMapping(*GetParam().multicast_queue_by_dscp));
    testing_multicast = true;
    // Set test case ID.
  } else if (GetParam().queue_by_dscp.has_value()) {
    ASSERT_OK_AND_ASSIGN(std::vector<p4::v1::Entity> entities,
                         sai::EntryBuilder()
                             .AddEntriesForwardingIpPacketsToGivenPort(
                                 /*egress_port=*/kSutEgressPortP4rtId,
                                 /*ip_version=*/sai::IpVersion::kIpv4And6,
                                 /*rewrite_options*/ kNextHopRewriteOptions)
                             .LogPdEntries()
                             .GetDedupedPiEntities(ir_p4info));
    ASSERT_OK(pdpi::InstallPiEntities(sut_p4rt.get(), ir_p4info, entities));
    ASSERT_OK_AND_ASSIGN(kDscpsByQueueName,
                         GetQueueToDscpsMapping(*GetParam().queue_by_dscp));
  } else {
    GTEST_SKIP() << "no queue_by_dscp or multicast_queue_by_dscp configured";
  }

  // Obtain queues and DSCPs for the queues.
  ASSERT_OK_AND_ASSIGN(
      std::vector<QueueInfo> queues_from_highest_to_lowest_priority,
      GetQueuesForSchedulerPolicyInDescendingOrderOfPriority(
          kSutEgressPortSchedulerPolicy, *gnmi_stub));
  // Remove queues which are not present in the dscp map passed in.
  for (auto i = queues_from_highest_to_lowest_priority.begin();
       i != queues_from_highest_to_lowest_priority.end();) {
    if (kDscpsByQueueName.has_value() &&
        !kDscpsByQueueName->contains(i->name)) {
      i = queues_from_highest_to_lowest_priority.erase(i);
    } else {
      ++i;
    }
  }
  std::vector<QueueInfo> strict_queues_from_highest_to_lowest_priority;
  for (auto &queue : queues_from_highest_to_lowest_priority) {
    if (queue.type == QueueType::kStrictlyPrioritized) {
      strict_queues_from_highest_to_lowest_priority.push_back(queue);
    }
  }
  if (strict_queues_from_highest_to_lowest_priority.empty()) {
    GTEST_SKIP() << "no strict queues configured, nothing to test";
  }
  LOG(INFO)
      << "Testing the following strict queues (highest to lowest priority): "
      << absl::StrJoin(strict_queues_from_highest_to_lowest_priority, " > ",
                       [](std::string *out, const auto &queue) {
                         absl::StrAppend(out, queue.name);
                       });

  // Restore scheduler config at the end of the test, so we can freely modify.
  ASSERT_OK_AND_ASSIGN(
      const std::string kInitialSchedulerConfig,
      GetSchedulerPolicyConfig(kSutEgressPortSchedulerPolicy, *gnmi_stub));
  const auto kRestoreSchedulerConfig = absl::Cleanup([&] {
    EXPECT_OK(UpdateSchedulerPolicyConfig(kSutEgressPortSchedulerPolicy,
                                          kInitialSchedulerConfig, *gnmi_stub))
        << "failed to restore initial scheduler config -- switch config may be "
           "corrupted, causing subsequent test to fail";
  });

  // Configure fair buffer profile (until the end of the test) so we can ignore
  // buffer carving effects.
  ASSERT_OK_AND_ASSIGN(Cleanup restore_buffer_config,
                       ConfigureFairBufferConfigForPortUntilEndOfScope(
                           kSutEgressPort, *gnmi_stub));

  // Connect to Ixia and fix constant traffic parameters.
  LOG(INFO) << "connecting to Ixia";
  ASSERT_OK_AND_ASSIGN(const std::string kIxiaHandle,
                       ixia::ConnectToIxia(*testbed));
  ASSERT_OK_AND_ASSIGN(
      const std::string kIxiaMainTrafficSrcPortHandle,
      ixia::IxiaVport(kIxiaHandle, kIxiaMainTrafficSrcPort, *testbed));
  ASSERT_OK_AND_ASSIGN(
      const std::string kIxiaBackgroundTrafficSrcPortHandle,
      ixia::IxiaVport(kIxiaHandle, kIxiaBackgroundTrafficSrcPort, *testbed));
  ASSERT_OK_AND_ASSIGN(const std::string kIxiaDstPortHandle,
                       ixia::IxiaVport(kIxiaHandle, kIxiaDstPort, *testbed));
  const int kNumQueueus = queues_from_highest_to_lowest_priority.size();
  const int kNumRoundRobinQueues =
      kNumQueueus - strict_queues_from_highest_to_lowest_priority.size();
  const int kNumBackgroundTrafficItems = 2 * kNumQueueus;  // IPv4 & IPv6
  constexpr int kFrameSizeInBytes = 1514;
  const int64_t kEgressLineRateInBytesPerSecond =
      links.egress_link.sut_interface_bits_per_second / 8;
  const int kEgressLineRateInFramesPerSecond =
      .99 * kEgressLineRateInBytesPerSecond / kFrameSizeInBytes;
  const int kFramesPerSecondPerTrafficItem =
      kEgressLineRateInFramesPerSecond / kNumBackgroundTrafficItems;
  const int64_t kBytesPerSecondPerTrafficItem =
      kEgressLineRateInBytesPerSecond / kNumBackgroundTrafficItems;

  // Main test, testing one strict queue under test at a time.
  for (const QueueInfo &queue_under_test :
       strict_queues_from_highest_to_lowest_priority) {
    LOG(INFO) << "== QUEUE UNDER TEST: " << queue_under_test.name << " =======";
    SCOPED_TRACE(absl::StrCat("queue under test: ", queue_under_test.name));

    // We run the test in two variants:
    // - Without CIRs. In this case, the strict queue under test competes
    //   for egress bandwith only with higher prioritized strict queues.
    // - With CIRs. In this case, the strict queue under test competes
    //   for egress bandwith also with all queues with a CIR, since CIRs get
    //   served first. We configure CIRs uniformly, for round robin queues only.
    for (const double kCirsFractionOfEgressLineRate : {0., .40}) {
      SCOPED_TRACE(absl::StrCat("CIR fraction of egress line rate: ",
                                kCirsFractionOfEgressLineRate * 100, "%"));
      // Set lower & upper queue bounds (CIRs/PIRs).
      LOG(INFO) << "configuring scheduler parameters: CIRs = "
                << kCirsFractionOfEgressLineRate * 100 << "% egress line rate";
      absl::flat_hash_map<std::string, SchedulerParameters>
          params_by_queue_name;
      // We split the overall CIR uniformly among all round robin queues.
      const int64_t kRoundRobinQueueCir = kCirsFractionOfEgressLineRate *
                                          kEgressLineRateInBytesPerSecond /
                                          kNumRoundRobinQueues;
      for (const QueueInfo &queue : queues_from_highest_to_lowest_priority) {
        SchedulerParameters &params = params_by_queue_name[queue.name];
        params.committed_information_rate =
            queue.type == QueueType::kRoundRobin ? kRoundRobinQueueCir : 0;
        params.peak_information_rate = kEgressLineRateInBytesPerSecond;
        if (queue.type == QueueType::kRoundRobin) {
          LOG(INFO) << "Round robin queue: " << queue.name
                    << " CIR = " << kRoundRobinQueueCir;
        }
      }
      ASSERT_OK(SetSchedulerPolicyParameters(kSutEgressPortSchedulerPolicy,
                                             params_by_queue_name, *gnmi_stub));

      // Configure traffic.
      LOG(INFO) << "configuring traffic";
      std::vector<std::string> traffic_items;
      absl::flat_hash_map<std::string, QueueInfo> queue_by_traffic_item_name;
      auto delete_traffic_items = absl::Cleanup([&] {
        LOG(INFO) << "deleting traffic items";
        for (auto &traffic_item : traffic_items) {
          EXPECT_OK(pins::TryUpToNTimes(3, absl::Seconds(1), [&] {
            return ixia::DeleteTrafficItem(traffic_item, *testbed);
          }));
        }
      });
      for (bool ipv4 : {true, false}) {
        // Configuring main traffic targetting queue under test.
        {
          ASSERT_THAT(kDscpsByQueueName,
                      Optional(Contains(
                          Pair(Eq(queue_under_test.name), Not(IsEmpty())))));
          const int kDscp =
              kDscpsByQueueName.value().at(queue_under_test.name).at(0);
          const std::string kTrafficName = absl::StrFormat(
              "main traffic: %d MB/s of IPv%d packets/second with DSCP %d "
              "targeting %s queue '%s'",
              kEgressLineRateInBytesPerSecond / 1'000'000, ipv4 ? 4 : 6, kDscp,
              queue_under_test.type == QueueType::kStrictlyPrioritized
                  ? "strict"
                  : "round-robin",
              queue_under_test.name);
          ixia::TrafficParameters traffic_params{
              .frame_size_in_bytes = kFrameSizeInBytes,
              // 50/50 for IPv4/IPv6.
              .traffic_speed =
                  ixia::FramesPerSecond{kEgressLineRateInFramesPerSecond / 2},
          };
          if (testing_multicast) {
            if (ipv4) {
              traffic_params.dst_mac =
                  netaddr::MacAddress(1, 0, 0x5e, 0, 0, kDscp);
              traffic_params.ip_parameters = ixia::Ipv4TrafficParameters{
                  .src_ipv4 = netaddr::Ipv4Address(192, 168, 2, kDscp),
                  .dst_ipv4 = kIpv4McastAddresses[kDscp],
                  // Set ECN 0 to avoid RED drops.
                  .priority = ixia::IpPriority{.dscp = kDscp, .ecn = 0},
              };
            } else {
              traffic_params.dst_mac =
                  netaddr::MacAddress(0x33, 0x33, 0, 0, 0, kDscp);
              traffic_params.ip_parameters = ixia::Ipv6TrafficParameters{
                  .src_ipv6 =
                      netaddr::Ipv6Address(0x1000, 0, 0, 0, 0, 0, 0, kDscp),
                  .dst_ipv6 = kIpv6McastAddresses[kDscp],
                  // Set ECN 0 to avoid RED drops.
                  .priority = ixia::IpPriority{.dscp = kDscp, .ecn = 0},
              };
            }
          } else {
            if (ipv4) {
              traffic_params.ip_parameters = ixia::Ipv4TrafficParameters{
                  .priority = ixia::IpPriority{.dscp = kDscp},
              };
            } else {
              traffic_params.ip_parameters = ixia::Ipv6TrafficParameters{
                  .priority = ixia::IpPriority{.dscp = kDscp},
              };
            }
          }
          ASSERT_OK_AND_ASSIGN(std::string traffic_item,
                               ixia::SetUpTrafficItem(
                                   kIxiaMainTrafficSrcPortHandle,
                                   kIxiaDstPortHandle, kTrafficName, *testbed));
          ASSERT_OK(ixia::SetTrafficParameters(traffic_item, traffic_params,
                                               *testbed));
          traffic_items.push_back(traffic_item);
          queue_by_traffic_item_name[kTrafficName] = queue_under_test;
        }

        // Configure background traffic, for all queues including the queue
        // under test.
        for (const QueueInfo &queue : queues_from_highest_to_lowest_priority) {
          LOG(INFO) << "configuring background traffic for queue: "
                    << queue.name;
          ASSERT_THAT(kDscpsByQueueName,
                      Optional(Contains(Pair(Eq(queue.name), Not(IsEmpty())))));
          const int kDscp = kDscpsByQueueName->at(queue.name).at(0);
          const std::string kTrafficName = absl::StrFormat(
              "background traffic: %d MB/s of IPv%d packets/second with DSCP "
              "%d targeting %s queue '%s'",
              kBytesPerSecondPerTrafficItem / 1'000'000, ipv4 ? 4 : 6, kDscp,
              queue.type == QueueType::kStrictlyPrioritized ? "strict"
                                                            : "round-robin",
              queue.name);
          ixia::TrafficParameters traffic_params{
              .frame_size_in_bytes = kFrameSizeInBytes,
              .traffic_speed =
                  ixia::FramesPerSecond{kFramesPerSecondPerTrafficItem},
          };
          if (testing_multicast) {
            if (ipv4) {
              traffic_params.dst_mac =
                  netaddr::MacAddress(1, 0, 0x5e, 0, 0, kDscp);
              traffic_params.ip_parameters = ixia::Ipv4TrafficParameters{
                  .src_ipv4 = netaddr::Ipv4Address(192, 168, 2, kDscp),
                  .dst_ipv4 = kIpv4McastAddresses[kDscp],
                  // Set ECN 0 to avoid RED drops.
                  .priority = ixia::IpPriority{.dscp = kDscp, .ecn = 0},
              };
            } else {
              traffic_params.dst_mac =
                  netaddr::MacAddress(0x33, 0x33, 0, 0, 0, kDscp);
              traffic_params.ip_parameters = ixia::Ipv6TrafficParameters{
                  .src_ipv6 =
                      netaddr::Ipv6Address(0x1000, 0, 0, 0, 0, 0, 0, kDscp),
                  .dst_ipv6 = kIpv6McastAddresses[kDscp],
                  // Set ECN 0 to avoid RED drops.
                  .priority = ixia::IpPriority{.dscp = kDscp, .ecn = 0},
              };
            }
          } else {
            if (ipv4) {
              traffic_params.ip_parameters = ixia::Ipv4TrafficParameters{
                  .priority = ixia::IpPriority{.dscp = kDscp},
              };
            } else {
              traffic_params.ip_parameters = ixia::Ipv6TrafficParameters{
                  .priority = ixia::IpPriority{.dscp = kDscp},
              };
            }
          }
          ASSERT_OK_AND_ASSIGN(std::string traffic_item,
                               ixia::SetUpTrafficItem(
                                   kIxiaBackgroundTrafficSrcPortHandle,
                                   kIxiaDstPortHandle, kTrafficName, *testbed));
          ASSERT_OK(ixia::SetTrafficParameters(traffic_item, traffic_params,
                                               *testbed));
          traffic_items.push_back(traffic_item);
          queue_by_traffic_item_name[kTrafficName] = queue;
        }
      }

      std::vector<TestOperations> test_operations;

      test_operations.push_back(TestOperations::TrafficTest);

      if (GetParam().nsf_reboot) {
        ASSERT_OK(NsfReboot(testbed.get()));
        test_operations.push_back(TestOperations::NsfRebootAndTrafficTest);
      }

      // Send traffic twice, once during NSF reboot and once post the reboot
      // to ensure the forwarding traffic is not disrupted.
      for (auto test_operation : test_operations) {
        if (test_operation == TestOperations::NsfRebootAndTrafficTest &&
            GetParam().ssh_client_for_nsf) {
          ASSERT_OK(
              WaitForNsfReboot(testbed.get(), *GetParam().ssh_client_for_nsf));
          LOG(INFO) << "NSF reboot complete, sending traffic again to ensure "
                       "the forwarding traffic is not disrupted.";
        }
        bool not_after_nsf_reboot =
            !GetParam().nsf_reboot ||
            test_operation == TestOperations::NsfRebootAndTrafficTest;
        Counters kInitialPortCounters;
        if (not_after_nsf_reboot) {
          // Get initial port counters after NSF Reboot is complete since
          // gnmi calls cannot be made during NSF reboot.
          ASSERT_OK_AND_ASSIGN(
              kInitialPortCounters,
              GetCountersForInterface(kSutEgressPort, *gnmi_stub));
        }

        // Run traffic for a while, then obtain stats.
        LOG(INFO) << "starting traffic (" << traffic_items.size() << " items)";
        // Occasionally the Ixia API cannot keep up and starting traffic
        // fails, so we try up to 3 times.
        ASSERT_OK(pins::TryUpToNTimes(3, /*delay=*/absl::Seconds(1), [&] {
          return ixia::StartTraffic(traffic_items, kIxiaHandle, *testbed);
        }));
        LOG(INFO) << "traffic started; sleeping for 3 seconds";
        absl::SleepFor(absl::Seconds(3));
        LOG(INFO) << "stopping traffic";
        ASSERT_OK(ixia::StopTraffic(traffic_items, *testbed));

        // Obtain traffic stats, and ensure queue under test got scheduled
        // for expected percentage of traffic.
        LOG(INFO) << "obtaining traffic stats";
        ASSERT_OK_AND_ASSIGN(
            const ixia::TrafficStats kTrafficStats,
            ixia::GetAllTrafficItemStats(kIxiaHandle, *testbed));
        
        if (not_after_nsf_reboot) {
          // Get port counters after NSF Reboot is complete since
          // gnmi calls cannot be made during NSF reboot.
          ASSERT_OK_AND_ASSIGN(
              Counters final_port_counters,
              GetCountersForInterface(kSutEgressPort, *gnmi_stub));

          SCOPED_TRACE(
              absl::StrCat("port counters incremented by ",
                           final_port_counters - kInitialPortCounters));
          SCOPED_TRACE(
              absl::StrCat("Initial port counters: ", kInitialPortCounters));
          SCOPED_TRACE(
              absl::StrCat("Final port counters: ", final_port_counters));
        }

        LOG(INFO) << "validating traffic stats against expectation";
        double bytes_per_second_received = 0;
        for (auto &[traffic_item, stats] :
             kTrafficStats.stats_by_traffic_item()) {
          ASSERT_OK_AND_ASSIGN(
              QueueInfo traffic_item_queue,
              gutil::FindOrStatus(queue_by_traffic_item_name, traffic_item));
          if (traffic_item_queue.name == queue_under_test.name) {
            bytes_per_second_received += ixia::BytesPerSecondReceived(stats);
          }
        }
        std::vector<std::string> higher_priority_queues;
        for (const QueueInfo &queue :
             strict_queues_from_highest_to_lowest_priority) {
          if (queue.name == queue_under_test.name) break;
          higher_priority_queues.push_back(queue.name);
        }
        const double kBytesPerSecondToHigherPriorityQueues =
            2 * higher_priority_queues.size() * kBytesPerSecondPerTrafficItem;
        LOG(INFO) << "higher priority queues "
                  << absl::StrJoin(higher_priority_queues, ", ")
                  << " contest for " << kBytesPerSecondToHigherPriorityQueues
                  << " bytes/s of the egress line rate ("
                  << 100. * kBytesPerSecondToHigherPriorityQueues /
                         kEgressLineRateInBytesPerSecond
                  << "%)";
        LOG(INFO) << "lower priority queues with CIRs contest for "
                  << (kCirsFractionOfEgressLineRate *
                      kEgressLineRateInBytesPerSecond)
                  << " bytes/s of the egress line rate ("
                  << kCirsFractionOfEgressLineRate * 100 << "%)";
        const double kBytesPerSecondExpected =
            (1 - kCirsFractionOfEgressLineRate) *
                kEgressLineRateInBytesPerSecond -
            kBytesPerSecondToHigherPriorityQueues;
        const double kAbsoluteError =
            bytes_per_second_received - kBytesPerSecondExpected;
        const double kRelativeErrorPercent =
            100. * kAbsoluteError / kBytesPerSecondExpected;
        const double kAcceptableErrorPercent = 3;
        LOG(INFO) << "received " << bytes_per_second_received
                  << " bytes/s from queue " << queue_under_test.name
                  << " (expected: " << kBytesPerSecondExpected
                  << "bytes/s, error: " << kRelativeErrorPercent << "%)";
        EXPECT_LE(std::abs(kRelativeErrorPercent), kAcceptableErrorPercent)
            << "expected to receive " << kBytesPerSecondExpected
            << " bytes/s, but received " << bytes_per_second_received
            << " bytes/s";
      }
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
  if (GetParam().multicast_queue_by_dscp.has_value()) {
    GTEST_SKIP() << "ECN not supported for multicast queues.";
  }
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


  thinkit::Switch &sut = testbed->Sut();
  // Set up P4Runtime session.
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<pdpi::P4RuntimeSession> sut_p4_session,
      pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
          sut, /*gnmi_config=*/absl::nullopt, GetParam().p4info));

  // Hook up to GNMI.
  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, testbed->Sut().CreateGnmiStub());

  // Get Ixia connected links.
  ASSERT_OK_AND_ASSIGN(IxiaLinks links,
                       GetIxiaLinks(*testbed, *gnmi_stub, GetParam()));

  const std::string &kSutInPort1 = links.ingress_links[0].sut_interface;
  const std::string &kIxiaTxPort1 = links.ingress_links[0].ixia_interface;

  const std::string &kSutInPort2 = links.ingress_links[1].sut_interface;
  const std::string &kIxiaTxPort2 = links.ingress_links[1].ixia_interface;

  const std::string &kSutOutPort = links.egress_link.sut_interface;
  const std::string &kIxiaRxPort = links.egress_link.ixia_interface;

  LOG(INFO) << absl::StrFormat(
      "Test packet route: [Ixia: %s]/[Ixia: %s] => [SUT: %s]/[SUT: %s] -> "
      "[SUT: %s] => [Ixia: %s]",
      kIxiaTxPort1, kIxiaTxPort2, kSutInPort1, kSutInPort2, kSutOutPort,
      kIxiaRxPort);

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

  ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(GetParam().p4info));

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
  std::optional<QueueNameByDscp> queue_name_by_ipv4_dscp =
      GetParam().queue_by_dscp;
  std::optional<QueueNameByDscp> queue_name_by_ipv6_dscp =
      GetParam().queue_by_dscp;
  const std::string kDefaultQueueName = "BE1";

  // Set up the switch to forward inbound packets to the egress port
  // Configure the switch to send all incoming packets out of the chosen egress
  // port.
  ASSERT_OK_AND_ASSIGN(
      const sai::TableEntries kTableEntries,
      ConstructEntriesToForwardAllTrafficToLoopbackPortAndCopyEcnPacketsToCPU(
          ir_p4info,
          /*p4rt_out_port_id=*/kSutOutPortId,
          /*p4rt_in_port1_id=*/kSutInPort1Id,
          /*p4rt_in_port2_id=*/kSutInPort2Id, GetParam().default_cpu_queue,
          GetParam().high_prio_cpu_queue));
  ASSERT_OK(testbed->Environment().StoreTestArtifact("pd_entries.textproto",
                                                     kTableEntries));

  ASSERT_OK(pdpi::InstallPdTableEntries(*sut_p4_session, kTableEntries));

  if (GetParam().nsf_reboot) {
    // Traffic is verified only once after NSF Reboot is complete.
    ASSERT_OK(DoNsfRebootAndWaitForSwitchReadyOrRecover(
        testbed.get(), *GetParam().ssh_client_for_nsf));
    // Create a new P4rt session after NSF Reboot
    ASSERT_OK_AND_ASSIGN(sut_p4_session, pdpi::P4RuntimeSession::Create(sut));
  }

  // Listen for punted packets from the SUT.
  EcnTestPacketCounters packet_receive_info;
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
              (kWredMaxThresholdInBytes * 1.5 / kDefaultFrameSizeinBytes),
              *testbed));
        } else {
          // Set traffic to 70 percent of line rate.
          ASSERT_OK(pins_test::ixia::SetFrameRate(
              traffic_ref1, frame_rate_at_line_speed_of_in_port1 * 70 / 100,
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
        ASSERT_OK_AND_ASSIGN(const int64_t ecn_counter_before_traffic,
                             GetGnmiPortEcnCounter(kSutOutPort, *gnmi_stub));

        ResetEcnTestPacketCounters(packet_receive_info);

        Counters kInitialPortCounters;
        ASSERT_OK_AND_ASSIGN(kInitialPortCounters,
                             GetCountersForInterface(kSutOutPort, *gnmi_stub));
        ASSERT_OK(pins::TryUpToNTimes(3, /*delay=*/absl::Seconds(1), [&] {
          return pins_test::ixia::StartTraffic(ixia_setup_result.traffic_refs,
                                               ixia_setup_result.topology_ref,
                                               *testbed);
        }));

        // Time period to examine egress packets for ECN marking.
        constexpr absl::Duration kStatsCollectionTime = absl::Seconds(10);

        absl::SleepFor(kStatsCollectionTime);

        {
          // We will be verifying for congestion bit in sampled packets
          // received at Receiver.
          absl::MutexLock lock(&packet_receive_info.mutex);
          LOG(INFO) << "Congestion : " << (is_congestion ? "true" : "false");
          LOG(INFO) << "IPv4 : " << (is_ipv4 ? "true" : "false");
          LOG(INFO) << "ECT : " << (is_ect ? "true" : "false");
          LOG(INFO) << "ECN marked Packets: "
                    << packet_receive_info.num_packets_ecn_marked;

          if (is_congestion && is_ect) {
            ASSERT_GT(packet_receive_info.num_packets_ecn_marked, 0);
            EXPECT_THAT(GetGnmiPortEcnCounter(kSutOutPort, *gnmi_stub),
                        IsOkAndHolds(Gt(ecn_counter_before_traffic)));
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
        
        ASSERT_OK_AND_ASSIGN(Counters final_port_counters,
                             GetCountersForInterface(kSutOutPort, *gnmi_stub));

        SCOPED_TRACE(absl::StrCat("port counters incremented by ",
                                  final_port_counters - kInitialPortCounters));
        SCOPED_TRACE(
            absl::StrCat("Initial port counters: ", kInitialPortCounters));
        SCOPED_TRACE(
            absl::StrCat("Final port counters: ", final_port_counters));

        // Read counters of the target queue.
        ASSERT_OK_AND_ASSIGN(
            const QueueCounters queue_counters_after_test_packet,
            GetGnmiQueueCounters(/*port=*/kSutOutPort,
                                 /*queue=*/target_queue, *gnmi_stub));
        
        SCOPED_TRACE(absl::StrCat("Queue counters before test packet: ",
                                  ToString(queue_counters_before_test_packet)));
        SCOPED_TRACE(absl::StrCat("Queue counters after test packet: ",
                                  ToString(queue_counters_after_test_packet)));
        // This test expects WRED config to only mark packets and not
        // drop. Expect no drops in target queue and queue transmit
        // counter increments.
        EXPECT_EQ(queue_counters_after_test_packet.num_packets_dropped,
                  queue_counters_before_test_packet.num_packets_dropped);

        EXPECT_GT(queue_counters_after_test_packet.num_packets_transmitted,
                  queue_counters_before_test_packet.num_packets_transmitted);
      }
    }
  }
}

// The purpose of this test is to verify Buffer configuration applies
// on egress port queues. The test will oversubscribe egress port with equal
// traffic for different queues. At the end of the test we verify if
// queues which are allocated more buffer transmit more packets.
TEST_P(FrontpanelBufferTest, BufferCarving) {
  LOG(INFO) << "---------------- Test started ---------------------";
  switch (GetParam().config_to_be_tested) {
    case kSharedStaticLimit:
      LOG(INFO) << "Testing shared static limit";
      break;
    case kDedicatedBuffer:
      LOG(INFO) << "Testing dedicated buffer";
      break;
    case kSharedAlpha:
    default:
      LOG(INFO) << "Testing shared alpha";
  }
  LOG(INFO) << "obtaining testbed handle";
  // Pick a testbed with SUT connected to an Ixia on 3 ports, so we can
  // oversubscribe a switch egress port.
  auto requirements = gutil::ParseProtoOrDie<thinkit::TestRequirements>(
      R"pb(
        interface_requirements { count: 3 interface_mode: TRAFFIC_GENERATOR }
      )pb");
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<thinkit::GenericTestbed> testbed,
      GetParam().default_params.testbed_interface->GetTestbedWithRequirements(
          requirements));

  // Pick 3 SUT ports connected to the Ixia, 2 for receiving test packets and
  // 1 for forwarding them back. We use the faster links for injecting packets
  // so we can oversubsribe the egress port.
  LOG(INFO) << "picking test packet links";
  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, testbed->Sut().CreateGnmiStub());
  // Get Ixia connected links.
  ASSERT_OK_AND_ASSIGN(IxiaLinks links,
                       GetIxiaLinks(*testbed, *gnmi_stub, GetParam()));

  const std::string &kSutIpv4IngressPort = links.ingress_links[0].sut_interface;
  const std::string &kSutIpv6IngressPort = links.ingress_links[1].sut_interface;
  const std::string &kSutEgressPort = links.egress_link.sut_interface;
  const std::string &kIxiaIpv4SrcPort = links.ingress_links[0].ixia_interface;
  const std::string &kIxiaIpv6SrcPort = links.ingress_links[1].ixia_interface;
  const std::string &kIxiaDstPort = links.egress_link.ixia_interface;
  LOG(INFO) << absl::StrFormat(
      "Test packet routes:"
      "\n- IPv4: [Ixia: %s] => [SUT: %s] -> [SUT: %s] => [Ixia: %s]"
      "\n- IPv6: [Ixia: %s] => [SUT: %s] -> [SUT: %s] => [Ixia: %s]",
      kIxiaIpv4SrcPort, kSutIpv4IngressPort, kSutEgressPort, kIxiaDstPort,
      kIxiaIpv6SrcPort, kSutIpv6IngressPort, kSutEgressPort, kIxiaDstPort);

  ASSERT_OK_AND_ASSIGN(
      const std::string kSutEgressPortBufferProfile,
      GetBufferAllocationProfileByEgressPort(kSutEgressPort, *gnmi_stub));
  LOG(INFO) << " Buffer Profile : " << kSutEgressPortBufferProfile;

  ASSERT_OK_AND_ASSIGN(
      const std::string kSutEgressPortSchedulerPolicy,
      GetSchedulerPolicyNameByEgressPort(kSutEgressPort, *gnmi_stub));
  absl::flat_hash_map<std::string, std::string> p4rt_id_by_interface;
  ASSERT_OK_AND_ASSIGN(p4rt_id_by_interface,
                       GetAllInterfaceNameToPortId(*gnmi_stub));
  ASSERT_OK_AND_ASSIGN(
      const std::string kSutEgressPortP4rtId,
      gutil::FindOrStatus(p4rt_id_by_interface, kSutEgressPort));

  // Configure the switch to send all incoming packets out of the chosen egress
  // port.
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt,
                       ConfigureSwitchAndReturnP4RuntimeSession(
                           testbed->Sut(), /*gnmi_config=*/std::nullopt,
                           GetParam().default_params.p4info));
  ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(GetParam().default_params.p4info));
  // Install entries for unicast queues.
  if (GetParam().default_params.queue_by_dscp.has_value()) {
    ASSERT_OK_AND_ASSIGN(std::vector<p4::v1::Entity> entities,
                         sai::EntryBuilder()
                             .AddEntriesForwardingIpPacketsToGivenPort(
                                 /*egress_port=*/kSutEgressPortP4rtId,
                                 /*ip_version=*/sai::IpVersion::kIpv4And6,
                                 /*rewrite_options*/ kNextHopRewriteOptions)
                             .LogPdEntries()
                             .GetDedupedPiEntities(ir_p4info));
    ASSERT_OK(pdpi::InstallPiEntities(sut_p4rt.get(), ir_p4info, entities));
  }

  netaddr::Ipv6Address kIpv6McastAddresses[64];
  netaddr::Ipv4Address kIpv4McastAddresses[64];
  for (int dscp = 0; dscp < 64; ++dscp) {
    kIpv6McastAddresses[dscp] =
        netaddr::Ipv6Address(0xff00, 0, 0, 0, 0, 0, 0, dscp + 1);
    kIpv4McastAddresses[dscp] = netaddr::Ipv4Address(224, 0, 0, dscp + 1);
  }

  // Install entries for multicast queues.
  if (GetParam().default_params.multicast_queue_by_dscp.has_value()) {

    ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_p4info,
                         pdpi::GetIrP4Info(*sut_p4rt));
    ASSERT_OK_AND_ASSIGN(
        auto entries, ConstructEntriesToForwardMcastTrafficToGivenPort(
                          ir_p4info, kSutEgressPortP4rtId, kIpv6McastAddresses,
                          kIpv4McastAddresses, 64));
    ASSERT_OK(pdpi::InstallPiEntities(sut_p4rt.get(), ir_p4info, entries));
  }

  // Before we update the scheduler config, save the current config and
  // prepare to restore it at the end of th test.
  ASSERT_OK_AND_ASSIGN(
      const std::string kInitialSchedulerConfig,
      GetSchedulerPolicyConfig(kSutEgressPortSchedulerPolicy, *gnmi_stub));
  const auto kRestoreSchedulerConfig = absl::Cleanup([&] {
    EXPECT_OK(UpdateSchedulerPolicyConfig(kSutEgressPortSchedulerPolicy,
                                          kInitialSchedulerConfig, *gnmi_stub))
        << "failed to restore initial scheduler config -- switch config may be "
           "corrupted, causing subsequent test to fail";
  });

  // Queues under test.
  const absl::flat_hash_map<std::string, BufferParameters> &
      kBufferParametersByQueueName = GetParam().buffer_parameters_by_queue_name;

  // Get strictly prioritized queues.
  ASSERT_OK_AND_ASSIGN(
      const absl::flat_hash_set<std::string> kStrictlyPrioritizedQueues,
      GetStrictlyPrioritizedQueuesMap(kSutEgressPortSchedulerPolicy,
                                      *gnmi_stub));

  // Set lower & upper bounds (CIRs/PIRs) such that they don't effect
  // scheduling, so we can focus on testing the buffer config.
  LOG(INFO) << "configuring scheduler parameters";
  {
    absl::flat_hash_map<std::string, SchedulerParameters> params_by_queue_name;
    for (auto &[queue_name, _] : kBufferParametersByQueueName) {
      if (!kStrictlyPrioritizedQueues.contains(queue_name)) {
        params_by_queue_name[queue_name].weight = 1;
      }
      params_by_queue_name[queue_name].committed_information_rate = 0;
      // Limit peak rate to 1% of line rate so queue is always full.
      params_by_queue_name[queue_name].peak_information_rate =
          0.01 * links.egress_link.sut_interface_bits_per_second / 8;
    }
    ASSERT_OK(SetSchedulerPolicyParameters(kSutEgressPortSchedulerPolicy,
                                           params_by_queue_name, *gnmi_stub));
    // Dump initial and modified configs, to ease debugging.
    ASSERT_OK(testbed->Environment().StoreTestArtifact(
        absl::StrCat(kSutEgressPortSchedulerPolicy, "_before_update.json"),
        FormatJsonBestEffort(kInitialSchedulerConfig)));
    ASSERT_OK_AND_ASSIGN(
        std::string updated_scheduler_config,
        GetSchedulerPolicyConfig(kSutEgressPortSchedulerPolicy, *gnmi_stub));
    ASSERT_OK(testbed->Environment().StoreTestArtifact(
        absl::StrCat(kSutEgressPortSchedulerPolicy, "_after_update.json"),
        FormatJsonBestEffort(updated_scheduler_config)));
  }

  // Before we update the buffer config, save the current config and
  // prepare to restore it at the end of th test.
  ASSERT_OK_AND_ASSIGN(const std::string kInitialBufferConfig,
                       GetBufferAllocationProfileConfig(
                           kSutEgressPortBufferProfile, *gnmi_stub));
  const auto kRestoreBufferConfig = absl::Cleanup([&] {
    EXPECT_OK(UpdateBufferAllocationProfileConfig(
        kSutEgressPortBufferProfile, kInitialBufferConfig, *gnmi_stub))
        << "failed to restore initial buffer config -- switch config may be "
           "corrupted, causing subsequent test to fail";
  });

  LOG(INFO) << "configuring buffer parameters";
  {
    ASSERT_OK(SetBufferConfigParameters(
        kSutEgressPortBufferProfile, kBufferParametersByQueueName, *gnmi_stub));
    // Dump initial and modified configs, to ease debugging.
    ASSERT_OK(testbed->Environment().StoreTestArtifact(
        absl::StrCat(kSutEgressPortBufferProfile, "_before_update.json"),
        FormatJsonBestEffort(kInitialBufferConfig)));
    ASSERT_OK_AND_ASSIGN(std::string updated_buffer_config,
                         GetBufferAllocationProfileConfig(
                             kSutEgressPortBufferProfile, *gnmi_stub));
    ASSERT_OK(testbed->Environment().StoreTestArtifact(
        absl::StrCat(kSutEgressPortBufferProfile, "_after_update.json"),
        FormatJsonBestEffort(updated_buffer_config)));
  }

  // Connect to Ixia and fix endpoints & parameters.
  LOG(INFO) << "configuring Ixia traffic";
  ASSERT_OK_AND_ASSIGN(const std::string kIxiaHandle,
                       ixia::ConnectToIxia(*testbed));
  ASSERT_OK_AND_ASSIGN(
      const std::string kIxiaIpv4SrcPortHandle,
      ixia::IxiaVport(kIxiaHandle, kIxiaIpv4SrcPort, *testbed));
  ASSERT_OK_AND_ASSIGN(
      const std::string kIxiaIpv6SrcPortHandle,
      ixia::IxiaVport(kIxiaHandle, kIxiaIpv6SrcPort, *testbed));
  ASSERT_OK_AND_ASSIGN(const std::string kIxiaDstPortHandle,
                       ixia::IxiaVport(kIxiaHandle, kIxiaDstPort, *testbed));
  constexpr int kFrameSizeInBytes = 1000;
  const int kTotalFramesPerSecond =
      links.egress_link.sut_interface_bits_per_second / (kFrameSizeInBytes * 8);
  const int kNumTrafficItemsPerLink = kBufferParametersByQueueName.size();
  const auto kTrafficItemSpeed =
      ixia::FramesPerSecond{kTotalFramesPerSecond / kNumTrafficItemsPerLink};

  // Figure out which DSCPs to use for each queue.
  using DscpsByQueueName = absl::flat_hash_map<std::string, std::vector<int>>;
  DscpsByQueueName kDscpsByUnicastQueueName;
  DscpsByQueueName kDscpsByMulticastQueueName;

  if (GetParam().default_params.queue_by_dscp.has_value()) {
    ASSERT_OK_AND_ASSIGN(
        kDscpsByUnicastQueueName,
        GetQueueToDscpsMapping(*GetParam().default_params.queue_by_dscp));
  }
  if (GetParam().default_params.multicast_queue_by_dscp.has_value()) {
    ASSERT_OK_AND_ASSIGN(
        kDscpsByMulticastQueueName,
        GetQueueToDscpsMapping(
            *GetParam().default_params.multicast_queue_by_dscp));
  }

  for (auto kDscpsByQueueName :
       {kDscpsByUnicastQueueName, kDscpsByMulticastQueueName}) {
    if (kDscpsByQueueName.empty()) {
      continue;
    }
    bool is_multicast = kDscpsByQueueName == kDscpsByMulticastQueueName;
    // Configue IPv4 and IPv6 traffic items to all queues under test.
    std::vector<std::string> traffic_items;
    absl::flat_hash_map<std::string, int64_t>
        buffer_config_by_traffic_item_name;
    for (auto &[queue_name, buffer_config] : kBufferParametersByQueueName) {
      // IPv4.
      {
        ASSERT_THAT(kDscpsByQueueName,
                    Contains(Pair(Eq(queue_name), Not(IsEmpty()))));
        int dscp = kDscpsByQueueName.at(queue_name).at(0);
        int config_value;
        switch (GetParam().config_to_be_tested) {
          case kSharedStaticLimit:
            config_value = *buffer_config.shared_static_limit;
            break;
          case kDedicatedBuffer:
            config_value = *buffer_config.dedicated_buffer;
            break;
          case kSharedAlpha:
          default:
            config_value = *buffer_config.dynamic_limit_scaling_factor;
        }
        std::string traffic_name = absl::StrFormat(
            "IPv4 packets with DSCP %d targeting queue '%s' with config %d",
            dscp, queue_name, config_value);
        ASSERT_OK_AND_ASSIGN(
            std::string traffic_item,
            ixia::SetUpTrafficItem(kIxiaIpv4SrcPortHandle, kIxiaDstPortHandle,
                                   traffic_name, *testbed));
        ASSERT_OK(ixia::SetTrafficParameters(
            traffic_item, is_multicast ?
            ixia::TrafficParameters{
                // Just send enough traffic to fill up buffer queues.
                .frame_count = 50000,
                .frame_size_in_bytes = kFrameSizeInBytes,
                .traffic_speed = kTrafficItemSpeed,
                .dst_mac = netaddr::MacAddress(1, 0, 0x5e, 0, 0, dscp + 1),
                .ip_parameters =
                    ixia::Ipv4TrafficParameters{
                        .dst_ipv4 = kIpv4McastAddresses[dscp],
                        .priority = ixia::IpPriority{.dscp = dscp},
                    },
            }
            :
            ixia::TrafficParameters{
                // Just send enough traffic to fill up buffer queues.
                .frame_count = 50000,
                .frame_size_in_bytes = kFrameSizeInBytes,
                .traffic_speed = kTrafficItemSpeed,
                .ip_parameters =
                    ixia::Ipv4TrafficParameters{
                        .priority = ixia::IpPriority{.dscp = dscp},
                    },
            },
            *testbed));
        traffic_items.push_back(traffic_item);
        buffer_config_by_traffic_item_name[traffic_name] = config_value;
      }
      // IPv6.
      {
        ASSERT_THAT(kDscpsByQueueName,
                    Contains(Pair(Eq(queue_name), Not(IsEmpty()))));
        int dscp = kDscpsByQueueName.at(queue_name).at(0);
        int config_value;
        switch (GetParam().config_to_be_tested) {
          case kSharedStaticLimit:
            config_value = *buffer_config.shared_static_limit;
            break;
          case kDedicatedBuffer:
            config_value = *buffer_config.dedicated_buffer;
            break;
          case kSharedAlpha:
          default:
            config_value = *buffer_config.dynamic_limit_scaling_factor;
        }
        std::string traffic_name = absl::StrFormat(
            "IPv6 packets with DSCP %d targeting queue '%s' with config %d",
            dscp, queue_name, config_value);
        ASSERT_OK_AND_ASSIGN(
            std::string traffic_item,
            ixia::SetUpTrafficItem(kIxiaIpv6SrcPortHandle, kIxiaDstPortHandle,
                                   traffic_name, *testbed));
        ASSERT_OK(ixia::SetTrafficParameters(
            traffic_item, is_multicast ?
            ixia::TrafficParameters{
                .frame_count = 100'000,
                .frame_size_in_bytes = kFrameSizeInBytes,
                .traffic_speed = kTrafficItemSpeed,
                .dst_mac = netaddr::MacAddress(0x33, 0x33, 0, 0, 0, dscp + 1),
                .ip_parameters =
                    ixia::Ipv6TrafficParameters{
                        .dst_ipv6 = kIpv6McastAddresses[dscp],
                        .priority = ixia::IpPriority{.dscp = dscp},
                    },
            }
            :
            ixia::TrafficParameters{
                .frame_count = 100'000,
                .frame_size_in_bytes = kFrameSizeInBytes,
                .traffic_speed = kTrafficItemSpeed,
                .ip_parameters =
                    ixia::Ipv6TrafficParameters{
                        .priority = ixia::IpPriority{.dscp = dscp},
                    },
            },
            *testbed));
        traffic_items.push_back(traffic_item);
        buffer_config_by_traffic_item_name[traffic_name] = config_value;
      }
    }

    if (GetParam().default_params.nsf_reboot) {
      ASSERT_OK(DoNsfRebootAndWaitForSwitchReadyOrRecover(
          testbed.get(), *GetParam().default_params.ssh_client_for_nsf));
    }
    Counters kInitialPortCounters;
    ASSERT_OK_AND_ASSIGN(kInitialPortCounters,
                         GetCountersForInterface(kSutEgressPort, *gnmi_stub));

    // Start traffic.
    LOG(INFO) << "starting traffic";
    ASSERT_OK(ixia::StartTraffic(traffic_items, kIxiaHandle, *testbed));

    LOG(INFO) << "traffic started -- sleeping for 5 seconds";
    absl::SleepFor(absl::Seconds(5));

    // Obtain traffic stats, and ensure traffic got forwarded according to
    // config.
    ASSERT_OK_AND_ASSIGN(const ixia::TrafficStats kTrafficStats,
                         ixia::GetAllTrafficItemStats(kIxiaHandle, *testbed));
    
    ASSERT_OK_AND_ASSIGN(Counters final_port_counters,
                         GetCountersForInterface(kSutEgressPort, *gnmi_stub));
    SCOPED_TRACE(absl::StrCat("port counters incremented by ",
                              final_port_counters - kInitialPortCounters));
    SCOPED_TRACE(absl::StrCat("Initial port counters: ", kInitialPortCounters));
    SCOPED_TRACE(absl::StrCat("Final port counters: ", final_port_counters));

    absl::flat_hash_map<int, int64_t> rx_frames_by_buffer_config;
    for (auto &[traffic_item_name, stats] :
         Ordered(kTrafficStats.stats_by_traffic_item())) {
      ASSERT_OK_AND_ASSIGN(
          int config, gutil::FindOrStatus(buffer_config_by_traffic_item_name,
                                          traffic_item_name));

      rx_frames_by_buffer_config[config] += stats.num_rx_frames();
      LOG(INFO) << "Traffic item : " << traffic_item_name
                << " Rx packets : " << stats.num_rx_frames();
    }

    int64_t lower_config_num_rx_frames = -1;
    int lower_config = -1;
    for (auto &[config, num_rx_frames] : Ordered(rx_frames_by_buffer_config)) {
      LOG(INFO) << "Config: " << absl::StrFormat("%2d", config)
                << " Num rx frames: " << num_rx_frames;
      EXPECT_GT(num_rx_frames, lower_config_num_rx_frames);
      if (GetParam().config_to_be_tested == kDedicatedBuffer &&
          lower_config_num_rx_frames != -1) {
        constexpr float kTolerance = 1.05;
        int dedicated_buffer_diff = config - lower_config;
        EXPECT_LE(num_rx_frames * kFrameSizeInBytes,
                  (lower_config_num_rx_frames * kFrameSizeInBytes +
                   dedicated_buffer_diff) *
                      kTolerance);
      }
      lower_config = config;
      lower_config_num_rx_frames = num_rx_frames;
    }
  }

  // Verify retrieval of per queue watermark statistics.
  absl::SleepFor(kMaxQueueCounterUpdateTime);
  for (auto &[queue_name, _] : kBufferParametersByQueueName) {
    ASSERT_OK_AND_ASSIGN(
        QueueCounters QueueCounters,
        GetGnmiQueueCounters(kSutEgressPort, queue_name, *gnmi_stub));
    LOG(INFO) << queue_name
              << " queue transmit: " << QueueCounters.num_packets_transmitted;
    LOG(INFO) << queue_name
              << " queue  drop: " << QueueCounters.num_packets_dropped;
    LOG(INFO) << queue_name
              << " queue max watermark: " << QueueCounters.max_queue_len;
    LOG(INFO) << queue_name << " queue periodic watermark: "
              << QueueCounters.max_periodic_queue_len;
  }
  LOG(INFO) << "---------------- Test done ---------------------";
}
}  // namespace pins_test
