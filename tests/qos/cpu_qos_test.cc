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

#include "tests/qos/cpu_qos_test.h"

#include <cstdint>
#include <memory>
#include <ostream>
#include <string>
#include <vector>

#include "absl/cleanup/cleanup.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/escaping.h"
#include "absl/strings/match.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/optional.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/collections.h"
#include "gutil/proto.h"
#include "gutil/proto_matchers.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "include/nlohmann/json.hpp"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/ixia_helper.h"
#include "lib/p4rt/packet_listener.h"
#include "lib/validator/validator_lib.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/netaddr/ipv4_address.h"
#include "p4_pdpi/netaddr/ipv6_address.h"
#include "p4_pdpi/netaddr/mac_address.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_pdpi/pd.h"
#include "p4_pdpi/string_encodings/decimal_string.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "tests/forwarding/util.h"
#include "thinkit/control_device.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/proto/generic_testbed.pb.h"
#include "thinkit/switch.h"

namespace pins_test {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::p4::config::v1::P4Info;

// Size of the "frame check sequence" (FCS) that is part of Layer 2 Ethernet
// frames.
constexpr int kFrameCheckSequenceSize = 4;

// The maximum time the switch is allowed to take before queue counters read via
// gNMI have to be incremented after a packet hits a queue.
// Empirically, for PINS, queue counters currently seem to get updated every
// 10 seconds.
constexpr absl::Duration kMaxQueueCounterUpdateTime = absl::Seconds(15);

struct QueueInfo {
  std::string gnmi_queue_name;      // Openconfig queue name.
  std::string p4_queue_name;        // P4 queue name.
  int rate_packets_per_second = 0;  // Rate of packets in packets per second.
};

// TODO: Parse QueueInfo from gNMI config.
absl::StatusOr<absl::flat_hash_map<std::string, QueueInfo>>
GetDefaultQueueInfo() {
  return absl::flat_hash_map<std::string, QueueInfo>{
      {"BE1", QueueInfo{"BE1", "0x2", 120}},
      {"AF1", QueueInfo{"AF1", "0x3", 120}},
      {"AF2", QueueInfo{"AF2", "0x4", 800}},
      {"AF3", QueueInfo{"AF3", "0x5", 120}},
      {"AF4", QueueInfo{"AF4", "0x6", 4000}},
      {"LLQ1", QueueInfo{"LLQ1", "0x0", 800}},
      {"LLQ2", QueueInfo{"LLQ2", "0x1", 800}},
      {"NC1", QueueInfo{"NC1", "0x7", 16000}},
  };
}

// Set up the switch to punt packets to CPU.
absl::Status SetUpPuntToCPU(const netaddr::MacAddress &dmac,
                            const netaddr::Ipv4Address &src_ip,
                            const netaddr::Ipv4Address &dst_ip,
                            absl::string_view p4_queue,
                            const p4::config::v1::P4Info &p4info,
                            pdpi::P4RuntimeSession &p4_session) {
  ASSIGN_OR_RETURN(auto ir_p4info, pdpi::CreateIrP4Info(p4info));
  RETURN_IF_ERROR(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      &p4_session,
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT, p4info))
      << "SetForwardingPipelineConfig: Failed to push P4Info: ";

  RETURN_IF_ERROR(pdpi::ClearTableEntries(&p4_session));
  auto acl_entry = gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
      R"pb(
        acl_ingress_table_entry {
          match {
            dst_mac { value: "$0" mask: "ff:ff:ff:ff:ff:ff" }
            is_ipv4 { value: "0x1" }
            src_ip { value: "$1" mask: "255.255.255.255" }
            dst_ip { value: "$2" mask: "255.255.255.255" }
          }
          action { trap { qos_queue: "$3" } }
          priority: 1
        }
      )pb",
      dmac.ToString(), src_ip.ToString(), dst_ip.ToString(), p4_queue));
  std::vector<p4::v1::TableEntry> pi_entries;
  ASSIGN_OR_RETURN(
      pi_entries.emplace_back(), pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, acl_entry),
      _.SetPrepend() << "Failed in PD table conversion to PI, entry: "
                     << acl_entry.DebugString() << " error: ");

  LOG(INFO) << "InstallPiTableEntries";
  return pdpi::InstallPiTableEntries(&p4_session, ir_p4info, pi_entries);
}

// These are the counters we track in these tests.
struct QueueCounters {
  int64_t num_packets_transmitted = 0;
  int64_t num_packet_dropped = 0;
};

std::ostream &operator<<(std::ostream &os, const QueueCounters &counters) {
  return os << absl::StreamFormat(
             "QueueCounters{"
             ".num_packets_transmitted = %d, "
             ".num_packets_dropped = %d"
             "}",
             counters.num_packets_transmitted, counters.num_packet_dropped);
}

// TODO: Move this to a helper library.
absl::StatusOr<QueueCounters> GetGnmiQueueCounters(
    absl::string_view port, absl::string_view queue,
    gnmi::gNMI::StubInterface &gnmi_stub) {
  QueueCounters counters;
  const std::string openconfig_transmit_count_state_path = absl::Substitute(
      "qos/interfaces/interface[interface-id=$0]"
      "/output/queues/queue[name=$1]/state/transmit-pkts",
      port, queue);

  ASSIGN_OR_RETURN(
      std::string transmit_counter_response,
      GetGnmiStatePathInfo(&gnmi_stub, openconfig_transmit_count_state_path,
                           "openconfig-qos:transmit-pkts"));

  if (!absl::SimpleAtoi(StripQuotes(transmit_counter_response),
                        &counters.num_packets_transmitted)) {
    return absl::InternalError(absl::StrCat("Unable to parse counter from ",
                                            transmit_counter_response));
  }

  const std::string openconfig_drop_count_state_path = absl::Substitute(
      "qos/interfaces/interface[interface-id=$0]"
      "/output/queues/queue[name=$1]/state/dropped-pkts",
      port, queue);

  ASSIGN_OR_RETURN(
      std::string drop_counter_response,
      GetGnmiStatePathInfo(&gnmi_stub, openconfig_drop_count_state_path,
                           "openconfig-qos:dropped-pkts"));

  if (!absl::SimpleAtoi(StripQuotes(drop_counter_response),
                        &counters.num_packet_dropped)) {
    return absl::InternalError(
        absl::StrCat("Unable to parse counter from ", drop_counter_response));
  }

  return counters;
}

// Returns the total number of packets enqueued for the queue with the given
// `QueueCounters`.
int64_t CumulativeNumPacketsEnqueued(const QueueCounters &counters) {
  return counters.num_packet_dropped + counters.num_packets_transmitted;
}

absl::Status SetPortSpeed(const std::string &port_speed,
                          const std::string &iface,
                          gnmi::gNMI::StubInterface &gnmi_stub) {
  std::string ops_config_path = absl::StrCat(
      "interfaces/interface[name=", iface, "]/ethernet/config/port-speed");
  std::string ops_val =
      absl::StrCat("{\"openconfig-if-ethernet:port-speed\":", port_speed, "}");
  RETURN_IF_ERROR(pins_test::SetGnmiConfigPath(&gnmi_stub, ops_config_path,
                                               GnmiSetType::kUpdate, ops_val));
  return absl::OkStatus();
}

absl::StatusOr<bool> CheckLinkUp(const std::string &iface,
                                 gnmi::gNMI::StubInterface &gnmi_stub) {
  std::string oper_status_state_path =
      absl::StrCat("interfaces/interface[name=", iface, "]/state/oper-status");
  std::string parse_str = "openconfig-interfaces:oper-status";
  ASSIGN_OR_RETURN(
      std::string ops_response,
      GetGnmiStatePathInfo(&gnmi_stub, oper_status_state_path, parse_str));
  return ops_response == "\"UP\"";
}

absl::StatusOr<packetlib::Packet> MakeIpv4PacketWithDscp(
    const netaddr::MacAddress &dst_mac, const netaddr::Ipv4Address &dst_ip,
    int dscp) {
  auto packet = gutil::ParseProtoOrDie<packetlib::Packet>(absl::Substitute(
      R"pb(
        headers {
          ethernet_header {
            ethernet_destination: "$0"
            ethernet_source: "00:01:02:03:04:05"
            ethertype: "0x0800"
          }
        }
        headers {
          ipv4_header {
            dscp: "$1"
            ecn: "0x0"
            identification: "0xa3cd"
            flags: "0x0"
            fragment_offset: "0x0000"
            ttl: "0x10"
            protocol: "0x05"
            ipv4_source: "10.0.0.2"
            ipv4_destination: "$2"
          }
        }
        payload: "Test packet to validate DSCP-to-queue mapping."
      )pb",
      dst_mac.ToString(), packetlib::IpDscp(dscp), dst_ip.ToString()));
  RETURN_IF_ERROR(packetlib::PadPacketToMinimumSize(packet).status());
  RETURN_IF_ERROR(packetlib::UpdateAllComputedFields(packet).status());
  return packet;
}

absl::StatusOr<packetlib::Packet> MakeIpv6PacketWithDscp(
    const netaddr::MacAddress &dst_mac, const netaddr::Ipv6Address &dst_ip,
    int dscp) {
  auto packet = gutil::ParseProtoOrDie<packetlib::Packet>(absl::Substitute(
      R"pb(
        headers {
          ethernet_header {
            ethernet_destination: "$0"
            ethernet_source: "00:01:02:03:04:05"
            ethertype: "0x86dd"
          }
        }
        headers {
          ipv6_header {
            dscp: "$1"
            ecn: "0x0"
            flow_label: "0x00000"
            next_header: "0xfd"  # Reserved for experimentation.
            hop_limit: "0x40"
            ipv6_source: "2001:db8:0:12::1"
            ipv6_destination: "$2"
          }
        }
        payload: "Test packet to validate DSCP-to-queue mapping."
      )pb",
      dst_mac.ToString(), packetlib::IpDscp(dscp), dst_ip.ToString()));
  RETURN_IF_ERROR(packetlib::PadPacketToMinimumSize(packet).status());
  RETURN_IF_ERROR(packetlib::UpdateAllComputedFields(packet).status());
  return packet;
}

absl::StatusOr<absl::flat_hash_map<int, std::string>>
ParseIpv4DscpToQueueMapping(absl::string_view gnmi_config) {
  // TODO: Actually parse config -- hard-coded for now.
  absl::flat_hash_map<int, std::string> queue_by_dscp;
  for (int dscp = 0; dscp < 64; ++dscp) queue_by_dscp[dscp] = "BE1";
  for (int dscp = 8; dscp <= 11; ++dscp) queue_by_dscp[dscp] = "AF1";
  queue_by_dscp[13] = "LLQ1";
  for (int dscp = 16; dscp <= 19; ++dscp) queue_by_dscp[dscp] = "AF2";
  queue_by_dscp[21] = "LLQ2";
  for (int dscp = 24; dscp <= 27; ++dscp) queue_by_dscp[dscp] = "AF3";
  for (int dscp = 32; dscp <= 35; ++dscp) queue_by_dscp[dscp] = "AF4";
  for (int dscp = 48; dscp <= 59; ++dscp) queue_by_dscp[dscp] = "NC1";
  return queue_by_dscp;
}

absl::StatusOr<absl::flat_hash_map<int, std::string>>
ParseIpv6DscpToQueueMapping(absl::string_view gnmi_config) {
  // TODO: Actually parse config -- hard-coded for now.
  return ParseIpv4DscpToQueueMapping(gnmi_config);
}

absl::StatusOr<std::optional<netaddr::Ipv4Address>> ParseLoopbackIpv4(
    absl::string_view gnmi_config) {
  // TODO: Actually parse IP -- hard-coded for now.
  return absl::nullopt;
}

absl::StatusOr<std::optional<netaddr::Ipv6Address>> ParseLoopbackIpv6(
    absl::string_view gnmi_config) {
  // TODO: Actually parse IP -- hard-coded for now.
  ASSIGN_OR_RETURN(auto ip,
                   netaddr::Ipv6Address::OfString("2607:f8b0:8096:3125::"));
  return ip;
}

// Represents a link connecting the switch under test (SUT) to a control device.
struct SutToControlLink {
  std::string sut_port_gnmi_name;
  std::string sut_port_p4rt_name;
  std::string control_device_port_gnmi_name;
  std::string control_device_port_p4rt_name;
};

std::ostream &operator<<(std::ostream &os, const SutToControlLink &link) {
  return os << absl::StreamFormat(
             "SutToControlLink{"
             ".sut_port_name = %s, .control_device_port_name = %s"
             "}",
             link.sut_port_gnmi_name, link.control_device_port_gnmi_name);
}
// Nondeterministically picks and returns a `SutToControlLink` that's up, or
// returns an error if no such port is found.
absl::StatusOr<SutToControlLink> PickSutToControlDeviceLinkThatsUp(
    thinkit::MirrorTestbed &testbed) {
  // TODO: Pick dynamically instead of hard-coding.
  return SutToControlLink{
      .sut_port_gnmi_name = "Ethernet28",
      .sut_port_p4rt_name = "516",
      .control_device_port_gnmi_name = "Ethernet28",
      .control_device_port_p4rt_name = "516",
  };
}

absl::StatusOr<p4::v1::TableEntry> MakeRouterInterface(
    absl::string_view router_interface_id, absl::string_view p4rt_port_name,
    const netaddr::MacAddress &mac, const pdpi::IrP4Info &ir_p4info) {
  ASSIGN_OR_RETURN(
      auto pd_entry,
      gutil::ParseTextProto<sai::TableEntry>(absl::Substitute(
          R"pb(
            router_interface_table_entry {
              match { router_interface_id: "$0" }
              action { set_port_and_src_mac { port: "$1" src_mac: "$2" } }
            }
          )pb",
          router_interface_id, p4rt_port_name, mac.ToString())));
  return pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, pd_entry);
}

// Purpose: Verify that P4Runtime per-entry ACL counters increment.
TEST_P(CpuQosTestWithoutIxia, PerEntryAclCounterIncrementsWhenEntryIsHit) {
  LOG(INFO) << "-- START OF TEST ---------------------------------------------";
  Testbed().Environment().SetTestCaseID("cfd7e8aa-6521-4683-9c07-038ea146934d");

  // Setup: the testbed consists of a SUT connected to a control device
  // that allows us to send and receive packets to/from the SUT.
  thinkit::Switch &sut = Testbed().Sut();
  thinkit::Switch &control_device = Testbed().ControlSwitch();
  const P4Info &p4info = GetParam().p4info;
  ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(p4info));

  // Set up gNMI.
  EXPECT_OK(Testbed().Environment().StoreTestArtifact("gnmi_config.json",
                                                      GetParam().gnmi_config));
  ASSERT_OK(pins_test::PushGnmiConfig(sut, GetParam().gnmi_config));
  ASSERT_OK(pins_test::PushGnmiConfig(control_device, GetParam().gnmi_config));
  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, sut.CreateGnmiStub());

  // TODO: Poll for config to be applied, links to come up instead.
  LOG(INFO) << "Sleeping 10 seconds to wait for config to be applied/links to "
               "come up.";
  absl::SleepFor(absl::Seconds(10));

  // Pick a link to be used for packet injection.
  ASSERT_OK_AND_ASSIGN(SutToControlLink link_used_for_test_packets,
                       PickSutToControlDeviceLinkThatsUp(Testbed()));
  LOG(INFO) << "Link used to inject test packets: "
            << link_used_for_test_packets;

  // Set up P4Runtime.
  EXPECT_OK(
      Testbed().Environment().StoreTestArtifact("p4info.textproto", p4info));
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt_session,
      pdpi::P4RuntimeSession::CreateWithP4InfoAndClearTables(sut, p4info));
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<pdpi::P4RuntimeSession> control_p4rt_session,
      pdpi::P4RuntimeSession::CreateWithP4InfoAndClearTables(control_device,
                                                             p4info));
  // We install a RIF to make this test non-trivial, as all packets are dropped
  // by default if no RIF exists (b/190736007).
  ASSERT_OK_AND_ASSIGN(
      p4::v1::TableEntry router_interface_entry,
      MakeRouterInterface(
          /*router_interface_id=*/"ingress-rif-to-workaround-b/190736007",
          /*p4rt_port_name=*/link_used_for_test_packets.sut_port_p4rt_name,
          // An arbitrary MAC address will do.
          /*mac=*/netaddr::MacAddress(0x00, 0x07, 0xE9, 0x42, 0xAC, 0x28),
          /*ir_p4info=*/ir_p4info));
  ASSERT_OK(pdpi::InstallPiTableEntry(sut_p4rt_session.get(),
                                      router_interface_entry));

  // Install ACL table entry to be hit with a test packet.
  ASSERT_OK_AND_ASSIGN(const sai::TableEntry pd_acl_entry,
                       gutil::ParseTextProto<sai::TableEntry>(R"pb(
                         acl_ingress_table_entry {
                           priority: 1
                           match {
                             is_ipv6 { value: "0x1" }
                             ttl { value: "0xff" mask: "0xff" }
                           }
                           action { acl_drop {} }
                         }
                       )pb"));
  ASSERT_OK_AND_ASSIGN(const p4::v1::TableEntry pi_acl_entry,
                       pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, pd_acl_entry));
  ASSERT_OK(pdpi::InstallPiTableEntry(sut_p4rt_session.get(), pi_acl_entry));

  // Check that the counters are initially zero.
  ASSERT_THAT(
      pdpi::ReadPiCounterData(sut_p4rt_session.get(), pi_acl_entry),
      IsOkAndHolds(EqualsProto(R"pb(byte_count: 0 packet_count: 0)pb")));

  // Send test packet hitting the ACL table entry.
  ASSERT_OK_AND_ASSIGN(
      packetlib::Packet test_packet,
      gutil::ParseTextProto<packetlib::Packet>(R"pb(
        headers {
          ethernet_header {
            ethernet_destination: "00:01:02:02:02:02"
            ethernet_source: "00:01:02:03:04:05"
            ethertype: "0x86dd"
          }
        }
        headers {
          ipv6_header {
            dscp: "0x00"
            ecn: "0x0"
            flow_label: "0x00000"
            next_header: "0xfd"  # Reserved for experimentation.
            hop_limit: "0xff"
            ipv6_source: "2001:db8:0:12::1"
            ipv6_destination: "2001:db8:0:12::2"
          }
        }
        payload: "IPv6 packet with TTL 0xff (255)."
      )pb"));
  // The ACL entry should match the test packet.
  ASSERT_EQ(test_packet.headers().at(1).ipv6_header().hop_limit(),
            pd_acl_entry.acl_ingress_table_entry().match().ttl().value());
  ASSERT_OK(packetlib::PadPacketToMinimumSize(test_packet));
  ASSERT_OK(packetlib::UpdateAllComputedFields(test_packet));
  ASSERT_OK_AND_ASSIGN(const std::string raw_packet,
                       packetlib::SerializePacket(test_packet));
  ASSERT_OK(pins::InjectEgressPacket(
      /*port=*/link_used_for_test_packets.control_device_port_p4rt_name,
      /*packet=*/raw_packet, ir_p4info, control_p4rt_session.get()));

  // Check that the counters increment within kMaxQueueCounterUpdateTime.
  absl::Time time_packet_sent = absl::Now();
  p4::v1::CounterData counter_data;
  do {
    ASSERT_OK_AND_ASSIGN(
        counter_data,
        pdpi::ReadPiCounterData(sut_p4rt_session.get(), pi_acl_entry));
  } while (counter_data.packet_count() == 0 &&
           absl::Now() - time_packet_sent < kMaxQueueCounterUpdateTime);
  p4::v1::CounterData expected_counter_data;
  expected_counter_data.set_packet_count(1);
  expected_counter_data.set_byte_count(raw_packet.size() +
                                       kFrameCheckSequenceSize);
  ASSERT_THAT(counter_data, EqualsProto(expected_counter_data))
      << "Counter for the table entry given below did not match expectation "
         "within "
      << kMaxQueueCounterUpdateTime
      << " after injecting the following test packet:\n-- test packet--\n"
      << test_packet.DebugString() << "-- table entry --\n"
      << pd_acl_entry.DebugString();

  LOG(INFO) << "-- END OF TEST -----------------------------------------------";
}

// Purpose: Verify DSCP-to-queue mapping for traffic to switch loopback IP.
TEST_P(CpuQosTestWithoutIxia, TrafficToLoopackIpGetsMappedToCorrectQueues) {
  LOG(INFO) << "-- START OF TEST ---------------------------------------------";
  Testbed().Environment().SetTestCaseID("61bb0173-0c49-4067-b15a-5c3dd7823126");

  // Setup: the testbed consists of a SUT connected to a control device
  // that allows us to send and receive packets to/from the SUT.
  thinkit::Switch &sut = Testbed().Sut();
  thinkit::Switch &control_device = Testbed().ControlSwitch();
  constexpr auto kSutMacAddress =
      netaddr::MacAddress(0x00, 0x07, 0xE9, 0x42, 0xAC, 0x28);  // Arbitrary.
  const P4Info &p4info = GetParam().p4info;
  ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(p4info));

  // Set up gNMI.
  EXPECT_OK(Testbed().Environment().StoreTestArtifact("gnmi_config.json",
                                                      GetParam().gnmi_config));
  ASSERT_OK(pins_test::PushGnmiConfig(sut, GetParam().gnmi_config));
  ASSERT_OK(pins_test::PushGnmiConfig(control_device, GetParam().gnmi_config));
  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, sut.CreateGnmiStub());
  // TODO: Poll for config to be applied, links to come up instead.
  LOG(INFO) << "Sleeping 10 seconds to wait for config to be applied/links to "
               "come up.";
  absl::SleepFor(absl::Seconds(10));

  // Pick a link to be used for packet injection.
  ASSERT_OK_AND_ASSIGN(SutToControlLink link_used_for_test_packets,
                       PickSutToControlDeviceLinkThatsUp(Testbed()));
  LOG(INFO) << "Link used to inject test packets: "
            << link_used_for_test_packets;

  // Set up P4Runtime.
  EXPECT_OK(
      Testbed().Environment().StoreTestArtifact("p4info.textproto", p4info));
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<pdpi::P4RuntimeSession> p4rt_session,
      pdpi::P4RuntimeSession::CreateWithP4InfoAndClearTables(sut, p4info));
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<pdpi::P4RuntimeSession> control_p4rt_session,
      pdpi::P4RuntimeSession::CreateWithP4InfoAndClearTables(control_device,
                                                             p4info));
  // TODO: Unless a RIF exists at the test packet ingress port,
  // packets will be dropped. Remove this once these RIFs are set up via gNMI.
  if (Testbed().Environment().MaskKnownFailures()) {
    ASSERT_OK_AND_ASSIGN(
        p4::v1::TableEntry router_interface_entry,
        MakeRouterInterface(
            /*router_interface_id=*/"ingress-rif-to-workaround-b/190736007",
            /*p4rt_port_name=*/link_used_for_test_packets.sut_port_p4rt_name,
            /*mac=*/kSutMacAddress,
            /*ir_p4info=*/ir_p4info));
    ASSERT_OK(
        pdpi::InstallPiTableEntry(p4rt_session.get(), router_interface_entry));
  }

  // Extract DSCP-to-queue mapping from gNMI config.
  using QueueNameByDscp = absl::flat_hash_map<int, std::string>;
  ASSERT_OK_AND_ASSIGN(std::optional<QueueNameByDscp> queue_name_by_ipv4_dscp,
                       ParseIpv4DscpToQueueMapping(GetParam().gnmi_config));
  ASSERT_OK_AND_ASSIGN(std::optional<QueueNameByDscp> queue_name_by_ipv6_dscp,
                       ParseIpv6DscpToQueueMapping(GetParam().gnmi_config));
  const std::string kDefaultQueueName = "BE1";

  // Extract loopback IPs from gNMI config.
  ASSERT_OK_AND_ASSIGN(std::optional<netaddr::Ipv4Address> loopback_ipv4,
                       ParseLoopbackIpv4(GetParam().gnmi_config));
  ASSERT_OK_AND_ASSIGN(std::optional<netaddr::Ipv6Address> loopback_ipv6,
                       ParseLoopbackIpv6(GetParam().gnmi_config));
  ASSERT_TRUE(loopback_ipv4.has_value() || loopback_ipv6.has_value())
      << "Expected a loopback IP to be configured via gNMI; nothing to test.";

  // Verify DSCP-to-queue mapping for all DSCPs using IP test packets destined
  // to the loopback IP(s).
  constexpr int kMaxDscp = 63;
  for (int dscp = 0; dscp <= kMaxDscp; ++dscp) {
    for (bool ipv4 : {true, false}) {
      if (ipv4 && !loopback_ipv4.has_value()) continue;
      if (!ipv4 && !loopback_ipv6.has_value()) continue;
      LOG(INFO) << "Testing DSCP-to-queue mapping for "
                << (ipv4 ? "IPv4" : "IPv6") << " packet with DSCP " << dscp;

      // Identify target queue for current DSCP.
      // The algorithm for picking a queue is somewhat adhoc and PINS specific.
      std::string target_queue = kDefaultQueueName;
      if (queue_name_by_ipv4_dscp.has_value()) {
        target_queue = gutil::FindOrDefault(*queue_name_by_ipv4_dscp, dscp,
                                            kDefaultQueueName);
      } else if (queue_name_by_ipv6_dscp.has_value()) {
        target_queue = gutil::FindOrDefault(*queue_name_by_ipv6_dscp, dscp,
                                            kDefaultQueueName);
      }
      LOG(INFO) << "Target queue: " << target_queue;

      // Read counters of the target queue.
      ASSERT_OK_AND_ASSIGN(
          const QueueCounters queue_counters_before_test_packet,
          GetGnmiQueueCounters(/*port=*/"CPU", /*queue=*/target_queue,
                               *gnmi_stub));

      // Inject test packet.
      ASSERT_OK_AND_ASSIGN(
          packetlib::Packet packet,
          ipv4
              ? MakeIpv4PacketWithDscp(/*dst_mac=*/kSutMacAddress,
                                       /*dst_ip=*/*loopback_ipv4, /*dscp=*/dscp)
              : MakeIpv6PacketWithDscp(/*dst_mac=*/kSutMacAddress,
                                       /*dst_ip=*/*loopback_ipv6,
                                       /*dscp=*/dscp));
      ASSERT_OK_AND_ASSIGN(std::string raw_packet,
                           packetlib::SerializePacket(packet));
      ASSERT_OK(pins::InjectEgressPacket(
          /*port=*/link_used_for_test_packets.control_device_port_p4rt_name,
          /*packet=*/raw_packet, ir_p4info, control_p4rt_session.get()));

      // Read counter of the target queue again.
      absl::Time time_packet_sent = absl::Now();
      QueueCounters queue_counters_after_test_packet;
      do {
        ASSERT_OK_AND_ASSIGN(
            queue_counters_after_test_packet,
            GetGnmiQueueCounters(/*port=*/"CPU", /*queue=*/target_queue,
                                 *gnmi_stub));
      } while (
          // It may take several seconds for the queue counters to update.
          CumulativeNumPacketsEnqueued(queue_counters_after_test_packet) ==
              CumulativeNumPacketsEnqueued(queue_counters_before_test_packet) &&
          absl::Now() - time_packet_sent < kMaxQueueCounterUpdateTime);

      EXPECT_EQ(
          CumulativeNumPacketsEnqueued(queue_counters_after_test_packet),
          CumulativeNumPacketsEnqueued(queue_counters_before_test_packet) + 1)
          << "expected counter to increment for queue '" << target_queue
          << "' targeted by the following test packet:\n"
          << packet.DebugString()
          << "\nBefore: " << queue_counters_before_test_packet
          << "\nAfter : " << queue_counters_after_test_packet;
    }
  }
  LOG(INFO) << "-- END OF TEST -----------------------------------------------";
}

TEST_P(CpuQosTestWithIxia, TestCPUQueueRateLimit) {
  // Pick a testbed with an Ixia Traffic Generator.
  auto requirements =
      gutil::ParseProtoOrDie<thinkit::TestRequirements>(
          R"pb(interface_requirements {
                 count: 1
                 interface_mode: TRAFFIC_GENERATOR
               })pb");

  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<thinkit::GenericTestbed> generic_testbed,
      GetParam().testbed_interface->GetTestbedWithRequirements(requirements));

  ASSERT_OK(generic_testbed->Environment().StoreTestArtifact(
      "gnmi_config.txt", GetParam().gnmi_config));

  thinkit::Switch& sut = generic_testbed->Sut();

  // Connect to TestTracker for test status.
  if (auto &id = GetParam().test_case_id; id.has_value()) {
    generic_testbed->Environment().SetTestCaseID(*id);
  }

  // Push GNMI config.
  ASSERT_OK(pins_test::PushGnmiConfig(sut, GetParam().gnmi_config));

  // Hook up to GNMI.
  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, sut.CreateGnmiStub());

  // Get Queues
  // TODO: Extract Queue info from config instead of hardcoded
  // default.
  ASSERT_OK_AND_ASSIGN(auto queues, GetDefaultQueueInfo());

  // Set up P4Runtime session.
  // TODO: Use `CreateWithP4InfoAndClearTables` cl/397193959 when
  // its available.
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<pdpi::P4RuntimeSession> sut_p4_session,
                       pdpi::P4RuntimeSession::Create(generic_testbed->Sut()));
  auto clear_table_entries = absl::Cleanup(
      [&]() { ASSERT_OK(pdpi::ClearTableEntries(sut_p4_session.get())); });

  // Flow details.
  const auto dest_mac = netaddr::MacAddress(02, 02, 02, 02, 02, 02);
  const auto source_mac = netaddr::MacAddress(00, 01, 02, 03, 04, 05);
  const auto source_ip = netaddr::Ipv4Address(192, 168, 10, 1);
  const auto dest_ip = netaddr::Ipv4Address(172, 0, 0, 1);

  // BE1 is guaranteed to exist in the map which is currently hardocoded
  // and we will test for BE1 queue.
  // TODO: When we replace hardcoding with extraction of members
  // from the config, we need to add iteration logic to go over the configured
  // queues.
  QueueInfo queue_under_test = queues["BE1"];

  ASSERT_OK(SetUpPuntToCPU(dest_mac, source_ip, dest_ip,
                           queue_under_test.p4_queue_name, GetParam().p4info,
                           *sut_p4_session));

  static constexpr absl::Duration kPollInterval = absl::Seconds(5);
  static constexpr absl::Duration kTotalTime = absl::Seconds(30);
  static const int kIterations = kTotalTime / kPollInterval;

  QueueCounters final_counters;
  QueueCounters delta_counters;
  // Check for counters every 5 seconds upto 30 seconds till they match.
  for (int gnmi_counters_check = 0; gnmi_counters_check < kIterations;
       gnmi_counters_check++) {
    absl::SleepFor(kPollInterval);

    ASSERT_OK_AND_ASSIGN(
        final_counters,
        GetGnmiQueueCounters("CPU", queue_under_test.gnmi_queue_name,
                             *gnmi_stub));
  }
}

}  // namespace
}  // namespace pins_test
