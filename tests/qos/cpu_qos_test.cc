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
#include <variant>
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
#include "absl/synchronization/mutex.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/optional.h"
#include "absl/types/variant.h"
#include "glog/logging.h"
#include "google/protobuf/util/json_util.h"
#include "gutil/collections.h"
#include "gutil/overload.h"
#include "gutil/proto.h"
#include "gutil/proto_matchers.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "include/nlohmann/json.hpp"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/gnmi/openconfig.pb.h"
#include "lib/ixia_helper.h"
#include "lib/p4rt/packet_listener.h"
#include "lib/validator/validator_lib.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/netaddr/ipv4_address.h"
#include "p4_pdpi/netaddr/ipv6_address.h"
#include "p4_pdpi/netaddr/mac_address.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_pdpi/pd.h"
#include "p4_pdpi/string_encodings/decimal_string.h"
#include "proto/gnmi/gnmi.pb.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "tests/forwarding/util.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "tests/qos/gnmi_parsers.h"
#include "tests/qos/packet_in_receiver.h"
#include "tests/qos/qos_test_util.h"
#include "tests/sflow/sflow_util.h"
#include "thinkit/control_device.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/proto/generic_testbed.pb.h"
#include "thinkit/switch.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace pins_test {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::p4::config::v1::P4Info;
using ::testing::Contains;
using ::testing::Not;

// Size of the "frame check sequence" (FCS) that is part of Layer 2 Ethernet
// frames.
constexpr int kFrameCheckSequenceSize = 4;

// After pushing gNMI config to a switch, the tests sleep for this duration
// assuming that the gNMI config will have been fully applied afterwards.
// TODO: Instead of hard-coding this time, tests should dynamically
// poll the state of the switch to ensure config has been applied.
constexpr absl::Duration kTimeToWaitForGnmiConfigToApply = absl::Seconds(30);

struct QueueInfo {
  std::string gnmi_queue_name;      // Openconfig queue name.
  std::string p4_queue_name;        // P4 queue name.
  int rate_packets_per_second = 0;  // Rate of packets in packets per second.
};

// Extract the queue configurations from the gNMI configuration.
// The function returns a map keyed on queue name and value
// holds queue configuration information.
// TODO: Need to handle exceptions cleanly for failures
// during json parsing which can crash the test run.
// Currently we are assuming validity of config json parameter passed into
// the test.
absl::StatusOr<absl::flat_hash_map<std::string, QueueInfo>>
ExtractQueueInfoViaGnmiConfig(absl::string_view gnmi_config) {
  nlohmann::json config = nlohmann::json::parse(gnmi_config);
  if (!config.is_object()) {
    return absl::InvalidArgumentError("Could not parse gnmi configuration.");
  }

  absl::flat_hash_map<std::string, QueueInfo> queue_info_by_queue_name;
  auto &qos_interfaces =
      config["openconfig-qos:qos"]["interfaces"]["interface"];

  std::string cpu_scheduler_policy;
  for (auto &interface : qos_interfaces) {
    if (interface["interface-id"].get<std::string>() == "CPU") {
      cpu_scheduler_policy =
          interface["output"]["scheduler-policy"]["config"]["name"]
              .get<std::string>();
      break;
    }
  }

  auto &scheduler_policies =
      config["openconfig-qos:qos"]["scheduler-policies"]["scheduler-policy"];
  for (auto &policy : scheduler_policies) {
    if (policy["name"].get<std::string>() == cpu_scheduler_policy) {
      for (auto &scheduler : policy["schedulers"]["scheduler"]) {
        std::string queue_name =
            scheduler["inputs"]["input"][0]["config"]["queue"]
                .get<std::string>();
        queue_info_by_queue_name[queue_name].gnmi_queue_name = queue_name;
        std::string peak_rate = scheduler["two-rate-three-color"]["config"]
                                         ["google-pins-qos:pir-pkts"]
                                             .get<std::string>();
        if (!absl::SimpleAtoi(peak_rate, &queue_info_by_queue_name[queue_name]
                                              .rate_packets_per_second)) {
          return absl::InternalError(
              absl::StrCat("Unable to parse rate as int ", peak_rate,
                           " for queue ", queue_name));
        }
        LOG(INFO) << "Queue: " << queue_name
                  << ", configured rate:" << peak_rate;
      }
      break;
    }
  }

  // TODO: Remove these once P4 uses gnmi queue names
  queue_info_by_queue_name["BE1"].p4_queue_name = "0x2";
  queue_info_by_queue_name["AF1"].p4_queue_name = "0x3";
  queue_info_by_queue_name["AF2"].p4_queue_name = "0x4";
  queue_info_by_queue_name["AF3"].p4_queue_name = "0x5";
  queue_info_by_queue_name["AF4"].p4_queue_name = "0x6";
  queue_info_by_queue_name["LLQ1"].p4_queue_name = "0x0";
  queue_info_by_queue_name["LLQ2"].p4_queue_name = "0x1";
  queue_info_by_queue_name["NC1"].p4_queue_name = "0x7";

  return queue_info_by_queue_name;
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
          action { acl_trap { qos_queue: "$3" } }
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

// Set up the switch to punt packets to CPU.
absl::Status SetUpV6PuntToCPU(const netaddr::MacAddress &dmac,
                              const netaddr::Ipv6Address &src_ip,
                              const netaddr::Ipv6Address &dst_ip,
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
            is_ipv6 { value: "0x1" }
          }
          action { acl_trap { qos_queue: "$1" } }
          priority: 1
        }
      )pb",
      dmac.ToString(), p4_queue));
  std::vector<p4::v1::TableEntry> pi_entries;
  ASSIGN_OR_RETURN(
      pi_entries.emplace_back(),
      pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, acl_entry),
      _.SetPrepend() << "Failed in PD table conversion to PI, entry: "
                     << acl_entry.DebugString() << " error: ");

  LOG(INFO) << "InstallPiTableEntries";
  return pdpi::InstallPiTableEntries(&p4_session, ir_p4info, pi_entries);
}

// Set up the switch to punt packets to CPU with meter.
// Returns a copy of installed Punt Entry or QoS Entry.
absl::StatusOr<p4::v1::TableEntry> SetUpPuntToCPUWithRateLimit(
    const netaddr::MacAddress &dmac, const netaddr::Ipv4Address &dst_ip,
    absl::string_view p4_queue, int rate_bytes_per_second, int burst_in_bytes,
    const p4::config::v1::P4Info &p4info, pdpi::P4RuntimeSession &p4_session) {
  ASSIGN_OR_RETURN(auto ir_p4info, pdpi::CreateIrP4Info(p4info));

  RETURN_IF_ERROR(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      &p4_session,
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT, p4info))
      << "SetForwardingPipelineConfig: Failed to push P4Info: ";

  RETURN_IF_ERROR(pdpi::ClearTableEntries(&p4_session));

  // There can be 2 schemes for punting depending on
  // pipeline.
  // If p4 info table has the "acl_ingress_qos_table" configured, then
  //     1. Punt the packets using "acl_ingress_table" entry.
  //     2. Rate limit the packets using a "acl_ingress_qos_table" entry, which
  //        allows capability to apply policer on a group of punt entries.
  // else
  //     Punt and Rate limit packets in same entry in "acl_ingress_table"
  if (ir_p4info.tables_by_name().contains("acl_ingress_qos_table")) {
    auto punt_entry = gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
        R"pb(
          acl_ingress_table_entry {
            match {
              dst_mac { value: "$0" mask: "ff:ff:ff:ff:ff:ff" }
              is_ipv4 { value: "0x1" }
              dst_ip { value: "$1" mask: "255.255.255.255" }
            }
            action { acl_trap { qos_queue: "$2" } }
            priority: 1
          }
        )pb",
        dmac.ToString(), dst_ip.ToString(), p4_queue));

    LOG(INFO) << "InstallPiTableEntry";
    ASSIGN_OR_RETURN(
        const p4::v1::TableEntry pi_acl_entry,
        pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, punt_entry));
    RETURN_IF_ERROR(pdpi::InstallPiTableEntry(&p4_session, pi_acl_entry));

    auto qos_entry = gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
        R"pb(
          acl_ingress_qos_table_entry {
            match {
              dst_mac { value: "$0" mask: "ff:ff:ff:ff:ff:ff" }
              is_ipv4 { value: "0x1" }
            }
            action {
              set_qos_queue_and_cancel_copy_above_rate_limit { qos_queue: "$1" }
            }
            priority: 4400
            meter_config { bytes_per_second: $2 burst_bytes: $3 }
          }
        )pb",
        dmac.ToString(), p4_queue, rate_bytes_per_second, burst_in_bytes));

    LOG(INFO) << "InstallPiTableEntry";
    ASSIGN_OR_RETURN(
        const p4::v1::TableEntry pi_acl_qos_entry,
        pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, qos_entry));
    RETURN_IF_ERROR(pdpi::InstallPiTableEntry(&p4_session, pi_acl_qos_entry));

    return pi_acl_qos_entry;
  } else {
    auto acl_entry = gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
        R"pb(
          acl_ingress_table_entry {
            match {
              dst_mac { value: "$0" mask: "ff:ff:ff:ff:ff:ff" }
              is_ipv4 { value: "0x1" }
              dst_ip { value: "$1" mask: "255.255.255.255" }
            }
            action { acl_trap { qos_queue: "$2" } }
            priority: 1
            meter_config { bytes_per_second: $3 burst_bytes: $4 }
          }
        )pb",
        dmac.ToString(), dst_ip.ToString(), p4_queue, rate_bytes_per_second,
        burst_in_bytes));

    LOG(INFO) << "InstallPiTableEntry";
    ASSIGN_OR_RETURN(
        const p4::v1::TableEntry pi_acl_entry,
        pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, acl_entry));
    RETURN_IF_ERROR(pdpi::InstallPiTableEntry(&p4_session, pi_acl_entry));
    return pi_acl_entry;
  }
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
      .sut_port_gnmi_name = "Ethernet1/1/1",
      .sut_port_p4rt_name = "1",
      .control_device_port_gnmi_name = "Ethernet1/1/1",
      .control_device_port_p4rt_name = "1",
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

  // Setup: the testbed consists of a SUT connected to a control device
  // that allows us to send and receive packets to/from the SUT.
  thinkit::Switch &sut = Testbed().Sut();
  thinkit::Switch &control_device = Testbed().ControlSwitch();
  const P4Info &p4info = GetParam().p4info;
  ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(p4info));

  // Configure mirror testbed.
  EXPECT_OK(
      Testbed().Environment().StoreTestArtifact("p4info.textproto", p4info));
  std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt_session,
      control_p4rt_session;
  ASSERT_OK_AND_ASSIGN(
      std::tie(sut_p4rt_session, control_p4rt_session),
      pins_test::ConfigureSwitchPairAndReturnP4RuntimeSessionPair(
          sut, control_device, GetParam().gnmi_config, p4info));

  // Store gNMI config for debugging purposes.
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(std::string sut_gnmi_config,
                       pins_test::GetGnmiConfig(*sut_gnmi_stub));
  EXPECT_OK(Testbed().Environment().StoreTestArtifact("sut_gnmi_config.json",
                                                      sut_gnmi_config));

  // Pick a link to be used for packet injection.
  ASSERT_OK_AND_ASSIGN(SutToControlLink link_used_for_test_packets,
                       PickSutToControlDeviceLinkThatsUp(Testbed()));
  LOG(INFO) << "Link used to inject test packets: "
            << link_used_for_test_packets;

  // Install ACL table entry to be hit with a test packet.
  ASSERT_OK_AND_ASSIGN(const sai::TableEntry pd_acl_entry,
                       gutil::ParseTextProto<sai::TableEntry>(R"pb(
                         acl_ingress_table_entry {
                           priority: 1
                           match {
                             is_ipv6 { value: "0x1" }
                             ip_protocol { value: "0xfd" mask: "0xff" }
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
        payload: "IPv6 packet with next header 0xfd (253)."
      )pb"));
  // The ACL entry should match the test packet.
  ASSERT_EQ(
      test_packet.headers().at(1).ipv6_header().next_header(),
      pd_acl_entry.acl_ingress_table_entry().match().ip_protocol().value());

  ASSERT_OK(packetlib::PadPacketToMinimumSize(test_packet));
  ASSERT_OK(packetlib::UpdateAllComputedFields(test_packet));
  ASSERT_OK_AND_ASSIGN(const std::string raw_packet,
                       packetlib::SerializePacket(test_packet));
  ASSERT_OK(pins::InjectEgressPacket(
      /*port=*/link_used_for_test_packets.control_device_port_p4rt_name,
      /*packet=*/raw_packet, ir_p4info, control_p4rt_session.get(),
      /*packet_delay=*/std::nullopt));

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

// Returns vector of packets for which we will test that the packet does not
// reach the CPU (when we haven't explicitly configure the switch otherwise).
absl::StatusOr<std::vector<packetlib::Packet>>
TestPacketsThatShouldNotGetPunted() {
  std::vector<packetlib::Packet> packets;

  // IPv4/6 packets with low TTLs.
  // TODO: TTL 0/1 packets currently *do* make it to the CPU by
  // default on some of our targets, so we exclude them here for now.
  for (int ttl : {/*0, 1,*/ 2, 3}) {
    ASSIGN_OR_RETURN(packets.emplace_back(),
                     gutil::ParseTextProto<packetlib::Packet>(absl::Substitute(
                         R"pb(
                           headers {
                             ethernet_header {
                               ethernet_destination: "00:01:02:02:02:02"
                               ethernet_source: "00:01:02:03:04:05"
                               ethertype: "0x0800"
                             }
                           }
                           headers {
                             ipv4_header {
                               dscp: "0x00"
                               ecn: "0x0"
                               identification: "0xa3cd"
                               flags: "0x0"
                               fragment_offset: "0x0000"
                               ttl: "$0"
                               protocol: "0x05"
                               ipv4_source: "10.0.0.2"
                               ipv4_destination: "10.0.0.3"
                             }
                           }
                           payload: "IPv4 packet with TTL $0."
                         )pb",
                         packetlib::IpTtl(ttl))));
    ASSIGN_OR_RETURN(
        packets.emplace_back(),
        gutil::ParseTextProto<packetlib::Packet>(absl::Substitute(
            R"pb(
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
                  hop_limit: "$0"
                  ipv6_source: "2001:db8:0:12::1"
                  ipv6_destination: "2001:db8:0:12::2"
                }
              }
              payload: "IPv6 packet with TTL $0."
            )pb",
            packetlib::IpTtl(ttl))));
  }

  // Ethernet broadcast packets (destination MAC ff:ff:ff:ff:ff:ff).
  ASSIGN_OR_RETURN(
      packets.emplace_back(),
      gutil::ParseTextProto<packetlib::Packet>(
          R"pb(
            headers {
              ethernet_header {
                ethernet_destination: "ff:ff:ff:ff:ff:ff"
                ethernet_source: "00:01:02:03:04:05"
                # This means size(payload) = 0xff bytes = 255 bytes.
                ethertype: "0x00ff"
              }
            }
            payload: "Ethernet broadcast packet."
          )pb"));
  ASSIGN_OR_RETURN(packets.emplace_back(),
                   gutil::ParseTextProto<packetlib::Packet>(
                       R"pb(
                         headers {
                           ethernet_header {
                             ethernet_destination: "ff:ff:ff:ff:ff:ff"
                             ethernet_source: "00:11:22:33:44:55"
                             ethertype: "0x0806"
                           }
                         }
                         headers {
                           arp_header {
                             hardware_type: "0x0001"
                             protocol_type: "0x0800"
                             hardware_length: "0x06"
                             protocol_length: "0x04"
                             operation: "0x0001"
                             sender_hardware_address: "00:11:22:33:44:55"
                             sender_protocol_address: "10.0.0.1"
                             target_hardware_address: "00:00:00:00:00:00"
                             target_protocol_address: "10.0.0.2"
                           }
                         }
                         payload: "ARP broadcast packet."
                       )pb"));

  // LLDP multicast packet.
  // TODO: If packetlib starts supporting LLDP, we can replace this
  // LLDP packet hex dump with a readable protobuf. For now, we can verify that
  // this is indeed a valid LLDP packet using, e.g., https://hpd.gasmi.net/.
  static constexpr absl::string_view kLldpPacketHexDump =
      "0180c200000ef40304321f6688cc02070402320af046030404073235330602007808266a"
      "753166326d3168342e6d747631352e6e65742e676f6f676c652e636f6d3a62702d342f36"
      "31100c05010af0460302000000fd000a1e6a753166326d3168342e6d747631352e6e6574"
      "2e676f6f676c652e636f6dfe0c001a11041666534220c811b3fe05001a1105920000";
  packetlib::Packet packet =
      packetlib::ParsePacket(absl::HexStringToBytes(kLldpPacketHexDump));
  if (packet.headers_size() < 1 || !packet.headers(0).has_ethernet_header()) {
    return gutil::InternalErrorBuilder();
  }
  packet.mutable_headers(0)
      ->mutable_ethernet_header()
      ->set_ethernet_destination("01:80:C2:00:00:0E");  // LLDP multicast.
  packets.push_back(packet);

  // Post-process packets to ensure they are valid.
  for (auto &packet : packets) {
    RETURN_IF_ERROR(packetlib::PadPacketToMinimumSize(packet).status());
    RETURN_IF_ERROR(packetlib::UpdateAllComputedFields(packet).status());
  }
  return packets;
}

// Queries via gNMI, parses, and returns as a proto the gNMI path
// `qos/interfaces/interface[interface-id=CPU]/output/queues`, which contains
// the state of all CPU queue counters.
absl::StatusOr<openconfig::QueuesByName> GetCpuQueueStateViaGnmi(
    gnmi::gNMI::StubInterface &gnmi_stub) {
  ASSIGN_OR_RETURN(
      std::string queues_json,
      GetGnmiStatePathInfo(
          &gnmi_stub,
          "qos/interfaces/interface[interface-id=CPU]/output/queues",
          "openconfig-qos:queues"));

  google::protobuf::util::JsonParseOptions options;
  options.ignore_unknown_fields = true;
  openconfig::Queues queues_proto;
  RETURN_IF_ERROR(
      gutil::ToAbslStatus(google::protobuf::util::JsonStringToMessage(
          queues_json, &queues_proto, options)));

  // Convert `Queues` to `QueuesByName`, which is equivalent but more convenient
  // for diffing.
  openconfig::QueuesByName queues_by_name;
  for (auto &queue : queues_proto.queues()) {
    queues_by_name.mutable_queues()->insert({queue.name(), queue.state()});
  }

  return queues_by_name;
}

// Purpose: Verify that the CPU is protected from packets by default.
TEST_P(CpuQosTestWithoutIxia,
       NoUnexpectedPacketsReachCpuInPristineSwitchState) {
  LOG(INFO) << "-- START OF TEST ---------------------------------------------";

  // Setup: the testbed consists of a SUT connected to a control device
  // that allows us to send and receive packets to/from the SUT.
  thinkit::Switch &sut = Testbed().Sut();
  thinkit::Switch &control_device = Testbed().ControlSwitch();
  const P4Info &p4info = GetParam().p4info;
  ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(p4info));

  EXPECT_OK(
      Testbed().Environment().StoreTestArtifact("p4info.textproto", p4info));
  std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt_session,
      control_p4rt_session;
  ASSERT_OK_AND_ASSIGN(
      std::tie(sut_p4rt_session, control_p4rt_session),
      pins_test::ConfigureSwitchPairAndReturnP4RuntimeSessionPair(
          sut, control_device, GetParam().gnmi_config, p4info));

  // Store gNMI config for debugging purposes.
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(std::string sut_gnmi_config,
                       pins_test::GetGnmiConfig(*sut_gnmi_stub));
  EXPECT_OK(Testbed().Environment().StoreTestArtifact("sut_gnmi_config.json",
                                                      sut_gnmi_config));

  // Pick a link to be used for packet injection.
  ASSERT_OK_AND_ASSIGN(SutToControlLink link_used_for_test_packets,
                       PickSutToControlDeviceLinkThatsUp(Testbed()));
  LOG(INFO) << "Link used to inject test packets: "
            << link_used_for_test_packets;

  // Extract loopback IPs from gNMI config, to avoid using them in test packets.
  using IpAddresses =
      std::vector<std::variant<netaddr::Ipv4Address, netaddr::Ipv6Address>>;
  ASSERT_OK_AND_ASSIGN(IpAddresses loopback_ips,
                       ParseLoopbackIps(sut_gnmi_config));

  // Read CPU queue state prior to injecting test packets. The state should
  // remain unchanged when we inject test packets.
  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, sut.CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(openconfig::QueuesByName initial_cpu_queue_state,
                       GetCpuQueueStateViaGnmi(*gnmi_stub));

  // Inject test packets and verify that the CPU queue state remains
  // unchanged.
  ASSERT_OK_AND_ASSIGN(std::vector<packetlib::Packet> test_packets,
                       TestPacketsThatShouldNotGetPunted());
  for (const packetlib::Packet &packet : test_packets) {
    // Ensure we are not hitting the loopback IP, as this would be a case in
    // which we *do* expect the packet to arrive at the CPU.
    for (const packetlib::Header &header : packet.headers()) {
      if (header.has_ipv4_header()) {
        ASSERT_OK_AND_ASSIGN(auto ip_dst,
                             netaddr::Ipv4Address::OfString(
                                 header.ipv4_header().ipv4_destination()));
        ASSERT_THAT(loopback_ips, Not(Contains(ip_dst)))
            << "TODO: Implement logic to pick non-loopback IP "
               "address.";
      }
      if (header.has_ipv6_header()) {
        ASSERT_OK_AND_ASSIGN(auto ip_dst,
                             netaddr::Ipv6Address::OfString(
                                 header.ipv6_header().ipv6_destination()));
        ASSERT_THAT(loopback_ips, Not(Contains(ip_dst)))
            << "TODO: Implement logic to pick non-loopback IP "
               "address.";
      }
    }

    LOG(INFO) << "injecting test packet: " << packet.DebugString();
    ASSERT_OK_AND_ASSIGN(std::string raw_packet,
                         packetlib::SerializePacket(packet));
    ASSERT_OK(pins::InjectEgressPacket(
        /*port=*/link_used_for_test_packets.control_device_port_p4rt_name,
        /*packet=*/raw_packet, ir_p4info, control_p4rt_session.get(),
        /*packet_delay=*/std::nullopt));

    LOG(INFO) << "Sleeping for " << kMaxQueueCounterUpdateTime
              << " before checking for queue counter increment.";
    absl::SleepFor(kMaxQueueCounterUpdateTime);
    ASSERT_OK_AND_ASSIGN(openconfig::QueuesByName cpu_queue_state,
                         GetCpuQueueStateViaGnmi(*gnmi_stub));
    EXPECT_THAT(cpu_queue_state, EqualsProto(initial_cpu_queue_state))
        << "for injected test packet: " << packet.DebugString();
    initial_cpu_queue_state = cpu_queue_state;
  }

  // Ensure tha the switch did not punt packets to the controller via P4RT.
  ASSERT_OK_AND_ASSIGN(std::vector<p4::v1::StreamMessageResponse> pi_responses,
                       sut_p4rt_session->ReadStreamChannelResponsesAndFinish());
  for (const auto &pi_response : pi_responses) {
    sai::PacketIn pd_packet;
    EXPECT_OK(pdpi::PiPacketInToPd(ir_p4info, pi_response.packet(), &pd_packet))
        << "where packet = " << pi_response.packet().DebugString();
    ADD_FAILURE() << "SUT punted the following packet to the controller "
                     "via P4Runtime: "
                  << (pd_packet.ByteSizeLong() == 0 // Translation failed.
                          ? pi_response.packet().DebugString()
                          : pd_packet.DebugString());
  }

  LOG(INFO) << "-- END OF TEST -----------------------------------------------";
}

// Purpose: Verify that VLAN tagged packets are received as expected.
TEST_P(CpuQosTestWithoutIxia, PuntToCpuWithVlanTag) {
  LOG(INFO) << "-- START OF TEST ---------------------------------------------";

  // Setup: the testbed consists of a SUT connected to a control device
  // that allows us to send and receive packets to/from the SUT.
  thinkit::Switch &sut = Testbed().Sut();
  thinkit::Switch &control_device = Testbed().ControlSwitch();
  const P4Info &p4info = GetParam().p4info;
  ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(p4info));

  EXPECT_OK(
      Testbed().Environment().StoreTestArtifact("p4info.textproto", p4info));
  std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt_session,
      control_p4rt_session;

  ASSERT_OK_AND_ASSIGN(
      std::tie(sut_p4rt_session, control_p4rt_session),
      pins_test::ConfigureSwitchPairAndReturnP4RuntimeSessionPair(
          sut, control_device, absl::nullopt, p4info));

  // Pick a link to be used for packet injection.
  ASSERT_OK_AND_ASSIGN(SutToControlLink link_used_for_test_packets,
                       PickSutToControlDeviceLinkThatsUp(Testbed()));
  LOG(INFO) << "Link used to inject test packets: "
            << link_used_for_test_packets;
  std::vector<packetlib::Packet> test_packets;
  // Test packet.
  ASSERT_OK_AND_ASSIGN(packetlib::Packet ipv4_packet,
                       gutil::ParseTextProto<packetlib::Packet>(R"pb(
        headers {
          ethernet_header {
            ethernet_destination: "00:01:02:02:02:02"
            ethernet_source: "00:01:02:03:04:05"
            ethertype: "0x8100"
          }
        }
        headers {
          vlan_header {
            priority_code_point: "0x0"
            drop_eligible_indicator: "0x1"
            vlan_identifier: "0x123"
            ethertype: "0x0800"
          }
        }
        headers {
          ipv4_header {
            version: "0x4"
            ihl: "0x5"
            dscp: "0x00"
            ecn: "0x0"
            identification: "0xa3cd"
            flags: "0x0"
            fragment_offset: "0x0000"
            ttl: "0x10"
            protocol: "0x11"
            ipv4_source: "10.0.0.2"
            ipv4_destination: "10.0.0.3"
          }
        }
        headers {
          udp_header { source_port: "0x0000" destination_port: "0x0000" }
        }
        payload: "IPv4 test packet with VLAN tag"
      )pb"));

  test_packets.push_back(ipv4_packet);

  ASSERT_OK_AND_ASSIGN(packetlib::Packet ipv6_packet,
                       gutil::ParseTextProto<packetlib::Packet>(R"pb(
        headers {
          ethernet_header {
            ethernet_destination: "00:01:02:02:02:02"
            ethernet_source: "00:01:02:03:04:05"
            ethertype: "0x8100"
          }
        }
        headers {
          vlan_header {
            priority_code_point: "0x0"
            drop_eligible_indicator: "0x1"
            vlan_identifier: "0x123"
            ethertype: "0x86dd"
          }
        }
        headers {
          ipv6_header {
            dscp: "0x00"
            ecn: "0x0"
            flow_label: "0x00000"
            next_header: "0x11"
            hop_limit: "0x40"
            ipv6_source: "2001:db8:0:12::1"
            ipv6_destination: "2001:db8:0:12::2"
          }
        }
        headers {
          udp_header { source_port: "0x0000" destination_port: "0x0000" }
        }
        payload: "IPv6 test packet with VLAN tag"
      )pb"));

  test_packets.push_back(ipv6_packet);

  // Install ACL table entry to be hit with a test packet.
  ASSERT_OK_AND_ASSIGN(const sai::TableEntry pd_acl_entry,
                       gutil::ParseTextProto<sai::TableEntry>(R"pb(
        acl_ingress_table_entry {
          priority: 1
          match {
            dst_mac { value: "00:01:02:02:02:02" mask: "ff:ff:ff:ff:ff:ff" }
          }
          action { acl_trap { qos_queue: "0x3" } }
        }
      )pb"));

  ASSERT_OK_AND_ASSIGN(
      const p4::v1::TableEntry pi_acl_entry,
      pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, pd_acl_entry));
  ASSERT_OK(pdpi::InstallPiTableEntry(sut_p4rt_session.get(), pi_acl_entry));

  for (packetlib::Packet &test_packet : test_packets) {
    // Start from fresh P4RT session.
    ASSERT_OK_AND_ASSIGN(sut_p4rt_session, pdpi::P4RuntimeSession::Create(sut));

    // Send packets.
    ASSERT_OK(packetlib::PadPacketToMinimumSize(test_packet));
    ASSERT_OK(packetlib::UpdateAllComputedFields(test_packet));
    ASSERT_OK_AND_ASSIGN(const std::string raw_packet,
                         packetlib::SerializePacket(test_packet));
    const int kPacketCount = 10;
    for (int iter = 0; iter < kPacketCount; iter++) {
      ASSERT_OK(pins::InjectEgressPacket(
          /*port=*/link_used_for_test_packets.control_device_port_p4rt_name,
          /*packet=*/raw_packet, ir_p4info, control_p4rt_session.get(),
          /*packet_delay=*/std::nullopt));
    }

    // Verify we receive expected packets back.
    absl::SleepFor(absl::Seconds(1));
    int num_vlan_packets_received = 0;
    ASSERT_OK_AND_ASSIGN(
        std::vector<p4::v1::StreamMessageResponse> pi_responses,
        sut_p4rt_session->ReadStreamChannelResponsesAndFinish());
    for (const auto &pi_response : pi_responses) {
      sai::StreamMessageResponse pd_response;
      ASSERT_OK(pdpi::PiStreamMessageResponseToPd(ir_p4info, pi_response,
                                                  &pd_response))
          << " packet in PI to PD failed: " << pi_response.DebugString();
      ASSERT_TRUE(pd_response.has_packet())
          << " received unexpected stream message for packet in: "
          << pd_response.DebugString();
      packetlib::Packet punted_packet =
          packetlib::ParsePacket(pd_response.packet().payload());
      EXPECT_THAT(punted_packet, EqualsProto(test_packet));
      num_vlan_packets_received += 1;
    }
    EXPECT_EQ(num_vlan_packets_received, kPacketCount);
  }
  LOG(INFO) << "-- END OF TEST -----------------------------------------------";
}

// Purpose: Verify DSCP-to-queue mapping for traffic to switch loopback IP.
TEST_P(CpuQosTestWithoutIxia, TrafficToLoopbackIpGetsMappedToCorrectQueues) {
  LOG(INFO) << "-- START OF TEST ---------------------------------------------";

  // Check that a test packet generator function is specified.
  ASSERT_TRUE(static_cast<bool>(GetParam().test_packet_generator_function))
      << "missing required parameter `test_packet_generator_function`";

  // Setup: the testbed consists of a SUT connected to a control device
  // that allows us to send and receive packets to/from the SUT.
  thinkit::Switch &sut = Testbed().Sut();
  thinkit::Switch &control_device = Testbed().ControlSwitch();

  const P4Info &p4info = GetParam().p4info;
  ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(p4info));

  // Configure mirror testbed.
  EXPECT_OK(
      Testbed().Environment().StoreTestArtifact("p4info.textproto", p4info));
    std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt_session,
      control_p4rt_session;
  ASSERT_OK_AND_ASSIGN(
      std::tie(sut_p4rt_session, control_p4rt_session),
      pins_test::ConfigureSwitchPairAndReturnP4RuntimeSessionPair(
          sut, control_device, GetParam().gnmi_config, p4info));

  // Store gNMI config for debugging purposes.
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(std::string sut_gnmi_config,
                       pins_test::GetGnmiConfig(*sut_gnmi_stub));
  EXPECT_OK(Testbed().Environment().StoreTestArtifact("sut_gnmi_config.json",
                                                      sut_gnmi_config));

  // Pick a link to be used for packet injection.
  ASSERT_OK_AND_ASSIGN(SutToControlLink link_used_for_test_packets,
                       PickSutToControlDeviceLinkThatsUp(Testbed()));
  LOG(INFO) << "Link used to inject test packets: "
            << link_used_for_test_packets;

  std::vector<PacketAndExpectedTargetQueue> test_packets =
      GetParam().test_packet_generator_function(sut_gnmi_config);
  ASSERT_FALSE(test_packets.empty())
      << "No packets to test, maybe no loopback IP is configured on switch?";

  for (const PacketAndExpectedTargetQueue &test_packet : test_packets) {
    std::string_view target_queue = test_packet.target_queue;
    SCOPED_TRACE(absl::StrCat("Packet: ", test_packet.packet_name,
                              ", Target queue: ", target_queue));
    LOG(INFO) << absl::StrCat("Packet: ", test_packet.packet_name,
                              ", Target queue: ", target_queue);
    ASSERT_GT(test_packet.packet.headers().size(), 0);
    ASSERT_TRUE(test_packet.packet.headers(0).has_ethernet_header());
    ASSERT_OK_AND_ASSIGN(
        sai::TableEntry l3_admit_entry,
        gutil::ParseTextProto<sai::TableEntry>(absl::Substitute(
            R"pb(
              l3_admit_table_entry {
                match { dst_mac { value: "$0" mask: "FF:FF:FF:FF:FF:FF" } }
                action { admit_to_l3 {} }
                priority: 1
              }
            )pb",
            test_packet.packet.headers(0)
                .ethernet_header()
                .ethernet_destination())));

    ASSERT_OK_AND_ASSIGN(p4::v1::TableEntry pi_entry,
                         pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, l3_admit_entry));

    // Clear table entries and install l3 admit entry.
    ASSERT_OK(pdpi::ClearTableEntries(sut_p4rt_session.get()));
    ASSERT_OK(pdpi::InstallPiTableEntry(sut_p4rt_session.get(), pi_entry));
    // Read counters of the target queue.
    ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());
    ASSERT_OK_AND_ASSIGN(
        const QueueCounters queue_counters_before_test_packet,
        GetGnmiQueueCounters(/*port=*/"CPU", /*queue=*/target_queue,
                             *sut_gnmi_stub));
    ASSERT_OK_AND_ASSIGN(std::string raw_packet,
                         packetlib::SerializePacket(test_packet.packet));

    const int kPacketCount = 50;
    for (int iter = 0; iter < kPacketCount; iter++) {
      ASSERT_OK(pins::InjectEgressPacket(
          /*port=*/link_used_for_test_packets.control_device_port_p4rt_name,
          /*packet=*/raw_packet, ir_p4info, control_p4rt_session.get(),
          /*packet_delay=*/std::nullopt));
    }
    // Read counter of the target queue again.
    absl::Time time_packet_sent = absl::Now();
    QueueCounters queue_counters_after_test_packet;
    do {
      ASSERT_OK_AND_ASSIGN(
          queue_counters_after_test_packet,
          GetGnmiQueueCounters(/*port=*/"CPU", /*queue=*/target_queue,
                               *sut_gnmi_stub));
    } while (
        // It may take several seconds for the queue counters to update.
        TotalPacketsForQueue(queue_counters_after_test_packet) <
            TotalPacketsForQueue(queue_counters_before_test_packet) +
                kPacketCount &&
        absl::Now() - time_packet_sent < kMaxQueueCounterUpdateTime);
    // We terminate early if this fails, as that can cause this loop to get
    // out of sync when counters increment after a long delay, resulting in
    // confusing error messages where counters increment by 2.
    ASSERT_EQ(TotalPacketsForQueue(queue_counters_after_test_packet),
              TotalPacketsForQueue(queue_counters_before_test_packet) +
                  kPacketCount)
        << "Counters for queue " << target_queue << " did not increment within "
        << kMaxQueueCounterUpdateTime
        << " after injecting the following test packet:\n"
        << test_packet.packet.DebugString()
        << "\nBefore: " << queue_counters_before_test_packet
        << "\nAfter : " << queue_counters_after_test_packet;
  }
  LOG(INFO) << "-- END OF TEST -----------------------------------------------";
}

// Buffering and software bottlenecks can cause
// some amount of variance in rate measured end to end.
// Level of tolerance for packet rate verification.
// This could be parameterized in future if this is platform
// dependent.
constexpr float kTolerancePercent = 10.0;

// Ixia configurations:
// 1. Frames sent per second by Ixia.
// 2. Total frames sent by Ixia.
// 3. Default framesize.
// 4. Maximum framesize.
// 5. Minimum framesize.
constexpr int kFramesPerSecond = 1000000;
constexpr int kTotalFrames = 10000000;
constexpr absl::Duration kTrafficDuration =
    absl::Seconds(kTotalFrames / kFramesPerSecond);
constexpr int kDefaultFrameSize = 1514;
constexpr int kMaxFrameSize = 9216;
constexpr int kMinFrameSize = 64;

struct PacketReceiveInfo {
  absl::Mutex mutex;
  int num_packets_punted ABSL_GUARDED_BY(mutex) = 0;
  absl::Time time_first_packet_punted ABSL_GUARDED_BY(mutex);
  absl::Time time_last_packet_punted ABSL_GUARDED_BY(mutex);
};

// Structure represents a link between SUT and Ixia.
// This is represented by Ixia interface name and the SUT's gNMI interface
// name.
struct IxiaLink {
  std::string ixia_interface;
  std::string sut_interface;
};
// Go over the connections and return vector of connections
// whose links are up.
absl::StatusOr<std::vector<IxiaLink>> GetReadyIxiaLinks(
    thinkit::GenericTestbed &generic_testbed,
    gnmi::gNMI::StubInterface &gnmi_stub) {
  std::vector<IxiaLink> links;
  absl::flat_hash_map<std::string, thinkit::InterfaceInfo> interface_info =
      generic_testbed.GetSutInterfaceInfo();
  // Loop through the interface_info looking for Ixia/SUT interface pairs,
  // checking if the link is up.  Add the pair to connections.
  for (const auto &[interface, info] : interface_info) {
    bool sut_link_up = false;
    if (info.interface_modes.contains(thinkit::TRAFFIC_GENERATOR))
    {
      ASSIGN_OR_RETURN(sut_link_up, CheckLinkUp(interface, gnmi_stub));
      if (sut_link_up) {
        links.push_back({
            .ixia_interface = info.peer_interface_name,
            .sut_interface = interface,
        });
      }
    }
  }
  return links;
}

TEST_P(CpuQosTestWithIxia, TestCPUQueueAssignmentAndQueueRateLimit) {
  // Pick a testbed with an Ixia Traffic Generator.
  auto requirements =
      gutil::ParseProtoOrDie<thinkit::TestRequirements>(
          R"pb(interface_requirements {
                 count: 1
                 interface_modes: TRAFFIC_GENERATOR
               })pb");

  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<thinkit::GenericTestbed> generic_testbed,
      GetParam().testbed_interface->GetTestbedWithRequirements(requirements));

  ASSERT_OK(generic_testbed->Environment().StoreTestArtifact(
      "gnmi_config.txt", GetParam().gnmi_config));

  ASSERT_GT(GetParam().control_plane_bandwidth_bytes_per_second, 0);

  thinkit::Switch &sut = generic_testbed->Sut();

  // Configure SUT.
  EXPECT_OK(generic_testbed->Environment().StoreTestArtifact(
      "gnmi_config.json", GetParam().gnmi_config));
  EXPECT_OK(generic_testbed->Environment().StoreTestArtifact(
      "p4info.textproto", GetParam().p4info));

  ASSERT_OK_AND_ASSIGN(std::unique_ptr<pdpi::P4RuntimeSession> sut_p4_session,
                       pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
                           sut, std::nullopt, GetParam().p4info));
  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, sut.CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(std::string sut_gnmi_config,
                       pins_test::GetGnmiConfig(*gnmi_stub));
  // Flow details.
  const auto dest_mac = netaddr::MacAddress(02, 02, 02, 02, 02, 02);
  const auto source_mac = netaddr::MacAddress(00, 01, 02, 03, 04, 05);
  const auto source_ip = netaddr::Ipv6Address(0x1000, 0, 0, 0, 0, 0, 0, 1);
  const auto dest_ip = netaddr::Ipv6Address(0x1000, 0, 0, 0, 0, 0, 0, 2);
  // Extract loopback IPs from gNMI config, to avoid using them in test packets.
  using IpAddresses = std::vector<netaddr::Ipv6Address>;
  ASSERT_OK_AND_ASSIGN(IpAddresses loopback_ipv6,
                       ParseLoopbackIpv6s(sut_gnmi_config));
  ASSERT_GE(loopback_ipv6.size(), 1) << "No Loopback IPs configured on switch";

  ASSERT_OK_AND_ASSIGN(std::vector<IxiaLink> ready_links,
                       GetReadyIxiaLinks(*generic_testbed, *gnmi_stub));

  ASSERT_FALSE(ready_links.empty()) << "Ixia links are not ready";

  std::string ixia_interface = ready_links[0].ixia_interface;
  std::string sut_interface = ready_links[0].sut_interface;

  // Set up Ixia traffic.
  // Send Ixia traffic.
  // Stop Ixia traffic.

  ASSERT_OK_AND_ASSIGN(ixia::IxiaPortInfo ixia_port,
                       ixia::ExtractPortInfo(ixia_interface));

  ASSERT_OK_AND_ASSIGN(
      std::string topology_ref,
      pins_test::ixia::IxiaConnect(ixia_port.hostname, *generic_testbed));

  ASSERT_OK_AND_ASSIGN(
      std::string vport_ref,
      pins_test::ixia::IxiaVport(topology_ref, ixia_port.card, ixia_port.port,
                                 *generic_testbed));

  ASSERT_OK_AND_ASSIGN(
      std::string traffic_ref,
      pins_test::ixia::IxiaSession(vport_ref, *generic_testbed));

  ASSERT_OK(pins_test::ixia::SetFrameRate(traffic_ref, kFramesPerSecond,
                                          *generic_testbed));

  ASSERT_OK(pins_test::ixia::SetFrameCount(traffic_ref, kTotalFrames,
                                           *generic_testbed));

  ASSERT_OK(pins_test::ixia::SetFrameSize(traffic_ref, kDefaultFrameSize,
                                          *generic_testbed));

  ASSERT_OK(pins_test::ixia::SetSrcMac(traffic_ref, source_mac.ToString(),
                                       *generic_testbed));

  ASSERT_OK(pins_test::ixia::SetDestMac(traffic_ref, dest_mac.ToString(),
                                        *generic_testbed));

  ASSERT_OK(pins_test::ixia::AppendIPv6(traffic_ref, *generic_testbed));

  ASSERT_OK(pins_test::ixia::SetSrcIPv6(traffic_ref, source_ip.ToString(),
                                        *generic_testbed));

  ASSERT_OK(pins_test::ixia::SetDestIPv6(traffic_ref, dest_ip.ToString(),
                                         *generic_testbed));

  // Listen for punted packets from the SUT.
  PacketReceiveInfo packet_receive_info;

  PacketInReceiver receiver(*sut_p4_session, [&packet_receive_info](auto) {
    absl::MutexLock lock(&packet_receive_info.mutex);
    if (packet_receive_info.num_packets_punted == 0) {
      packet_receive_info.time_first_packet_punted = absl::Now();
    }
    packet_receive_info.time_last_packet_punted = absl::Now();
    packet_receive_info.num_packets_punted++;
    return;
  });

  // Get Queues.
  ASSERT_OK_AND_ASSIGN(auto queues,
                       ExtractQueueInfoViaGnmiConfig(GetParam().gnmi_config));

  constexpr absl::string_view kPuntOnlyTest = "punt_only_test";
  constexpr absl::string_view kLoopbackPuntTest = "to_loopback_punt_test";
  constexpr absl::string_view kLoopbackPuntTtl0Test =
      "to_loopback_ttl0_punt_test";

  for (auto test_case :
       {kPuntOnlyTest, kLoopbackPuntTest, kLoopbackPuntTtl0Test}) {
    LOG(INFO) << "\n\nTesting case: " << test_case;
    LOG(INFO) << "\n===================\n\n";
    if (test_case == kLoopbackPuntTest) {
      ASSERT_OK(pins_test::ixia::SetDestIPv6(
          traffic_ref, loopback_ipv6.front().ToString(), *generic_testbed));
      LOG(INFO) << "Traffic to Loopback IP: "
                << loopback_ipv6.front().ToString();
    } else if (test_case == kLoopbackPuntTtl0Test) {
      ASSERT_OK(pins_test::ixia::SetDestIPv6(
          traffic_ref, loopback_ipv6.front().ToString(), *generic_testbed));
      ASSERT_OK(pins_test::ixia::SetIpTTL(traffic_ref, /*ttl=*/0,
                                          /*is_ipv4=*/false, *generic_testbed));
      LOG(INFO) << "Traffic with TTL=0 and to Loopback IP: "
                << loopback_ipv6.front().ToString();
    }
    for (auto &[queue_name, queue_info] : queues) {
      // TODO : Need to fix supported CPU queues. Currently,
      // punting to queue 0 is not supported by OA in SONiC.
      if (generic_testbed->Environment().MaskKnownFailures() &&
          queue_info.p4_queue_name == "0x0") {
        continue;
      }

      LOG(INFO) << "\n\n\nTesting Queue : " << queue_info.gnmi_queue_name
                << "\n===================\n\n\n";

      // Verify configuration on the queue matches expected configuration
      // in the case that expected queue limit was passed in.
      if (GetParam().expected_queue_limit_config_pps.contains(
              queue_info.gnmi_queue_name)) {
        EXPECT_EQ(queue_info.rate_packets_per_second,
                  GetParam().expected_queue_limit_config_pps.at(
                      queue_info.gnmi_queue_name));
      }

      // Set framesize based on supported control plane bandwidth.
      int frame_size = GetParam().control_plane_bandwidth_bytes_per_second /
                       queue_info.rate_packets_per_second;
      // Framesize lesser than 64 bytes is not a viable frame, hence we will
      // skip end to end rate check.
      if (frame_size < kMinFrameSize) {
        LOG(INFO)
            << "Skipping, as queue rate " << queue_info.rate_packets_per_second
            << "(pps) is infeasible to test with control plane bandwidth of "
            << GetParam().control_plane_bandwidth_bytes_per_second
            << " bytes per second.";
        continue;
      }

      if (frame_size > kMaxFrameSize) {
        frame_size = kMaxFrameSize;
      }

      ASSERT_OK(pins_test::ixia::SetFrameSize(traffic_ref, frame_size,
                                              *generic_testbed));

      ASSERT_OK(SetUpV6PuntToCPU(dest_mac, source_ip, dest_ip,
                                 queue_info.p4_queue_name, GetParam().p4info,
                                 *sut_p4_session));
      ASSERT_OK_AND_ASSIGN(
          QueueCounters initial_counters,
          GetGnmiQueueCounters("CPU", queue_info.gnmi_queue_name, *gnmi_stub));

      // Reset received packet count at tester.
      {
        absl::MutexLock lock(&packet_receive_info.mutex);
        packet_receive_info.num_packets_punted = 0;
      }

      ASSERT_OK(pins_test::ixia::StartTraffic(traffic_ref, topology_ref,
                                              *generic_testbed));

      // Wait for Traffic to be sent.
      absl::SleepFor(kTrafficDuration);

      static constexpr absl::Duration kPollInterval = absl::Seconds(5);
      static constexpr absl::Duration kTotalTime = absl::Seconds(30);
      static const int kIterations = kTotalTime / kPollInterval;

      QueueCounters final_counters;
      QueueCounters delta_counters;
      // Check for counters every 5 seconds up to 30 seconds till they match.
      for (int gnmi_counters_check = 0; gnmi_counters_check < kIterations;
           gnmi_counters_check++) {
        absl::SleepFor(kPollInterval);
        ASSERT_OK_AND_ASSIGN(
            final_counters, GetGnmiQueueCounters(
                                "CPU", queue_info.gnmi_queue_name, *gnmi_stub));
        delta_counters = {
            .num_packets_transmitted = final_counters.num_packets_transmitted -
                                       initial_counters.num_packets_transmitted,
            .num_packets_dropped = final_counters.num_packets_dropped -
                                   initial_counters.num_packets_dropped,
        };
        LOG(INFO) << "Tx = " << delta_counters.num_packets_transmitted
                  << " Drop = " << delta_counters.num_packets_dropped;
        if (delta_counters.num_packets_transmitted +
                delta_counters.num_packets_dropped ==
            kTotalFrames) {
          break;
        }
        ASSERT_NE(gnmi_counters_check, kIterations - 1)
            << "GNMI packet count "
            << delta_counters.num_packets_transmitted +
                   delta_counters.num_packets_dropped
            << " != Packets sent from Ixia " << kTotalFrames;
      }

      {
        absl::MutexLock lock(&packet_receive_info.mutex);
        // Verify the received packets matches gNMI queue stats.
        ASSERT_LE(packet_receive_info.num_packets_punted,
                  delta_counters.num_packets_transmitted);
        ASSERT_GE(packet_receive_info.num_packets_punted,
                  delta_counters.num_packets_transmitted *
                      (1 - kTolerancePercent / 100));
        absl::Duration duration = packet_receive_info.time_last_packet_punted -
                                  packet_receive_info.time_first_packet_punted;

        LOG(INFO) << "Packets received at Controller: "
                  << packet_receive_info.num_packets_punted;
        LOG(INFO) << "Packet size: " << frame_size;
        LOG(INFO) << "Timestamp of first received packet: "
                  << packet_receive_info.time_first_packet_punted;
        LOG(INFO) << "Timestamp of last received packet: "
                  << packet_receive_info.time_last_packet_punted;
        LOG(INFO) << "Duration of packets received: " << duration;
        int rate_received = 0;
        if (int64_t useconds = absl::ToInt64Microseconds(duration);
            useconds != 0) {
          rate_received =
              packet_receive_info.num_packets_punted * 1000000 / useconds;
          LOG(INFO) << "Rate of packets received (pps): " << rate_received;
        }
        EXPECT_LE(rate_received, queue_info.rate_packets_per_second *
                                     (1 + kTolerancePercent / 100));
        EXPECT_GE(rate_received, queue_info.rate_packets_per_second *
                                     (1 - kTolerancePercent / 100));
      }
    } // for each queue.
  }   // test_case
  // Stop receiving at tester.
  receiver.Destroy();
}

TEST_P(CpuQosTestWithIxia, TestPuntFlowRateLimitAndCounters) {
  // Pick a testbed with an Ixia Traffic Generator.
  auto requirements =
      gutil::ParseProtoOrDie<thinkit::TestRequirements>(
          R"pb(interface_requirements {
                 count: 1
                 interface_modes: TRAFFIC_GENERATOR
               })pb");

  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<thinkit::GenericTestbed> generic_testbed,
      GetParam().testbed_interface->GetTestbedWithRequirements(requirements));

  // TODO: Skip test till known failure is fixed.
  GTEST_SKIP() << "Skipping till b/203545459 is fixed";

  ASSERT_OK(generic_testbed->Environment().StoreTestArtifact(
      "gnmi_config.txt", GetParam().gnmi_config));

  ASSERT_GT(GetParam().control_plane_bandwidth_bytes_per_second, 0);

  thinkit::Switch &sut = generic_testbed->Sut();

  // Configure SUT.
  EXPECT_OK(generic_testbed->Environment().StoreTestArtifact(
      "gnmi_config.json", GetParam().gnmi_config));
  EXPECT_OK(generic_testbed->Environment().StoreTestArtifact(
      "p4info.textproto", GetParam().p4info));
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<pdpi::P4RuntimeSession> sut_p4_session,
                       pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
                           sut, GetParam().gnmi_config, GetParam().p4info));

  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, sut.CreateGnmiStub());

  // Disable sFlow since it would interfere with the test results.
  ASSERT_OK(pins::SetSflowConfigEnabled(gnmi_stub.get(), /*enabled=*/false));

  absl::Cleanup cleanup([&] {
    // Restore sflow enable config.
    ASSERT_OK_AND_ASSIGN(bool sflow_enabled,
                         pins::IsSflowConfigEnabled(GetParam().gnmi_config));
    EXPECT_OK(pins::SetSflowConfigEnabled(gnmi_stub.get(), sflow_enabled))
        << "failed to restore sflow configuration -- switch config may be "
           "corrupted, causing subsequent test to fail";
  });

  // Flow details.
  const auto dest_mac = netaddr::MacAddress(02, 02, 02, 02, 02, 02);
  const auto source_mac = netaddr::MacAddress(00, 01, 02, 03, 04, 05);
  const auto source_ip = netaddr::Ipv4Address(192, 168, 10, 1);
  const auto dest_ip = netaddr::Ipv4Address(172, 0, 0, 1);

  // Go through all the ports that interface to the Ixia and set them
  // first to 200GB.
  const absl::flat_hash_map<std::string, thinkit::InterfaceInfo>
      interface_info = generic_testbed->GetSutInterfaceInfo();
  for (const auto &[interface, info] : interface_info) {
    if (info.interface_modes.contains(thinkit::TRAFFIC_GENERATOR)) {
      ASSERT_OK(SetPortSpeedInBitsPerSecond(
          "\"openconfig-if-ethernet:SPEED_200GB\"", interface, *gnmi_stub));
      ASSERT_OK(SetPortMtu(kMaxFrameSize, interface, *gnmi_stub));
    }
  }

  // Wait to let the links come up. Switch guarantees state paths to reflect
  // in 10s. Lets wait for a bit more.
  LOG(INFO) << "Sleeping " << kTimeToWaitForGnmiConfigToApply
            << " to wait for config to be applied/links to come up.";
  absl::SleepFor(kTimeToWaitForGnmiConfigToApply);
  ASSERT_OK(
      pins_test::WaitForGnmiPortIdConvergence(sut, GetParam().gnmi_config,
      /*timeout=*/absl::Minutes(3)));

  ASSERT_OK_AND_ASSIGN(std::vector<IxiaLink> ready_links,
                       GetReadyIxiaLinks(*generic_testbed, *gnmi_stub));
  // If links didnt come, lets try 100GB as some testbeds have 100GB
  // IXIA connections.
  if (ready_links.empty()) {
    for (const auto &[interface, info] : interface_info) {
      if (info.interface_modes.contains(thinkit::TRAFFIC_GENERATOR))
        ASSERT_OK(SetPortSpeedInBitsPerSecond(
            "\"openconfig-if-ethernet:SPEED_100GB\"", interface, *gnmi_stub));
      }
    }
    // Wait to let the links come up. Switch guarantees state paths to reflect
    // in 10s. Lets wait for a bit more.
    LOG(INFO) << "Sleeping " << kTimeToWaitForGnmiConfigToApply
              << " to wait for config to be applied/links to come up.";
    absl::SleepFor(kTimeToWaitForGnmiConfigToApply);
    ASSERT_OK_AND_ASSIGN(ready_links,
                         GetReadyIxiaLinks(*generic_testbed, *gnmi_stub));

  ASSERT_FALSE(ready_links.empty()) << "Ixia links are not ready";
  std::string ixia_interface = ready_links[0].ixia_interface;
  std::string sut_interface = ready_links[0].sut_interface;

  // We will perform the following steps with Ixia:
  // Set up Ixia traffic.
  // Send Ixia traffic.
  // Stop Ixia traffic.

  ASSERT_OK_AND_ASSIGN(ixia::IxiaPortInfo ixia_port,
                       ixia::ExtractPortInfo(ixia_interface));

  ASSERT_OK_AND_ASSIGN(
      std::string topology_ref,
      pins_test::ixia::IxiaConnect(ixia_port.hostname, *generic_testbed));

  ASSERT_OK_AND_ASSIGN(
      std::string vport_ref,
      pins_test::ixia::IxiaVport(topology_ref, ixia_port.card, ixia_port.port,
                                 *generic_testbed));

  ASSERT_OK_AND_ASSIGN(
      std::string traffic_ref,
      pins_test::ixia::IxiaSession(vport_ref, *generic_testbed));

  ASSERT_OK(pins_test::ixia::SetFrameRate(traffic_ref, kFramesPerSecond,
                                          *generic_testbed));

  ASSERT_OK(pins_test::ixia::SetFrameCount(traffic_ref, kTotalFrames,
                                           *generic_testbed));

  ASSERT_OK(pins_test::ixia::SetFrameSize(traffic_ref, kMaxFrameSize,
                                          *generic_testbed));

  ASSERT_OK(pins_test::ixia::SetSrcMac(traffic_ref, source_mac.ToString(),
                                       *generic_testbed));

  ASSERT_OK(pins_test::ixia::SetDestMac(traffic_ref, dest_mac.ToString(),
                                        *generic_testbed));

  ASSERT_OK(pins_test::ixia::AppendIPv4(traffic_ref, *generic_testbed));

  ASSERT_OK(pins_test::ixia::SetSrcIPv4(traffic_ref, source_ip.ToString(),
                                        *generic_testbed));

  ASSERT_OK(pins_test::ixia::SetDestIPv4(traffic_ref, dest_ip.ToString(),
                                         *generic_testbed));

  // Listen for punted packets from the SUT.
  PacketReceiveInfo packet_receive_info;
  {
    absl::MutexLock lock(&packet_receive_info.mutex);
    packet_receive_info.num_packets_punted = 0;
  }

  // Get Queues.
  ASSERT_OK_AND_ASSIGN(auto queues,
                       ExtractQueueInfoViaGnmiConfig(GetParam().gnmi_config));

  for (auto &[queue_name, queue_info] : queues) {
    // Lets set flow rate limit to be half of queue limit so that queue limit
    // doesnt take effect.
    int flow_rate_limit_in_bytes_per_second =
        (kMaxFrameSize * queue_info.rate_packets_per_second) / 2;

    if (flow_rate_limit_in_bytes_per_second >
        GetParam().control_plane_bandwidth_bytes_per_second) {
      flow_rate_limit_in_bytes_per_second =
          GetParam().control_plane_bandwidth_bytes_per_second / 2;
    }

    // TODO : Need to fix supported CPU queues. Currently, punting
    // to queue 0 is not supported by OA in SONiC.
    if (generic_testbed->Environment().MaskKnownFailures() &&
        queue_info.p4_queue_name == "0x0") {
      continue;
    }

    LOG(INFO) << "\n\n\nTesting Queue : " << queue_info.gnmi_queue_name
              << "\n===================\n\n\n";

    ASSERT_OK_AND_ASSIGN(
        p4::v1::TableEntry pi_acl_entry,
        SetUpPuntToCPUWithRateLimit(dest_mac, dest_ip, queue_info.p4_queue_name,
                                    flow_rate_limit_in_bytes_per_second,
                                    /*burst_in_bytes=*/kMaxFrameSize,
                                    GetParam().p4info, *sut_p4_session));
    ASSERT_OK_AND_ASSIGN(
        QueueCounters initial_counters,
        GetGnmiQueueCounters("CPU", queue_info.gnmi_queue_name, *gnmi_stub));

    // Reset received packet count at tester for each iteration.
    {
      absl::MutexLock lock(&packet_receive_info.mutex);
      packet_receive_info.num_packets_punted = 0;
    }

    // Check that the counters are initially zero.
    ASSERT_THAT(
        pdpi::ReadPiCounterData(sut_p4_session.get(), pi_acl_entry),
        IsOkAndHolds(EqualsProto(R"pb(byte_count: 0 packet_count: 0)pb")));

    ASSERT_OK(pins_test::ixia::StartTraffic(traffic_ref, topology_ref,
                                            *generic_testbed));

    // Wait for Traffic to be sent.
    absl::SleepFor(kTrafficDuration);

    // Check for counters every 5 seconds upto 30 seconds till the fetched gNMI
    // queue counter stats match packets and bytes sent by Ixia.
    // Check that the counters increment within kMaxQueueCounterUpdateTime.
    absl::Time time_packet_sent = absl::Now();
    p4::v1::CounterData counter_data;
    do {
      ASSERT_OK_AND_ASSIGN(
          counter_data,
          pdpi::ReadPiCounterData(sut_p4_session.get(), pi_acl_entry));
    } while (counter_data.packet_count() != kTotalFrames &&
             absl::Now() - time_packet_sent < kMaxQueueCounterUpdateTime);
    p4::v1::CounterData expected_counter_data;
    expected_counter_data.set_packet_count(kTotalFrames);
    expected_counter_data.set_byte_count(static_cast<int64_t>(kMaxFrameSize) *
                                         static_cast<int64_t>(kTotalFrames));
    EXPECT_THAT(counter_data, EqualsProto(expected_counter_data))
        << "Counter for the table entry given below did not match expectation "
           "within "
        << kMaxQueueCounterUpdateTime
        << " after injecting the Ixia test packets via CPU queue "
        << queue_name;

    // Verify GNMI queue stats match packets received.
    static constexpr absl::Duration kPollInterval = absl::Seconds(5);
    static constexpr absl::Duration kTotalTime = absl::Seconds(20);
    static const int kIterations = kTotalTime / kPollInterval;
    // Check for counters every 5 seconds upto 20 seconds till they match.
    for (int gnmi_counters_check = 0; gnmi_counters_check < kIterations;
         gnmi_counters_check++) {
      absl::SleepFor(kPollInterval);
      QueueCounters final_counters;
      QueueCounters delta_counters;
      ASSERT_OK_AND_ASSIGN(
          final_counters,
          GetGnmiQueueCounters("CPU", queue_info.gnmi_queue_name, *gnmi_stub));
      delta_counters = {
          .num_packets_transmitted = final_counters.num_packets_transmitted -
                                     initial_counters.num_packets_transmitted,
          .num_packets_dropped = final_counters.num_packets_dropped -
                                 initial_counters.num_packets_dropped,
      };
      LOG(INFO) << delta_counters;
      absl::MutexLock lock(&packet_receive_info.mutex);
      if (delta_counters.num_packets_transmitted ==
          packet_receive_info.num_packets_punted) {
        break;
      }
      ASSERT_NE(gnmi_counters_check, kIterations - 1)
          << "GNMI packet count "
          << delta_counters.num_packets_transmitted +
                 delta_counters.num_packets_dropped
          << " != Packets received at controller "
          << packet_receive_info.num_packets_punted;
    }

    {
      absl::MutexLock lock(&packet_receive_info.mutex);

      LOG(INFO) << "Packets received at Controller: "
                << packet_receive_info.num_packets_punted;
      LOG(INFO) << "Timestamp of first received packet: "
                << packet_receive_info.time_first_packet_punted;
      LOG(INFO) << "Timestamp of last received packet: "
                << packet_receive_info.time_last_packet_punted;

      absl::Duration duration = packet_receive_info.time_last_packet_punted -
                                packet_receive_info.time_first_packet_punted;
      LOG(INFO) << "Duration of packets received: " << duration;
      LOG(INFO) << "Frame size: " << kMaxFrameSize;
      int64_t rate_received_in_bytes_per_second = 0;
      int64_t useconds = absl::ToInt64Microseconds(duration);
      ASSERT_NE(useconds, 0);
      int64_t num_bytes =
          packet_receive_info.num_packets_punted * kMaxFrameSize;
      LOG(INFO) << "Num bytes received: " << num_bytes;
      rate_received_in_bytes_per_second = num_bytes * 1000000 / useconds;
      LOG(INFO) << "Rate of packets received (bytes per second): "
                << rate_received_in_bytes_per_second;
      EXPECT_LE(
          rate_received_in_bytes_per_second,
          flow_rate_limit_in_bytes_per_second * (1 + kTolerancePercent / 100));
      EXPECT_GE(
          rate_received_in_bytes_per_second,
          flow_rate_limit_in_bytes_per_second * (1 - kTolerancePercent / 100));
    }
  } // for each queue.
}

}  // namespace
}  // namespace pins_test
