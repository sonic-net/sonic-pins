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

#include "tests/qos/cpu_qos_test.h"

#include <bitset>
#include <cstdint>
#include <memory>
#include <optional>
#include <ostream>
#include <string>
#include <tuple>
#include <utility>
#include <variant>
#include <vector>

#include "absl/base/thread_annotations.h"
#include "absl/cleanup/cleanup.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/flags/declare.h"
#include "absl/flags/flag.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/escaping.h"
#include "absl/strings/match.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/synchronization/mutex.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/optional.h"
#include "absl/types/variant.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "google/protobuf/util/json_util.h"
#include "gtest/gtest.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "gutil/gutil/version.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/gnmi/openconfig.pb.h"
#include "lib/ixia_helper.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/netaddr/ipv4_address.h"
#include "p4_infra/netaddr/ipv6_address.h"
#include "p4_infra/netaddr/mac_address.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/pd.h"
#include "p4_infra/p4_runtime/p4_runtime_session.h"
#include "p4_infra/p4_runtime/p4_runtime_session_extras.h"
#include "p4_infra/packetlib/packetlib.h"
#include "p4_infra/packetlib/packetlib.pb.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "proto/gnmi/gnmi.pb.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"
#include "sai_p4/instantiations/google/versions.h"
#include "tests/forwarding/util.h"
#include "tests/integration/system/nsf/interfaces/testbed.h"
#include "tests/integration/system/nsf/util.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "tests/qos/gnmi_parsers.h"
#include "tests/qos/packet_in_receiver.h"
#include "tests/qos/qos_test_util.h"
#include "tests/sflow/sflow_util.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/generic_testbed_fixture.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/proto/generic_testbed.pb.h"
#include "thinkit/ssh_client.h"
#include "thinkit/switch.h"

ABSL_DECLARE_FLAG(std::optional<sai::Instantiation>, switch_instantiation);

namespace pins_test {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::p4::config::v1::P4Info;
using ::testing::AllOf;
using ::testing::Contains;
using ::testing::Ge;
using ::testing::Le;
using ::testing::Not;

const sai::NexthopRewriteOptions kNextHopRewriteOptions = {
    .src_mac_rewrite = netaddr::MacAddress(0x66, 0x55, 0x44, 0x33, 0x22, 0x11),
    .dst_mac_rewrite = netaddr::MacAddress(2, 2, 2, 2, 2, 2),
};

// Size of the "frame check sequence" (FCS) that is part of Layer 2 Ethernet
// frames.
constexpr int kFrameCheckSequenceSize = 4;

absl::Status NsfRebootHelper(const Testbed &testbed,
                             std::shared_ptr<thinkit::SSHClient> ssh_client) {
  // TODO: Add punt flow before reboot,
  // send traffic and measure downtine based on traffic drop.
  return DoNsfRebootAndWaitForSwitchReadyOrRecover(testbed, *ssh_client);
}

// Set up the switch to punt packets to CPU.
absl::Status SetUpPuntToCPU(const netaddr::MacAddress &dmac,
                            const netaddr::Ipv4Address &dst_ip,
                            absl::string_view p4_queue,
                            const pdpi::IrP4Info &ir_p4info,
                            p4_runtime::P4RuntimeSession &p4_session) {
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
        }
      )pb",
      dmac.ToString(), dst_ip.ToString(), p4_queue));
  p4::v1::TableEntry pi_entry;
  ASSIGN_OR_RETURN(
      pi_entry, pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, acl_entry),
      _.SetPrepend() << "Failed in PD table conversion to PI, entry: "
                     << acl_entry.DebugString() << " error: ");

  LOG(INFO) << "Installing Table Entry: " << acl_entry.ShortDebugString();
  return gutil::StatusBuilder(
             p4_runtime::InstallPiTableEntry(&p4_session, pi_entry))
         << "Failed to install entry: " << acl_entry.ShortDebugString();
}

packetlib::Packet BuildPuntToCpuPacket(const netaddr::MacAddress &dmac,
                                       const netaddr::Ipv4Address &src_ip,
                                       const netaddr::Ipv4Address &dst_ip) {
  return gutil::ParseProtoOrDie<packetlib::Packet>(absl::Substitute(
      R"pb(headers {
             ethernet_header {
               ethernet_destination: "$0"
               ethernet_source: "00:00:00:00:00:7b"
               ethertype: "0x0800"
             }
           }
           headers {
             ipv4_header {
               ihl: "0x5"
               dscp: "0x0a"
               ecn: "0x0"
               identification: "0x0000"
               flags: "0x0"
               fragment_offset: "0x0000"
               ttl: "0x20"
               protocol: "0x11"
               ipv4_source: "$1"
               ipv4_destination: "$2"
             }
           }
           headers {
             udp_header { source_port: "0x0929" destination_port: "0x11d7" }
           })pb",
      dmac.ToString(), src_ip.ToString(), dst_ip.ToString()));
}

// Set up the switch to punt packets to CPU
// The function also adds a wildcard l3_admit entry, so that
// packets addressed to switch are punted to the CPU due to L3.
// We would like packets punted to CPU due to multiple reasons but
// should still be able to receive the packets end to end due to the
// punt flow.
absl::Status SetUpV6PuntToCPUWithRateLimitAndWildCardL3AdmitEntry(
    const netaddr::MacAddress &dmac, const netaddr::Ipv6Address &src_ip,
    const netaddr::Ipv6Address &dst_ip, int rate_bytes_per_second,
    int burst_in_bytes, absl::string_view p4_queue,
    const p4::config::v1::P4Info &p4info,
    p4_runtime::P4RuntimeSession &p4_session) {
  ASSIGN_OR_RETURN(auto ir_p4info, pdpi::CreateIrP4Info(p4info));

  RETURN_IF_ERROR(p4_runtime::SetMetadataAndSetForwardingPipelineConfig(
      &p4_session,
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT, p4info))
      << "SetForwardingPipelineConfig: Failed to push P4Info: ";

  RETURN_IF_ERROR(p4_runtime::ClearTableEntries(&p4_session));

  auto l3_admit_entry = gutil::ParseProtoOrDie<sai::TableEntry>(
      R"pb(
        l3_admit_table_entry {
          match {}  # Wildcard.
          action { admit_to_l3 {} }
          priority: 1
        }
      )pb");
  std::vector<p4::v1::TableEntry> pi_entries;
  ASSIGN_OR_RETURN(
      pi_entries.emplace_back(),
      pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, l3_admit_entry),
      _.SetPrepend() << "Failed in PD table conversion to PI, entry: "
                     << l3_admit_entry.DebugString() << " error: ");

  if (ir_p4info.tables_by_name().contains("acl_ingress_qos_table")) {
    auto punt_entry = gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
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

    LOG(INFO) << "Installing trap rule to queue " << p4_queue
              << " in ACL punt table";
    ASSIGN_OR_RETURN(
        pi_entries.emplace_back(),
        pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, punt_entry));

    auto qos_entry = gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
        R"pb(
          acl_ingress_qos_table_entry {
            match {
              dst_mac { value: "$0" mask: "ff:ff:ff:ff:ff:ff" }
              is_ipv6 { value: "0x1" }
            }
            action {
              set_qos_queue_and_cancel_copy_above_rate_limit { qos_queue: "$1" }
            }
            priority: 4400
            meter_config { bytes_per_second: $2 burst_bytes: $3 }
          }
        )pb",
        dmac.ToString(), p4_queue, rate_bytes_per_second, burst_in_bytes));

    LOG(INFO) << "Installing QoS rule to rate limit flow to a rate of "
              << rate_bytes_per_second << "(Bps) and burst of "
              << burst_in_bytes << "(Bytes)";
    ASSIGN_OR_RETURN(
        pi_entries.emplace_back(),
        pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, qos_entry));
  } else {
    auto acl_entry = gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
        R"pb(
          acl_ingress_table_entry {
            match {
              dst_mac { value: "$0" mask: "ff:ff:ff:ff:ff:ff" }
              is_ipv6 { value: "0x1" }
            }
            action { acl_trap { qos_queue: "$1" } }
            priority: 1
            meter_config { bytes_per_second: $2 burst_bytes: $3 }
          }
        )pb",
        dmac.ToString(), p4_queue, rate_bytes_per_second, burst_in_bytes));

    ASSIGN_OR_RETURN(
        pi_entries.emplace_back(),
        pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, acl_entry),
        _.SetPrepend() << "Failed in PD table conversion to PI, entry: "
                       << acl_entry.DebugString() << " error: ");
  }
  LOG(INFO) << "InstallPiTableEntries";
  return p4_runtime::InstallPiTableEntries(&p4_session, ir_p4info, pi_entries);
}

// Set up the switch to punt packets to CPU with meter.
// Returns a copy of installed Punt Entry or QoS Entry.
absl::StatusOr<p4::v1::TableEntry> SetUpPuntToCPUWithRateLimit(
    const netaddr::MacAddress &dmac, const netaddr::Ipv4Address &dst_ip,
    absl::string_view p4_queue, int rate_bytes_per_second, int burst_in_bytes,
    const AclIngressTablePuntFlowRateLimitAction &acl_ingress_table_action,
    const p4::config::v1::P4Info &p4info,
    p4_runtime::P4RuntimeSession &p4_session) {
  ASSIGN_OR_RETURN(auto ir_p4info, pdpi::CreateIrP4Info(p4info));

  RETURN_IF_ERROR(p4_runtime::SetMetadataAndSetForwardingPipelineConfig(
      &p4_session,
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT, p4info))
      << "SetForwardingPipelineConfig: Failed to push P4Info: ";

  RETURN_IF_ERROR(p4_runtime::ClearTableEntries(&p4_session));

  // There can be 2 schemes for punting depending on pipeline.
  // If p4 info table has the "acl_ingress_qos_table" configured, then
  //     1. Punt the packets using "acl_ingress_table" entry.
  //     2. Rate limit the packets using a "acl_ingress_qos_table" entry, which
  //        allows capability to apply policer on a group of punt entries.
  // else
  //     Punt and Rate limit packets in same entry in "acl_ingress_table"
  if (ir_p4info.tables_by_name().contains(kAclIngressQosTable)) {
    auto punt_entry = gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
        R"pb(
          acl_ingress_table_entry {
            match {
              dst_mac { value: "$0" mask: "ff:ff:ff:ff:ff:ff" }
              is_ipv4 { value: "0x1" }
              dst_ip { value: "$1" mask: "255.255.255.255" }
            }
            action { acl_copy { qos_queue: "$2" } }
            priority: 1
          }
        )pb",
        dmac.ToString(), dst_ip.ToString(), p4_queue));

    LOG(INFO) << "InstallPiTableEntry";
    ASSIGN_OR_RETURN(
        const p4::v1::TableEntry pi_acl_entry,
        pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, punt_entry));
    RETURN_IF_ERROR(p4_runtime::InstallPiTableEntry(&p4_session, pi_acl_entry));

    auto qos_entry = gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
        R"pb(
          acl_ingress_qos_table_entry {
            match {
              dst_mac { value: "$0" mask: "ff:ff:ff:ff:ff:ff" }
              is_ipv4 { value: "0x1" }
            }
            action { $1 { $2: "$3" } }
            priority: 4400
            meter_config { bytes_per_second: $4 burst_bytes: $5 }
          }
        )pb",
        dmac.ToString(), acl_ingress_table_action.rate_limit_action,
        acl_ingress_table_action.cpu_queue_attribute_name, p4_queue,
        rate_bytes_per_second, burst_in_bytes));

    LOG(INFO) << "InstallPiTableEntry";
    ASSIGN_OR_RETURN(
        const p4::v1::TableEntry pi_acl_qos_entry,
        pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, qos_entry));
    RETURN_IF_ERROR(
        p4_runtime::InstallPiTableEntry(&p4_session, pi_acl_qos_entry));

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
            action { $2 { $3: "$4" } }
            priority: 1
            meter_config { bytes_per_second: $5 burst_bytes: $6 }
          }
        )pb",
        dmac.ToString(), dst_ip.ToString(),
        acl_ingress_table_action.rate_limit_action,
        acl_ingress_table_action.cpu_queue_attribute_name, p4_queue,
        rate_bytes_per_second, burst_in_bytes));

    LOG(INFO) << "InstallPiTableEntry";
    ASSIGN_OR_RETURN(
        const p4::v1::TableEntry pi_acl_entry,
        pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, acl_entry));
    RETURN_IF_ERROR(p4_runtime::InstallPiTableEntry(&p4_session, pi_acl_entry));
    return pi_acl_entry;
  }
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

  openconfig::QueuesByName queues_by_name;
  for (auto &queue : queues_proto.queues()) {
    ASSIGN_OR_RETURN(
        std::string transmitted_packets,
        GetGnmiStatePathInfo(
            &gnmi_stub, absl::Substitute(
                            "qos/interfaces/interface[interface-id=CPU]/output/"
                            "queues/queue[name=$0]/state/transmit-pkts",
                            queue.name())),
        _ << "Failed to query transmit-pkts for CPU queue " << queue.name());
    openconfig::Queues::Queue::State state;
    ASSIGN_OR_RETURN(*state.mutable_transmit_pkts(),
                     ParseJsonValue(transmitted_packets));
    queues_by_name.mutable_queues()->insert({queue.name(), state});
  }

  return queues_by_name;
}

// Return the name of each queue with a difference in transmitted packets.
// Only returns queues that are present in both snapshots.
absl::flat_hash_set<std::string> QueuesWithTransmittedPacketDifferences(
    const openconfig::QueuesByName &snapshot1,
    const openconfig::QueuesByName &snapshot2) {
  absl::flat_hash_set<std::string> diff_queues;
  for (const auto &[name, state] : snapshot2.queues()) {
    auto queue1 = snapshot1.queues().find(name);
    if (queue1 == snapshot1.queues().end()) continue;
    if (queue1->second.transmit_pkts() != state.transmit_pkts()) {
      diff_queues.insert(name);
    }
  }
  return diff_queues;
}

void EraseQueuesFromSnapshot(const absl::flat_hash_set<std::string> &queues,
                             openconfig::QueuesByName &snapshot) {
  for (const auto &queue : queues) snapshot.mutable_queues()->erase(queue);
}

// Not all CPU queues reported by the switch are valid. Return true if the queue
// is usable.
bool IsValidCpuQueue(absl::string_view queue_name) {
  return !absl::StartsWith(queue_name, "CPU:");
}

absl::Status InstallAclEntriesToFilterOutUnsolicitedPackets(
    p4_runtime::P4RuntimeSession &sut_p4rt_session) {
  // TODO: Uncomment when acl_deny is supported by the
  // switch and acl_ingress_table.
  // return pdpi::InstallPdTableEntries<sai::TableEntries>(
  //     sut_p4rt_session,
  //     R"pb(
  //       entries {
  //         acl_ingress_table_entry {
  //           priority: 1
  //           match { ether_type { value: "0x8809" mask: "0xffff" } }
  //           action { acl_deny {} }
  //         }
  //       }
  //     )pb");
  return absl::OkStatus();
}

// Increment the number of transmitted packets in the queue state proto by the
// specified amount.
absl::Status IncrementTransmittedPackets(
    openconfig::Queues::Queue::State &state, int packets) {
  int initial_packet_count;
  if (!absl::SimpleAtoi(state.transmit_pkts(), &initial_packet_count)) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Cannot increment non-integer transmitted packet count for queue "
           << "with state: " << state.ShortDebugString() << ".";
  }
  state.set_transmit_pkts(absl::StrCat(initial_packet_count + packets));
  return absl::OkStatus();
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

  // Configure mirror testbed.
  EXPECT_OK(
      Testbed().Environment().StoreTestArtifact("p4info.textproto", p4info));
  std::unique_ptr<p4_runtime::P4RuntimeSession> sut_p4rt_session,
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

  // Install ACL table entry to drop broadcast packets from Control to avoid
  // broadcast storm.
  ASSERT_OK_AND_ASSIGN(
      const sai::TableEntry pd_broadcast_drop_entry,
      gutil::ParseTextProto<sai::TableEntry>(R"pb(
        acl_ingress_table_entry {
          priority: 1
          match {
            dst_mac { value: "ff:ff:ff:ff:ff:ff" mask: "ff:ff:ff:ff:ff:ff" }
          }
          action { acl_drop {} }
        }
      )pb"));

  ASSERT_OK_AND_ASSIGN(const p4::v1::TableEntry pi_drop_entry,
                       pdpi::PartialPdTableEntryToPiTableEntry(
                           ir_p4info, pd_broadcast_drop_entry));

  ASSERT_OK(p4_runtime::InstallPiTableEntry(control_p4rt_session.get(),
                                            pi_drop_entry));

  // Read CPU queue state prior to injecting test packets. The state should
  // remain unchanged when we inject test packets.
  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, sut.CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(openconfig::QueuesByName initial_cpu_queue_state,
                       GetCpuQueueStateViaGnmi(*gnmi_stub));

  // Get a list of queues with passive traffic to exclude from this test.
  absl::SleepFor(absl::Seconds(10));
  ASSERT_OK_AND_ASSIGN(openconfig::QueuesByName passive_cpu_queue_state,
                       GetCpuQueueStateViaGnmi(*gnmi_stub));
  absl::flat_hash_set<std::string> excluded_queues =
      QueuesWithTransmittedPacketDifferences(initial_cpu_queue_state,
                                             passive_cpu_queue_state);
  LOG(INFO) << "Skipping queues due to passive traffic: "
            << absl::StrJoin(excluded_queues, ", ");
  EraseQueuesFromSnapshot(excluded_queues, initial_cpu_queue_state);
  ASSERT_FALSE(initial_cpu_queue_state.queues().empty());

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
    EraseQueuesFromSnapshot(excluded_queues, cpu_queue_state);
    EXPECT_THAT(cpu_queue_state, EqualsProto(initial_cpu_queue_state))
        << "for injected test packet: " << packet.DebugString();
    initial_cpu_queue_state = cpu_queue_state;
  }

  // Ensure that the switch did not punt packets to the controller via P4RT.
  ASSERT_OK_AND_ASSIGN(std::vector<p4::v1::StreamMessageResponse> pi_responses,
                       sut_p4rt_session->ReadStreamChannelResponsesAndFinish());
  for (const auto &pi_response : pi_responses) {
    sai::PacketIn pd_packet;
    EXPECT_OK(pdpi::PiPacketInToPd(ir_p4info, pi_response.packet(), &pd_packet))
        << "where packet = " << pi_response.packet().DebugString();
    ADD_FAILURE() << "SUT punted the following packet to the controller "
                     "via P4Runtime: "
                  << (pd_packet.ByteSizeLong() == 0  // Translation failed.
                          ? pi_response.packet().DebugString()
                          : pd_packet.DebugString());
  }

  LOG(INFO) << "-- END OF TEST -----------------------------------------------";
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
  std::unique_ptr<p4_runtime::P4RuntimeSession> sut_p4rt_session,
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
  ASSERT_OK_AND_ASSIGN(
      const p4::v1::TableEntry pi_acl_entry,
      pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, pd_acl_entry));
  ASSERT_OK(
      p4_runtime::InstallPiTableEntry(sut_p4rt_session.get(), pi_acl_entry));

  // Check that the counters are initially zero.
  ASSERT_THAT(
      p4_runtime::ReadPiCounterData(sut_p4rt_session.get(), pi_acl_entry),
      IsOkAndHolds(EqualsProto(R"pb(byte_count: 0 packet_count: 0)pb")));

  if (GetParam().nsf_reboot && GetParam().ssh_client_for_nsf) {
    ASSERT_OK(NsfRebootHelper(&Testbed(), GetParam().ssh_client_for_nsf));
  } else if (GetParam().nsf_reboot && !GetParam().ssh_client_for_nsf) {
    FAIL() << "ssh_client parameter needed for NSF Reboot is not provided";
  }

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
        p4_runtime::ReadPiCounterData(sut_p4rt_session.get(), pi_acl_entry));
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
  std::unique_ptr<p4_runtime::P4RuntimeSession> sut_p4rt_session,
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
  ASSERT_OK_AND_ASSIGN(
      packetlib::Packet ipv4_packet,
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

  ASSERT_OK_AND_ASSIGN(
      packetlib::Packet ipv6_packet,
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
  ASSERT_OK_AND_ASSIGN(
      const sai::TableEntry pd_acl_entry,
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
  ASSERT_OK(
      p4_runtime::InstallPiTableEntry(sut_p4rt_session.get(), pi_acl_entry));

  if (GetParam().nsf_reboot && GetParam().ssh_client_for_nsf) {
    ASSERT_OK(NsfRebootHelper(&Testbed(), GetParam().ssh_client_for_nsf));
  } else if (GetParam().nsf_reboot && !GetParam().ssh_client_for_nsf) {
    FAIL() << "ssh_client parameter needed for NSF Reboot is not provided";
  }

  for (packetlib::Packet &test_packet : test_packets) {
    // Start from fresh P4RT session.
    ASSERT_OK_AND_ASSIGN(sut_p4rt_session,
                         p4_runtime::P4RuntimeSession::Create(sut));

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
          /*packet_delay=*/absl::Milliseconds(10)));
    }

    EXPECT_OK(sut_p4rt_session->HandleNextNStreamMessages(
        [&](const p4::v1::StreamMessageResponse &message) {
          if (!message.has_packet()) return false;
          packetlib::Packet punted_packet =
              packetlib::ParsePacket(message.packet().payload());
          if (!testing::Matches(EqualsProto(test_packet))(punted_packet)) {
            LOG(WARNING) << "Received unknown packet: "
                         << punted_packet.ShortDebugString();
            return false;
          }
          return true;
        },
        kPacketCount, absl::Minutes(2)));
  }
  LOG(INFO) << "-- END OF TEST -----------------------------------------------";
}

// Purpose: Verify protocol-to-queue mapping for traffic to switch.
TEST_P(CpuQosTestWithoutIxia, TrafficToSwitchInbandGetsMappedToCorrectQueues) {
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
  std::unique_ptr<p4_runtime::P4RuntimeSession> sut_p4rt_session,
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
      GetParam().test_packet_generator_function(
          sut_gnmi_config, absl::GetFlag(FLAGS_switch_instantiation));

  ASSERT_FALSE(test_packets.empty())
      << "No packets to test, maybe no loopback IP is configured on switch?";

  // Clear table entries and install l3 admit entry.
  ASSERT_OK(p4_runtime::ClearEntities(*sut_p4rt_session));
  absl::flat_hash_set<std::string> added_dst_mac;
  for (const PacketAndExpectedTargetQueue &test_packet : test_packets) {
    std::string_view target_queue = test_packet.target_queue;
    SCOPED_TRACE(absl::StrCat("Packet: ", test_packet.packet_name,
                              ", Target queue: ", target_queue));
    LOG(INFO) << absl::StrCat("Packet: ", test_packet.packet_name,
                              ", Target queue: ", target_queue);

    ASSERT_GT(test_packet.packet.headers().size(), 0);
    ASSERT_TRUE(test_packet.packet.headers(0).has_ethernet_header());
    LOG(INFO) << "Packet dst mac: "
              << test_packet.packet.headers(0)
                     .ethernet_header()
                     .ethernet_destination();

    // Install l3 admit entry only once per dst mac.
    if (!added_dst_mac.contains(test_packet.packet.headers(0)
                                    .ethernet_header()
                                    .ethernet_destination())) {
      LOG(INFO) << "Installing l3 admit entry for "
                << test_packet.packet.headers(0)
                       .ethernet_header()
                       .ethernet_destination();
      ASSERT_OK(p4_runtime::InstallPdTableEntry<sai::TableEntry>(
          *sut_p4rt_session,
          absl::Substitute(
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
      added_dst_mac.insert(test_packet.packet.headers(0)
                               .ethernet_header()
                               .ethernet_destination());
    }
    // Certain unsolicited packets may be sent, which should be filtered out
    // before evaluating queues.
    ASSERT_OK(
        InstallAclEntriesToFilterOutUnsolicitedPackets(*sut_p4rt_session));
  }

  if (GetParam().nsf_reboot && GetParam().ssh_client_for_nsf) {
    ASSERT_OK(NsfRebootHelper(&Testbed(), GetParam().ssh_client_for_nsf));
  } else if (GetParam().nsf_reboot && !GetParam().ssh_client_for_nsf) {
    FAIL() << "ssh_client parameter needed for NSF Reboot is not provided";
  }

  for (const PacketAndExpectedTargetQueue &test_packet : test_packets) {
    std::string_view target_queue = test_packet.target_queue;
    SCOPED_TRACE(absl::StrCat("Packet: ", test_packet.packet_name,
                              ", Target queue: ", target_queue));
    LOG(INFO) << absl::StrCat("Packet: ", test_packet.packet_name,
                              ", Target queue: ", target_queue);

    // Read counters of the target queue.
    ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());
    ASSERT_OK_AND_ASSIGN(
        const QueueCounters queue_counters_before_test_packet,
        GetGnmiQueueCounters(/*port=*/"CPU", /*queue=*/target_queue,
                             *sut_gnmi_stub));

    ASSERT_OK_AND_ASSIGN(std::string raw_packet,
                         packetlib::SerializePacket(test_packet.packet));

    // TODO: Disallow unsolicited packets once they can be filtered
    // out correctly.
    constexpr int kMaxAllowedUnsolicitedPackets = 100;
    // High to ensure we get good signal compared to the number of allowed
    // unsolicited packets.
    const int kPacketCount = 1000;
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

    int expected_queue_counters_after_test_packets =
        TotalPacketsForQueue(queue_counters_before_test_packet) + kPacketCount;

    // We terminate early if this fails, as that can cause this loop to get
    // out of sync when counters increment after a long delay, resulting in
    // confusing error messages where counters increment by 2.
    EXPECT_THAT(TotalPacketsForQueue(queue_counters_after_test_packet),
                AllOf(Ge(expected_queue_counters_after_test_packets),
                      Le(expected_queue_counters_after_test_packets +
                         kMaxAllowedUnsolicitedPackets)))
        << "Counters for queue " << target_queue << " did not increment within "
        << kMaxQueueCounterUpdateTime
        << " after injecting the following test packet or had too many "
           "unsolicited packets:\n"
        << test_packet.packet.DebugString()
        << "\nBefore  : " << queue_counters_before_test_packet
        << "\nAfter   : " << queue_counters_after_test_packet
        << "\nExpected: " << expected_queue_counters_after_test_packets
        << " to "
        << expected_queue_counters_after_test_packets +
               kMaxAllowedUnsolicitedPackets;
  }
  LOG(INFO) << "-- END OF TEST -----------------------------------------------";
}

// Ensure that P4 CPU Queue name references the intended CPU Queue.
TEST_P(CpuQosTestWithoutIxia, P4CpuQueueMappingByNameIsCorrect) {
  struct QueueTest {
    int packets;                  // Number of packets to send to this Queue.
    netaddr::Ipv4Address dst_ip;  // Unique dest IP of packets to this Queue.
  };

  // Initialize and clear the SUT.
  const p4::config::v1::P4Info &p4info = GetParam().p4info;
  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info ir_p4info, pdpi::CreateIrP4Info(p4info));
  ASSERT_OK_AND_ASSIGN(auto p4info_version,
                       gutil::ParseVersion(p4info.pkg_info().version()));
  if (p4info_version <
      *gutil::ParseVersion(SAI_P4_PKGINFO_VERSION_HAS_CPU_QUEUE_NAME_SUPPORT)) {
    GTEST_SKIP() << "P4Info version " << p4info.pkg_info().version()
                 << " is lower than the minimum supported version "
                 << SAI_P4_PKGINFO_VERSION_HAS_CPU_QUEUE_NAME_SUPPORT;
  }

  std::unique_ptr<p4_runtime::P4RuntimeSession> sut_p4rt_session,
      control_p4rt_session;
  ASSERT_OK_AND_ASSIGN(
      std::tie(sut_p4rt_session, control_p4rt_session),
      pins_test::ConfigureSwitchPairAndReturnP4RuntimeSessionPair(
          Sut(), ControlSwitch(), GetParam().gnmi_config, p4info));

  // Pick a link to be used for packet injection.
  ASSERT_OK_AND_ASSIGN(SutToControlLink link_used_for_test_packets,
                       PickSutToControlDeviceLinkThatsUp(Testbed()));
  LOG(INFO) << "Link used to inject test packets: "
            << link_used_for_test_packets;

  // Find all queues and initialize the test conditions for each.
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, Sut().CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(openconfig::QueuesByName initial_state,
                       GetCpuQueueStateViaGnmi(*sut_gnmi_stub));

  // Search for and remove queues that have passive traffic.
  absl::SleepFor(absl::Seconds(10));
  ASSERT_OK_AND_ASSIGN(openconfig::QueuesByName passive_state,
                       GetCpuQueueStateViaGnmi(*sut_gnmi_stub));
  absl::flat_hash_set<std::string> excluded_queues =
      QueuesWithTransmittedPacketDifferences(initial_state, passive_state);
  LOG(INFO) << "Skipping queues due to passive traffic: "
            << absl::StrJoin(excluded_queues, ", ");
  EraseQueuesFromSnapshot(excluded_queues, initial_state);

  for (const auto &[name, state] : passive_state.queues()) {
    if (initial_state.queues().contains(name) &&
        initial_state.queues().at(name).transmit_pkts() <
            state.transmit_pkts()) {
      LOG(INFO) << "Skipping Queue '" << name
                << "' due to presence of passive traffic.";
      initial_state.mutable_queues()->erase(name);
    }
  }

  // Set up unique IP & packet counts to send to each queue.
  absl::flat_hash_map<std::string, QueueTest> test_cases;
  constexpr uint32_t kBaseIp = 0x0A000000;  // 10.0.0.0
  constexpr int kBasePackets = 10;
  int queue_index = 0;
  for (const auto &[name, state] : initial_state.queues()) {
    if (!IsValidCpuQueue(name)) continue;
    if (absl::StartsWith(name, "INBAND_")) continue;
    test_cases[name] = QueueTest({
        .packets = kBasePackets + queue_index,
        .dst_ip = netaddr::Ipv4Address(std::bitset<32>(kBaseIp + queue_index)),
    });
    ++queue_index;
  }
  ASSERT_FALSE(test_cases.empty());

  // Set up the switch dataplane with the CPU Queue name.
  constexpr netaddr::MacAddress kDestMac(std::bitset<48>(0x0A0000000000));
  for (const auto &[queue, setup] : test_cases) {
    ASSERT_OK(SetUpPuntToCPU(kDestMac, setup.dst_ip, queue, ir_p4info,
                             *sut_p4rt_session));
  }

  if (GetParam().nsf_reboot && GetParam().ssh_client_for_nsf) {
    ASSERT_OK(NsfRebootHelper(&Testbed(), GetParam().ssh_client_for_nsf));
    // Create a new P4rt session after NSF Reboot
    ASSERT_OK_AND_ASSIGN(sut_p4rt_session,
                         p4_runtime::P4RuntimeSession::Create(Sut()));
    // Reset initial state of queues after NSF Reboot
    ASSERT_OK_AND_ASSIGN(initial_state,
                         GetCpuQueueStateViaGnmi(*sut_gnmi_stub));
  } else if (GetParam().nsf_reboot && !GetParam().ssh_client_for_nsf) {
    FAIL() << "ssh_client parameter needed for NSF Reboot is not provided";
  }

  // Inject the test packets
  constexpr netaddr::Ipv4Address kSrcIp(std::bitset<32>(0x0B000000));
  for (const auto &[queue, setup] : test_cases) {
    packetlib::Packet packet =
        BuildPuntToCpuPacket(kDestMac, kSrcIp, setup.dst_ip);

    ASSERT_OK_AND_ASSIGN(std::string raw_packet,
                         packetlib::SerializePacket(packet));
    LOG(INFO) << "Injecting " << setup.packets << " packets into CPU Queue "
              << queue << ": " << packet.ShortDebugString();
    for (int i = 0; i < setup.packets; ++i) {
      EXPECT_OK(pins::InjectEgressPacket(
          link_used_for_test_packets.control_device_port_p4rt_name, raw_packet,
          ir_p4info, control_p4rt_session.get()))
          << "Failed to inject queue " << queue << " packet #" << i << ": "
          << packet.ShortDebugString();
    }
  }

  // Generate the expected state.
  openconfig::QueuesByName expected_state = initial_state;
  for (const auto &[queue, setup] : test_cases) {
    EXPECT_OK(IncrementTransmittedPackets(
        expected_state.mutable_queues()->at(queue), setup.packets));
  }

  // Wait for the expected state.
  absl::Time start = absl::Now();
  openconfig::QueuesByName results;
  do {
    absl::SleepFor(absl::Seconds(5));
    ASSERT_OK_AND_ASSIGN(results, GetCpuQueueStateViaGnmi(*sut_gnmi_stub));
    EraseQueuesFromSnapshot(excluded_queues, results);
  } while (absl::Now() - start < kMaxQueueCounterUpdateTime &&
           !testing::Matches(EqualsProto(expected_state))(results));
  EXPECT_THAT(results, EqualsProto(expected_state));

  // Throw away the PacketIn events.
  ASSERT_OK_AND_ASSIGN(std::vector<p4::v1::StreamMessageResponse> pi_responses,
                       sut_p4rt_session->ReadStreamChannelResponsesAndFinish());
}

// Buffering and software bottlenecks can cause
// some amount of variance in rate measured end to end.
// Level of tolerance for packet rate verification.
// This could be parameterized in future if this is platform
// dependent.
constexpr float kTolerancePercent = 10.0;
constexpr float kMeterCounterTolerance = 5.0;

// Ixia configurations:
// 1. Frames sent per second by Ixia.
// 2. Total frames sent by Ixia.
// 3. Default frame size.
// 4. Maximum frame size.
// 5. Minimum frame size.
constexpr int kFramesPerSecond = 1000000;
constexpr int kTotalFrames = 30000000;
constexpr absl::Duration kTrafficDuration =
    absl::Seconds(kTotalFrames / kFramesPerSecond);
constexpr int kDefaultFrameSize = 1514;
constexpr int kMaxFrameSize = 9216;
constexpr int kVlanTagSize = 4;
constexpr int kMaxFrameSizeWithoutVlanTag = kMaxFrameSize - kVlanTagSize;
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
    if (info.interface_modes.contains(thinkit::TRAFFIC_GENERATOR)) {
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
                 interface_mode: TRAFFIC_GENERATOR
               })pb");

  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<thinkit::GenericTestbed> generic_testbed,
      GetParam().testbed_interface->GetTestbedWithRequirements(requirements));

  ASSERT_GT(GetParam().control_plane_bandwidth_bytes_per_second, 0);

  thinkit::Switch &sut = generic_testbed->Sut();

  // Configure SUT.
  EXPECT_OK(generic_testbed->Environment().StoreTestArtifact(
      "p4info.textproto", GetParam().p4info));
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<p4_runtime::P4RuntimeSession> sut_p4_session,
      pins_test::ConfigureSwitchAndReturnP4RuntimeSession(sut, std::nullopt,
                                                          GetParam().p4info));
  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, sut.CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(std::string sut_gnmi_config,
                       pins_test::GetGnmiConfig(*gnmi_stub));
  EXPECT_OK(generic_testbed->Environment().StoreTestArtifact("gnmi_config.json",
                                                             sut_gnmi_config));
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

  // Get Queues.
  ASSERT_OK_AND_ASSIGN(auto queues, ExtractQueueInfoViaGnmiConfig(
                                        /*port=*/"CPU", sut_gnmi_config));

  constexpr absl::string_view kPuntOnlyTest = "punt_only_test";
  constexpr absl::string_view kLoopbackPuntTest = "to_loopback_punt_test";
  constexpr absl::string_view kPuntTtl0Test = "ttl0_punt_test";

  if (GetParam().nsf_reboot && GetParam().ssh_client_for_nsf) {
    ASSERT_OK(
        NsfRebootHelper(generic_testbed.get(), GetParam().ssh_client_for_nsf));
    // Create a new P4rt session after NSF Reboot
    ASSERT_OK_AND_ASSIGN(sut_p4_session,
                         p4_runtime::P4RuntimeSession::Create(sut));
  } else if (GetParam().nsf_reboot && !GetParam().ssh_client_for_nsf) {
    FAIL() << "ssh_client parameter needed for NSF Reboot is not provided";
  }

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

  for (auto test_case : {kPuntOnlyTest, kPuntTtl0Test}) {
    LOG(INFO) << "\n\nTesting case: " << test_case;
    LOG(INFO) << "\n===================\n\n";
    if (test_case == kLoopbackPuntTest) {
      ASSERT_OK(pins_test::ixia::SetDestIPv6(
          traffic_ref, loopback_ipv6.front().ToString(), *generic_testbed));
      LOG(INFO) << "Traffic to Loopback IP: "
                << loopback_ipv6.front().ToString();
    } else if (test_case == kPuntTtl0Test) {
      ASSERT_OK(pins_test::ixia::SetIpTTL(traffic_ref, /*ttl=*/0,
                                          /*is_ipv4=*/false, *generic_testbed));
      LOG(INFO) << "Traffic with TTL=0";
    }

    for (auto &[queue_name, queue_info] : queues) {
      // Skip unconfigured queues.
      if (queue_info.rate_packets_per_second == 0) {
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

      // Set frame size based on supported control plane bandwidth.
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
      // Punt flows to Inband queues should not succeed.
      if (absl::StartsWith(queue_info.p4_queue_name, "INBAND")) {
        // PKTIO queues.
        if (!generic_testbed->Environment().MaskKnownFailures()) {
          ASSERT_FALSE(
              SetUpV6PuntToCPUWithRateLimitAndWildCardL3AdmitEntry(
                  dest_mac, source_ip, dest_ip,
                  /*rate_bytes_per_second=*/
                  (queue_info.rate_packets_per_second + 10) * frame_size,
                  /*burst_in_bytes=*/(queue_info.rate_packets_per_second + 10) *
                      frame_size / 4,
                  queue_info.p4_queue_name, GetParam().p4info, *sut_p4_session)
                  .ok());
        }
        continue;
      }
      // Punt packets to CPU with flow rate set to at least 10 packets
      // higher than the queue rate. This means that the queue limits will
      // be the bottleneck.
      ASSERT_OK(SetUpV6PuntToCPUWithRateLimitAndWildCardL3AdmitEntry(
          dest_mac, source_ip, dest_ip,
          /*rate_bytes_per_second=*/(queue_info.rate_packets_per_second + 10) *
              frame_size,
          /*burst_in_bytes=*/(queue_info.rate_packets_per_second + 10) *
              frame_size,
          queue_info.p4_queue_name, GetParam().p4info, *sut_p4_session));
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
      static constexpr absl::Duration kTotalTime = absl::Seconds(25);
      static const int kIterations = kTotalTime / kPollInterval;

      QueueCounters final_counters;
      QueueCounters delta_counters;
      // Check for counters every 5 seconds up to 15 seconds till they match.
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
    }  // for each queue.
  }  // test_case
  // Stop receiving at tester.
  receiver.Destroy();
}

TEST_P(CpuQosTestWithIxia, TestPuntFlowRateLimitAndCounters) {
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

  ASSERT_GT(GetParam().control_plane_bandwidth_bytes_per_second, 0);

  thinkit::Switch &sut = generic_testbed->Sut();

  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, sut.CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(std::string sut_gnmi_config,
                       pins_test::GetGnmiConfig(*gnmi_stub));
  EXPECT_OK(generic_testbed->Environment().StoreTestArtifact("gnmi_config.json",
                                                             sut_gnmi_config));
  EXPECT_OK(generic_testbed->Environment().StoreTestArtifact(
      "p4info.textproto", GetParam().p4info));
  // Configure SUT.
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<p4_runtime::P4RuntimeSession> sut_p4_session,
      pins_test::ConfigureSwitchAndReturnP4RuntimeSession(sut, std::nullopt,
                                                          GetParam().p4info));

  // Disable sFlow since it would interfere with the test results.
  ASSERT_OK(pins::SetSflowConfigEnabled(gnmi_stub.get(), /*enabled=*/false));

  absl::Cleanup cleanup([&] {
    // Restore sflow enable config.
    ASSERT_OK_AND_ASSIGN(bool sflow_enabled,
                         pins::IsSflowConfigEnabled(sut_gnmi_config));
    EXPECT_OK(pins::SetSflowConfigEnabled(gnmi_stub.get(), sflow_enabled))
        << "failed to restore sflow configuration -- switch config may be "
           "corrupted, causing subsequent test to fail";
  });

  // Flow details.
  const auto dest_mac = netaddr::MacAddress(02, 02, 02, 02, 02, 02);
  const auto source_mac = netaddr::MacAddress(00, 01, 02, 03, 04, 05);
  const auto source_ip = netaddr::Ipv4Address(192, 168, 10, 1);
  const auto dest_ip = netaddr::Ipv4Address(172, 0, 0, 1);

  const absl::flat_hash_map<std::string, thinkit::InterfaceInfo>
      interface_info = generic_testbed->GetSutInterfaceInfo();

  ASSERT_OK_AND_ASSIGN(std::vector<IxiaLink> ready_links,
                       GetReadyIxiaLinks(*generic_testbed, *gnmi_stub));

  ASSERT_FALSE(ready_links.empty());

  std::string ixia_interface = ready_links[0].ixia_interface;
  std::string sut_interface = ready_links[0].sut_interface;
  std::string ixia_rx_interface = ready_links[1].ixia_interface;
  std::string sut_egress_interface = ready_links[1].sut_interface;

  LOG(INFO) << absl::StrFormat(
      "Test packet route: [Ixia: %s] => [SUT: %s] -> [SUT: %s] => [Ixia: %s]",
      ixia_interface, sut_interface, sut_egress_interface, ixia_rx_interface);

  absl::flat_hash_map<std::string, std::string> p4rt_id_by_interface;
  ASSERT_OK_AND_ASSIGN(p4rt_id_by_interface,
                       GetAllInterfaceNameToPortId(*gnmi_stub));
  ASSERT_OK_AND_ASSIGN(
      const std::string kSutEgressPortP4rtId,
      gutil::FindOrStatus(p4rt_id_by_interface, sut_egress_interface));

  // We will perform the following steps with Ixia:
  // Set up Ixia traffic.
  // Send Ixia traffic.
  // Stop Ixia traffic.

  ASSERT_OK_AND_ASSIGN(ixia::IxiaPortInfo ixia_port,
                       ixia::ExtractPortInfo(ixia_interface));

  ASSERT_OK_AND_ASSIGN(ixia::IxiaPortInfo ixia_rx_port,
                       ixia::ExtractPortInfo(ixia_rx_interface));

  ASSERT_OK_AND_ASSIGN(
      std::string kIxiaHandle,
      pins_test::ixia::IxiaConnect(ixia_port.hostname, *generic_testbed));

  ASSERT_OK_AND_ASSIGN(
      std::string kIxiaSrcPortHandle,
      pins_test::ixia::IxiaVport(kIxiaHandle, ixia_port.card, ixia_port.port,
                                 *generic_testbed));

  ASSERT_OK_AND_ASSIGN(
      std::string kIxiaDstPortHandle,
      pins_test::ixia::IxiaVport(kIxiaHandle, ixia_rx_port.card,
                                 ixia_rx_port.port, *generic_testbed));

  const std::string kTrafficName = "cpu_qos_test_ixia_traffic";
  ASSERT_OK_AND_ASSIGN(
      const std::string kIxiaTrafficHandle,
      ixia::SetUpTrafficItem(kIxiaSrcPortHandle, kIxiaDstPortHandle,
                             kTrafficName, *generic_testbed));
  auto delete_traffic_item = absl::Cleanup([&, kIxiaTrafficHandle] {
    ASSERT_OK(ixia::DeleteTrafficItem(kIxiaTrafficHandle, *generic_testbed));
  });

  auto traffic_parameters = ixia::TrafficParameters{
      .frame_count = kTotalFrames,
      .frame_size_in_bytes = kMaxFrameSizeWithoutVlanTag,
      .traffic_speed = ixia::FramesPerSecond{kFramesPerSecond},
      .src_mac = source_mac,
      .dst_mac = dest_mac,
      .ip_parameters = ixia::Ipv4TrafficParameters{
          .src_ipv4 = source_ip,
          .dst_ipv4 = dest_ip,
          // Set ECN 0 to avoid RED drops.
          .priority = ixia::IpPriority{.dscp = 0, .ecn = 0},
      }};

  // Get Queues.
  ASSERT_OK_AND_ASSIGN(auto queues, ExtractQueueInfoViaGnmiConfig(
                                        /*port=*/"CPU", sut_gnmi_config));
  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(GetParam().p4info));
  ASSERT_OK_AND_ASSIGN(std::vector<p4::v1::Entity> entities,
                       sai::EntryBuilder()
                           .AddEntriesForwardingIpPacketsToGivenPort(
                               /*egress_port=*/kSutEgressPortP4rtId,
                               /*ip_version=*/sai::IpVersion::kIpv4And6,
                               /*rewrite_options*/ kNextHopRewriteOptions)
                           .LogPdEntries()
                           .GetDedupedPiEntities(ir_p4info));

  bool has_acl_qos_table =
      ir_p4info.tables_by_name().contains(kAclIngressQosTable);

  if (GetParam().nsf_reboot && GetParam().ssh_client_for_nsf) {
    ASSERT_OK(
        NsfRebootHelper(generic_testbed.get(), GetParam().ssh_client_for_nsf));
    // Create a new P4rt session after NSF Reboot
    ASSERT_OK_AND_ASSIGN(sut_p4_session,
                         p4_runtime::P4RuntimeSession::Create(sut));
  } else if (GetParam().nsf_reboot && !GetParam().ssh_client_for_nsf) {
    FAIL() << "ssh_client parameter needed for NSF Reboot is not provided";
  }

  // Listen for punted packets from the SUT.
  PacketReceiveInfo packet_receive_info;
  {
    absl::MutexLock lock(&packet_receive_info.mutex);
    packet_receive_info.num_packets_punted = 0;
  }

  PacketInReceiver receiver(*sut_p4_session, [&packet_receive_info](auto) {
    absl::MutexLock lock(&packet_receive_info.mutex);
    if (packet_receive_info.num_packets_punted == 0) {
      packet_receive_info.time_first_packet_punted = absl::Now();
    }
    packet_receive_info.time_last_packet_punted = absl::Now();
    packet_receive_info.num_packets_punted++;
    return;
  });

  for (auto &[queue_name, queue_info] : queues) {
    // Skip unconfigured queues or queues with very low rate-limit as it is not
    // feasible to verify flow rate limit at low queue rates.
    if (queue_info.rate_packets_per_second <= 10) {
      continue;
    }
    // Lets set flow rate limit to be half of queue limit so that queue limit
    // doesn't take effect.
    int flow_rate_limit_in_bytes_per_second =
        (kMaxFrameSizeWithoutVlanTag * queue_info.rate_packets_per_second) / 2;

    if (flow_rate_limit_in_bytes_per_second >
        GetParam().control_plane_bandwidth_bytes_per_second) {
      flow_rate_limit_in_bytes_per_second =
          GetParam().control_plane_bandwidth_bytes_per_second / 2;
    }

    for (auto acl_table_punt_action :
         GetParam().acl_ingress_table_punt_flow_rate_limit_actions) {
      if (acl_table_punt_action.rate_limit_action == kAclTrap ||
          acl_table_punt_action.rate_limit_action == kAclCopy) {
      } else if (acl_table_punt_action.rate_limit_action ==
                 kAclSetCpuQueueAndDenyAboveRateLimit) {
      }

      // Skip ACL "Ingress table" rate limit actions if switch supports
      // ACL "Ingress QoS table".
      if (has_acl_qos_table == true &&
          (acl_table_punt_action.rate_limit_action == kAclTrap ||
           acl_table_punt_action.rate_limit_action == kAclCopy)) {
        LOG(INFO) << "Skipping " << kAclIngressTable << " action "
                  << acl_table_punt_action.rate_limit_action
                  << " as switch has " << kAclIngressQosTable;
        continue;
      }
      // Skip ACL "Ingress QoS table" rate limit actions if switch does not
      // support ACL "Ingress QoS table".
      if (has_acl_qos_table == false &&
          (acl_table_punt_action.rate_limit_action ==
               kAclSetCpuQueueAndCancelCopyAboveRateLimit ||
           acl_table_punt_action.rate_limit_action ==
               kAclSetCpuQueueAndDenyAboveRateLimit ||
           acl_table_punt_action.rate_limit_action ==
               kAclSetCpuQueueMulticastQueueAndDenyAboveRateLimit)) {
        LOG(INFO) << "Skipping action as rate limit action is part of "
                  << pins_test::kAclIngressTable;
        continue;
      }

      // Punt flows to Inband queues should not succeed.
      if (absl::StartsWith(queue_info.p4_queue_name, "INBAND")) {
        // PKTIO queues.
        if (!generic_testbed->Environment().MaskKnownFailures()) {
          ASSERT_FALSE(
              (SetUpPuntToCPUWithRateLimit(
                   dest_mac, dest_ip, queue_info.p4_queue_name,
                   flow_rate_limit_in_bytes_per_second,
                   /*burst_in_bytes=*/kMaxFrameSizeWithoutVlanTag,
                   acl_table_punt_action, GetParam().p4info, *sut_p4_session)
                   .ok()));
        }
        continue;
      }

      LOG(INFO) << "\n\n\nTesting Queue : " << queue_info.gnmi_queue_name
                << ", acl_qos_table_action: "
                << acl_table_punt_action.rate_limit_action
                << "\n===================\n\n\n";

      ASSERT_OK_AND_ASSIGN(
          p4::v1::TableEntry pi_acl_entry,
          SetUpPuntToCPUWithRateLimit(
              dest_mac, dest_ip, queue_info.p4_queue_name,
              flow_rate_limit_in_bytes_per_second,
              /*burst_in_bytes=*/kMaxFrameSizeWithoutVlanTag,
              acl_table_punt_action, GetParam().p4info, *sut_p4_session));
      ASSERT_OK(p4_runtime::InstallPiEntities(sut_p4_session.get(), ir_p4info,
                                              entities));
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
          p4_runtime::ReadPiCounterData(sut_p4_session.get(), pi_acl_entry),
          IsOkAndHolds(EqualsProto(R"pb(byte_count: 0 packet_count: 0)pb")));
      if (pi_acl_entry.has_meter_config()) {
        EXPECT_OK(p4_runtime::ReadPiMeterCounterData(sut_p4_session.get(),
                                                     pi_acl_entry));
      }

      ASSERT_OK(ixia::SetTrafficParameters(
          kIxiaTrafficHandle, traffic_parameters, *generic_testbed));

      // Occasionally the Ixia API cannot keep up and starting traffic fails,
      // so we try up to 3 times.
      ASSERT_OK(pins::TryUpToNTimes(3, /*delay=*/absl::Seconds(1), [&] {
        return ixia::StartTraffic(kIxiaTrafficHandle, kIxiaHandle,
                                  *generic_testbed);
      }));

      // Wait for Traffic to be sent.
      absl::SleepFor(kTrafficDuration);

      // Check for counters every 5 seconds up to 30 seconds till the fetched
      // gNMI queue counter stats match packets and bytes sent by Ixia. Check
      // that the counters increment within kMaxQueueCounterUpdateTime.
      absl::Time time_packet_sent = absl::Now();
      p4::v1::CounterData counter_data;
      do {
        ASSERT_OK_AND_ASSIGN(
            counter_data,
            p4_runtime::ReadPiCounterData(sut_p4_session.get(), pi_acl_entry));
      } while (counter_data.packet_count() != kTotalFrames &&
               absl::Now() - time_packet_sent < kMaxQueueCounterUpdateTime);
      p4::v1::CounterData expected_counter_data;
      expected_counter_data.set_packet_count(kTotalFrames);
      expected_counter_data.set_byte_count(
          static_cast<int64_t>(kMaxFrameSizeWithoutVlanTag) *
          static_cast<int64_t>(kTotalFrames));
      EXPECT_GE(
          counter_data.packet_count(),
          expected_counter_data.packet_count() * (1 - kTolerancePercent / 100))
          << "Packet count for the table entry given below did not match "
             "expectation "
             "within "
          << kMaxQueueCounterUpdateTime
          << " after injecting the Ixia test packets via CPU queue "
          << queue_name;

      EXPECT_GE(counter_data.byte_count(), expected_counter_data.byte_count() *
                                               (1 - kTolerancePercent / 100))
          << "Byte count for the table entry given below did not match "
             "expectation "
             "within "
          << kMaxQueueCounterUpdateTime
          << " after injecting the Ixia test packets via CPU queue "
          << queue_name;
      // Verify GNMI queue stats match packets received.
      static constexpr absl::Duration kPollInterval = absl::Seconds(5);
      static constexpr absl::Duration kTotalTime = absl::Seconds(20);
      static const int kIterations = kTotalTime / kPollInterval;

      // Check for counters every 5 seconds up to 20 seconds till they match.
      for (int gnmi_counters_check = 0; gnmi_counters_check < kIterations;
           gnmi_counters_check++) {
        absl::SleepFor(kPollInterval);
        QueueCounters final_counters;
        QueueCounters delta_counters;
        ASSERT_OK_AND_ASSIGN(
            final_counters, GetGnmiQueueCounters(
                                "CPU", queue_info.gnmi_queue_name, *gnmi_stub));
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
        LOG(INFO) << "Frame size: " << kMaxFrameSizeWithoutVlanTag;
        int64_t rate_received_in_bytes_per_second = 0;
        int64_t useconds = absl::ToInt64Microseconds(duration);
        ASSERT_NE(useconds, 0);
        int64_t num_bytes = packet_receive_info.num_packets_punted *
                            kMaxFrameSizeWithoutVlanTag;
        LOG(INFO) << "Num bytes received: " << num_bytes;
        rate_received_in_bytes_per_second = num_bytes * 1000000 / useconds;
        LOG(INFO) << "Rate of packets received (bytes per second): "
                  << rate_received_in_bytes_per_second;
        EXPECT_LE(rate_received_in_bytes_per_second,
                  flow_rate_limit_in_bytes_per_second *
                      (1 + kTolerancePercent / 100));
        EXPECT_GE(rate_received_in_bytes_per_second,
                  flow_rate_limit_in_bytes_per_second *
                      (1 - kTolerancePercent / 100));

        if (pi_acl_entry.has_meter_config()) {
          ASSERT_OK_AND_ASSIGN(p4::v1::MeterCounterData meter_counter_data,
                               p4_runtime::ReadPiMeterCounterData(
                                   sut_p4_session.get(), pi_acl_entry));
          LOG(INFO) << "Meter counter data: "
                    << meter_counter_data.DebugString();
          // With some tolerance, green packets should equal number of expected
          // receive packets based on the configured rate limit and red packets
          // should be the remainder of the total transmitted packets.
          int64_t expected_green_bytes =
              static_cast<int64_t>(flow_rate_limit_in_bytes_per_second) *
              useconds / 1000000;
          int64_t expected_green_packets =
              expected_green_bytes /
              static_cast<int64_t>(kMaxFrameSizeWithoutVlanTag);
          EXPECT_LE(
              meter_counter_data.green().packet_count(),
              expected_green_packets * (1 + kMeterCounterTolerance / 100));
          EXPECT_GE(
              meter_counter_data.green().packet_count(),
              expected_green_packets * (1 - kMeterCounterTolerance / 100));
          EXPECT_LE(meter_counter_data.green().byte_count(),
                    expected_green_bytes * (1 + kMeterCounterTolerance / 100));
          EXPECT_GE(meter_counter_data.green().byte_count(),
                    expected_green_bytes * (1 - kMeterCounterTolerance / 100));

          int64_t expected_red_packets =
              static_cast<int64_t>(kTotalFrames) - expected_green_packets;
          int64_t expected_red_bytes =
              static_cast<int64_t>(kTotalFrames) *
                  static_cast<int64_t>(kMaxFrameSizeWithoutVlanTag) -
              expected_green_bytes;
          EXPECT_LE(meter_counter_data.red().packet_count(),
                    expected_red_packets * (1 + kMeterCounterTolerance / 100));
          EXPECT_GE(meter_counter_data.red().packet_count(),
                    expected_red_packets * (1 - kMeterCounterTolerance / 100));
          EXPECT_LE(meter_counter_data.red().byte_count(),
                    expected_red_bytes * (1 + kMeterCounterTolerance / 100));
          EXPECT_GE(meter_counter_data.red().byte_count(),
                    expected_red_bytes * (1 - kMeterCounterTolerance / 100));
          // For trap action we do not expect any forwarding.
          if (acl_table_punt_action.rate_limit_action == kAclTrap) {
            ASSERT_OK_AND_ASSIGN(
                const ixia::TrafficItemStats kIxiaTrafficStats,
                ixia::GetTrafficItemStats(kIxiaHandle, kTrafficName,
                                          *generic_testbed));
            ASSERT_EQ(kIxiaTrafficStats.num_rx_frames(), 0);
            continue;
          }
          // Check observed traffic rate.
          ASSERT_OK_AND_ASSIGN(
              const ixia::TrafficItemStats kIxiaTrafficStats,
              ixia::GetTrafficItemStats(kIxiaHandle, kTrafficName,
                                        *generic_testbed));
          const int64_t kObservedTrafficRate =
              ixia::BytesPerSecondReceived(kIxiaTrafficStats);
          LOG(INFO) << "Rate of forwarded packets received (bytes per second): "
                    << kObservedTrafficRate;
          if (acl_table_punt_action.rate_limit_action ==
                  kAclSetCpuQueueAndDenyAboveRateLimit ||
              acl_table_punt_action.rate_limit_action ==
                  kAclSetCpuQueueMulticastQueueAndDenyAboveRateLimit) {
            // For "deny" actions verify that forwarded traffic does not
            // get impacted by the policer.
            EXPECT_LE(kObservedTrafficRate,
                      flow_rate_limit_in_bytes_per_second *
                          (1 + kTolerancePercent / 100));
            EXPECT_GE(kObservedTrafficRate,
                      flow_rate_limit_in_bytes_per_second *
                          (1 - kTolerancePercent / 100));
          } else {
            // For "CopyCancel" action verify that the rate limit applies to the
            // forwarded traffic also.
            EXPECT_LE(kObservedTrafficRate,
                      static_cast<int64_t>(kFramesPerSecond) *
                          kMaxFrameSizeWithoutVlanTag *
                          (1 + kTolerancePercent / 100));
            EXPECT_GE(kObservedTrafficRate,
                      static_cast<int64_t>(kFramesPerSecond) *
                          kMaxFrameSizeWithoutVlanTag *
                          (1 - kTolerancePercent / 100));
          }
        }
      }
    }
  }  // for each queue.

  // Stop receiving at tester.
  receiver.Destroy();
}

// Purpose: Verify that burst of packets sent within the queue buffer limit
// are transmitted by the queue, and excess packets get dropped.
TEST_P(CpuQosTestWithIxia, CpuQosBurstyTraffic) {
  LOG(INFO) << "-- START OF TEST ---------------------------------------------";

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


  ASSERT_GT(GetParam().control_plane_bandwidth_bytes_per_second, 0);

  thinkit::Switch &sut = generic_testbed->Sut();

  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, sut.CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(std::string sut_gnmi_config,
                       pins_test::GetGnmiConfig(*gnmi_stub));
  EXPECT_OK(generic_testbed->Environment().StoreTestArtifact("gnmi_config.json",
                                                             sut_gnmi_config));
  EXPECT_OK(generic_testbed->Environment().StoreTestArtifact(
      "p4info.txtpb", GetParam().p4info));
  ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(GetParam().p4info));
  // Configure SUT.
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<p4_runtime::P4RuntimeSession> sut_p4_session,
      pins_test::ConfigureSwitchAndReturnP4RuntimeSession(sut, std::nullopt,
                                                          GetParam().p4info));

  // Disable sFlow since it would interfere with the test results.
  ASSERT_OK(pins::SetSflowConfigEnabled(gnmi_stub.get(), /*enabled=*/false));

  absl::Cleanup cleanup([&] {
    // Restore sflow enable config.
    ASSERT_OK_AND_ASSIGN(bool sflow_enabled,
                         pins::IsSflowConfigEnabled(sut_gnmi_config));
    EXPECT_OK(pins::SetSflowConfigEnabled(gnmi_stub.get(), sflow_enabled))
        << "failed to restore sflow configuration -- switch config may be "
           "corrupted, causing subsequent test to fail";
  });

  // Flow details.
  constexpr auto dest_mac = netaddr::MacAddress(00, 01, 02, 03, 04, 05);
  constexpr auto source_mac = netaddr::MacAddress(00, 01, 02, 03, 04, 06);
  constexpr auto source_ip = netaddr::Ipv4Address(192, 168, 10, 1);

  ASSERT_OK_AND_ASSIGN(std::vector<IxiaLink> ready_links,
                       GetReadyIxiaLinks(*generic_testbed, *gnmi_stub));

  ASSERT_FALSE(ready_links.empty());

  std::string ixia_interface = ready_links[0].ixia_interface;

  // We will perform the following steps with Ixia:
  // Set up Ixia traffic.
  // Send Ixia traffic.
  // Stop Ixia traffic.

  constexpr int kFrameSize =
      kMaxFrameSize - kVlanTagSize - kFrameCheckSequenceSize;

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

  ASSERT_OK(
      pins_test::ixia::SetFrameSize(traffic_ref, kFrameSize, *generic_testbed));

  ASSERT_OK(pins_test::ixia::SetSrcMac(traffic_ref, source_mac.ToString(),
                                       *generic_testbed));

  ASSERT_OK(pins_test::ixia::SetDestMac(traffic_ref, dest_mac.ToString(),
                                        *generic_testbed));

  ASSERT_OK(pins_test::ixia::AppendIPv4(traffic_ref, *generic_testbed));

  ASSERT_OK(pins_test::ixia::SetSrcIPv4(traffic_ref, source_ip.ToString(),
                                        *generic_testbed));

  if (GetParam().nsf_reboot && GetParam().ssh_client_for_nsf) {
    ASSERT_OK(
        NsfRebootHelper(generic_testbed.get(), GetParam().ssh_client_for_nsf));
    // Create a new P4rt session after NSF Reboot
    ASSERT_OK_AND_ASSIGN(sut_p4_session,
                         p4_runtime::P4RuntimeSession::Create(sut));
  } else if (GetParam().nsf_reboot && !GetParam().ssh_client_for_nsf) {
    FAIL() << "ssh_client parameter needed for NSF Reboot is not provided";
  }

  // Listen for punted packets from the SUT.
  PacketReceiveInfo packet_receive_info;
  {
    absl::MutexLock lock(&packet_receive_info.mutex);
    packet_receive_info.num_packets_punted = 0;
  }

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
  ASSERT_OK_AND_ASSIGN(auto queues, ExtractQueueInfoViaGnmiConfig(
                                        /*port=*/"CPU", sut_gnmi_config));
  int queue_index = 0;
  for (auto &[queue_name, queue_info] : queues) {
    if (!IsValidCpuQueue(queue_info.p4_queue_name)) continue;
    if (absl::StartsWith(queue_info.p4_queue_name, "INBAND_")) continue;
    // Skip unconfigured queues.
    if (queue_info.rate_packets_per_second == 0) {
      continue;
    }

    LOG(INFO) << "\n\n\nTesting Queue : " << queue_name
              << "\n===================\n\n\n";

    constexpr uint32_t kBaseIp = 0xac000001;
    auto kDestIp = netaddr::Ipv4Address(std::bitset<32>(kBaseIp + queue_index));
    // Install punt entries on control switch
    ASSERT_OK(SetUpPuntToCPU(dest_mac, kDestIp, queue_info.p4_queue_name,
                             ir_p4info, *sut_p4_session));

    ASSERT_OK(pins_test::ixia::SetDestIPv4(traffic_ref, kDestIp.ToString(),
                                           *generic_testbed));

    ASSERT_OK_AND_ASSIGN(QueueCounters initial_counters,
                         GetGnmiQueueCounters("CPU", queue_name, *gnmi_stub));

    // Reset received packet count at tester for each iteration.
    {
      absl::MutexLock lock(&packet_receive_info.mutex);
      packet_receive_info.num_packets_punted = 0;
    }

    int num_pipes = GetParam().num_pipes;
    int kBurstyTotalFrames =
        queue_info.shared_buffer_static_limit / (num_pipes * kFrameSize) +
        queue_info.scheduler_be_pkts;
    ASSERT_OK(pins_test::ixia::SetFrameCount(traffic_ref, kBurstyTotalFrames,
                                             *generic_testbed));

    ASSERT_OK(pins_test::ixia::StartTraffic(traffic_ref, topology_ref,
                                            *generic_testbed));

    // Wait for Traffic to be sent.
    absl::SleepFor(kTrafficDuration);

    static constexpr absl::Duration kPollInterval = absl::Seconds(5);
    static constexpr absl::Duration kTotalTime = absl::Seconds(15);
    static const int kIterations = kTotalTime / kPollInterval;

    QueueCounters final_counters;
    QueueCounters delta_counters;
    // Check for counters every 5 seconds up to 15 seconds till they match.
    for (int gnmi_counters_check = 0; gnmi_counters_check < kIterations;
         gnmi_counters_check++) {
      absl::SleepFor(kPollInterval);
      ASSERT_OK_AND_ASSIGN(final_counters,
                           GetGnmiQueueCounters("CPU", queue_name, *gnmi_stub));
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
          kBurstyTotalFrames) {
        break;
      }
    }

    // The shared buffer is split between the number of pipes.
    ASSERT_GE(delta_counters.num_packets_transmitted,
              queue_info.shared_buffer_static_limit / (num_pipes * kFrameSize));
    ASSERT_LE(delta_counters.num_packets_transmitted, kBurstyTotalFrames);
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
      LOG(INFO) << "Packet size: " << kFrameSize;
      LOG(INFO) << "Timestamp of first received packet: "
                << packet_receive_info.time_first_packet_punted;
      LOG(INFO) << "Timestamp of last received packet: "
                << packet_receive_info.time_last_packet_punted;
      LOG(INFO) << "Duration of packets received: " << duration;
    }
    ++queue_index;
  }  // for each queue.
  // Stop receiving at tester.
  receiver.Destroy();
}

}  // namespace
}  // namespace pins_test
