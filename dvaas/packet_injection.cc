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

#include "dvaas/packet_injection.h"

#include <cstdlib>
#include <optional>
#include <queue>
#include <string>
#include <vector>

#include "absl/algorithm/container.h"
#include "absl/container/btree_map.h"
#include "absl/container/flat_hash_map.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/escaping.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "dvaas/port_id_map.h"
#include "dvaas/test_vector.h"
#include "dvaas/test_vector.pb.h"
#include "gutil/gutil/status.h"
#include "lib/p4rt/p4rt_port.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_infra/p4_pdpi/utils/ir.h"
#include "tests/forwarding/util.h"

namespace dvaas {
namespace {

using pins_test::P4rtPortId;

// Utils.
// Reads P4Info from the `device` and convert it to IrP4Info.
absl::StatusOr<pdpi::IrP4Info> GetIrP4Info(
    pdpi::P4RuntimeSession& p4rt_session) {
  ASSIGN_OR_RETURN(p4::v1::GetForwardingPipelineConfigResponse response,
                   pdpi::GetForwardingPipelineConfig(&p4rt_session));
  return pdpi::CreateIrP4Info(response.config().p4info());
}

bool IsRouteSolicitationPacket(const packetlib::Packet& packet) {
  return absl::c_any_of(packet.headers(), [](const packetlib::Header& header) {
    return header.icmp_header().type() == "0x85";
  });
}

bool IsIpv6HopByHopPacket(const packetlib::Packet& packet) {
  return absl::c_any_of(packet.headers(), [](const packetlib::Header& header) {
    return header.ipv6_header().next_header() == "0x00";
  });
}

bool IsLacpPacket(const packetlib::Packet& packet) {
  return absl::c_any_of(packet.headers(), [](const packetlib::Header& header) {
    return header.ethernet_header().ethertype() == "0x8809";
  });
}

bool IsPsampEncapedPacket(const packetlib::Packet& packet) {
  return absl::c_any_of(packet.headers(), [](const packetlib::Header& header) {
    return header.has_psamp_header();
  });
}

bool IsArpPacket(const packetlib::Packet& packet) {
  return absl::c_any_of(packet.headers(), [](const packetlib::Header& header) {
    return header.ethernet_header().ethertype() == "0x0806" ||
           header.vlan_header().ethertype() == "0x0806";
  });
}

bool IsRsyslogPacket(const packetlib::Packet& packet) {
  return absl::c_any_of(packet.headers(), [](const packetlib::Header& header) {
    return header.has_ipv6_header() &&
           (header.ipv6_header().ipv6_destination() == "2001:4860:f802::c0" ||
            header.ipv6_header().ipv6_destination() == "2001:4860:f802::bf");
  });
}

}  // namespace

bool DefaultIsExpectedUnsolicitedPacket(const packetlib::Packet& packet) {
  // TODO Switch generates router solicitation packets.
  if (IsRouteSolicitationPacket(packet)) {
    return true;
  }
  // TODO Switch generates IPV6 hop_by_hop packets.
  if (IsIpv6HopByHopPacket(packet)) {
    return true;
  }
  // Switch generates LACP packets if LAGs are present.
  if (IsLacpPacket(packet)) {
    return true;
  }
  // Control switch sends a known unsolicited packet, SUT mirrors it back to the
  // control switch but with PSAMP encap, so it is no longer recognized by the
  // above filters.
  if (IsPsampEncapedPacket(packet)) {
    return true;
  }
  if (std::getenv("gpins_alpine_env") != nullptr) {
    // TODO: Remove once Alpine disables unsolicited ARP packets.
    if (IsArpPacket(packet)) {
      LOG(INFO) << "ALPINE: Ignoring ARP packet";
      return true;
    }
  }
  return false;
}

absl::StatusOr<std::vector<TaggedPacketIn>>
CollectStreamMessageResponsesAndReturnTaggedPacketIns(
    pdpi::P4RuntimeSession& p4rt_session, absl::Duration duration,
    const IsExpectedUnsolicitedPacketFunctionType&
        is_expected_unsolicited_packet) {
  // Collect all unread stream messages responses from the P4RT session that
  // were received before or during the specified duration.
  ASSIGN_OR_RETURN(std::vector<p4::v1::StreamMessageResponse> responses,
                   p4rt_session.GetAllStreamMessagesFor(duration));

  std::vector<TaggedPacketIn> tagged_packet_ins;
  for (const p4::v1::StreamMessageResponse& response : responses) {
    if (!response.has_packet()) {
      // TODO: Decide if we should continue or fail and stop.
      return gutil::FailedPreconditionErrorBuilder()
             << "Unexpected (i.e. non-packet-in) response "
             << response.DebugString();
    } else {
      const packetlib::Packet parsed_inner_packet =
          packetlib::ParsePacket(response.packet().payload());

      absl::StatusOr<int> test_packet_id =
          ExtractIdFromTaggedPacket(response.packet().payload());
      if (test_packet_id.ok()) {
        tagged_packet_ins.push_back({
            .tag = *test_packet_id,
            .packet_in = response.packet(),
            .parsed_inner_packet = parsed_inner_packet,
        });
      } else {
        if (is_expected_unsolicited_packet(parsed_inner_packet)) {
          VLOG(1) << "Ignoring expected unsolicited packet "
                  << parsed_inner_packet.ShortDebugString();
        } else {
          // TODO: Decide if we should continue or fail and stop.
          return gutil::FailedPreconditionErrorBuilder()
                 << "Non-tagged packet-in "
                 << parsed_inner_packet.DebugString();
        }
      }
    }
  }

  return tagged_packet_ins;
}

// Returns the SUT egress port corresponding to the punted packet on control
// switch given the `mirror_testbed_port_map`.
absl::StatusOr<P4rtPortId> GetSutEgressPortFromControlSwitchPacketIn(
    const pdpi::IrPacketIn& packet_in,
    const MirrorTestbedP4rtPortIdMap& mirror_testbed_port_map) {
  ASSIGN_OR_RETURN(const std::string control_switch_ingress_port_p4rt_encoding,
                   GetIngressPortFromIrPacketIn(packet_in));
  P4rtPortId control_switch_ingress_port;
  if (absl::StartsWith(control_switch_ingress_port_p4rt_encoding, "0x")) {
    ASSIGN_OR_RETURN(control_switch_ingress_port,
                     P4rtPortId::MakeFromHexstringEncoding(
                         control_switch_ingress_port_p4rt_encoding));
  } else {
    ASSIGN_OR_RETURN(control_switch_ingress_port,
                     P4rtPortId::MakeFromP4rtEncoding(
                         control_switch_ingress_port_p4rt_encoding));
  }
  return mirror_testbed_port_map.GetSutPortConnectedToControlSwitchPort(
      control_switch_ingress_port);
}

absl::StatusOr<std::string> GetIngressPortFromIrPacketIn(
    const pdpi::IrPacketIn& packet_in) {
  for (const auto& metadata : packet_in.metadata()) {
    if (metadata.name() == "ingress_port") {
      return pdpi::IrValueString(metadata.value());
    }
  }
  return absl::InvalidArgumentError(
      "IrPacketIn does not contain 'ingress_port' metadata.");
}

absl::StatusOr<PacketTestRuns> SendTestPacketsAndCollectOutputs(
    pdpi::P4RuntimeSession& sut, pdpi::P4RuntimeSession& control_switch,
    const PacketTestVectorById& packet_test_vector_by_id,
    const PacketInjectionParams& parameters, PacketStatistics& statistics,
    bool log_injection_progress) {
  LOG(INFO) << "Injecting test packets into the dataplane "
            << packet_test_vector_by_id.size();
  statistics.total_packets_injected += packet_test_vector_by_id.size();

  // Compute per packet injection delay.
  std::optional<absl::Duration> injection_delay;
  if (parameters.max_packets_to_send_per_second.has_value()) {
    injection_delay =
        absl::Milliseconds(1e3 / *parameters.max_packets_to_send_per_second);
  }

  std::queue<int> test_vectors_id_queue;
  for (const auto& [test_id, packet_test_vector] : packet_test_vector_by_id) {
    test_vectors_id_queue.push(test_id);
  }

  // Batches the packets, which are injected and collected according to the
  // `max_in_flight_packets` parameter. If not specified, the batch size is
  // equal to the number of test vectors (all of them are injected as one
  // batch).
  int max_in_flight_packets = parameters.max_in_flight_packets.value_or(
      packet_test_vector_by_id.size());
  if (parameters.max_in_flight_packets.has_value()) {
    LOG(INFO) << "Packet injection is split into batches of size "
              << max_in_flight_packets;
  }

  absl::btree_map<int, SwitchOutput> switch_output_by_id;
  absl::flat_hash_map<int, absl::Time> packet_injection_time_by_id;
  ASSIGN_OR_RETURN(const pdpi::IrP4Info control_ir_p4info,
                   GetIrP4Info(control_switch));
  while (!test_vectors_id_queue.empty()) {
    int num_in_flight_packets = 0;
    // Sends the packets that are ready to be sent according to the given batch
    // size.
    while (!test_vectors_id_queue.empty() &&
           num_in_flight_packets < max_in_flight_packets) {
      int test_id = test_vectors_id_queue.front();
      test_vectors_id_queue.pop();
      const PacketTestVector& packet_test_vector =
          packet_test_vector_by_id.at(test_id);
      num_in_flight_packets++;

      const Packet& packet = packet_test_vector.input().packet();
      if (packet_test_vector.input().type() == SwitchInput::DATAPLANE) {
        // Get corresponding control switch port for the packet's ingress port.
        ASSIGN_OR_RETURN(const P4rtPortId sut_ingress_port,
                         P4rtPortId::MakeFromP4rtEncoding(packet.port()));
        ASSIGN_OR_RETURN(
            const P4rtPortId control_switch_port,
            parameters.mirror_testbed_port_map
                .GetControlSwitchPortConnectedToSutPort(sut_ingress_port));

        // Inject to egress of control switch.
        RETURN_IF_ERROR(pins::InjectEgressPacket(
            control_switch_port.GetP4rtEncoding(),
            absl::HexStringToBytes(packet.hex()), control_ir_p4info,
            &control_switch, injection_delay));
      } else if (packet_test_vector.input().type() ==
                 SwitchInput::SUBMIT_TO_INGRESS) {
        // Inject to SUT ingress port.
        ASSIGN_OR_RETURN(const pdpi::IrP4Info sut_ir_p4info, GetIrP4Info(sut));
        std::string raw_packet = absl::HexStringToBytes(packet.hex());
        RETURN_IF_ERROR(
            pins::InjectIngressPacket(raw_packet, sut_ir_p4info, &sut));
      } else if (packet_test_vector.input().type() == SwitchInput::PACKET_OUT) {
        ASSIGN_OR_RETURN(const P4rtPortId sut_egress_port,
                         P4rtPortId::MakeFromP4rtEncoding(packet.port()));
        // Inject to SUT egress port.
        ASSIGN_OR_RETURN(const pdpi::IrP4Info sut_ir_p4info, GetIrP4Info(sut));
        RETURN_IF_ERROR(
            pins::InjectEgressPacket(sut_egress_port.GetP4rtEncoding(),
                                     absl::HexStringToBytes(packet.hex()),
                                     sut_ir_p4info, &sut, injection_delay));
      } else {
        // TODO: Add support for other input types.
        return absl::UnimplementedError(
            absl::StrCat("Test vector input type not supported\n",
                         packet_test_vector.input().DebugString()));
      }
      packet_injection_time_by_id[test_id] = absl::Now();
    }

    // Check the output of the control switch.
    LOG(INFO) << "Waiting for "
              << parameters.max_expected_packet_in_flight_duration
              << " before collecting packets to account for in-flight packets";
    absl::StatusOr<std::vector<TaggedPacketIn>> control_packet_ins =
        CollectStreamMessageResponsesAndReturnTaggedPacketIns(
            control_switch, parameters.max_expected_packet_in_flight_duration,
            parameters.is_expected_unsolicited_packet);
    RETURN_IF_ERROR(control_packet_ins.status())
        << "while collecting the output of control_switch";
    LOG(INFO) << "Collected " << control_packet_ins->size()
              << " forwarded packets (from control switch)";
    statistics.total_packets_forwarded += control_packet_ins->size();

    // Processing the output of the control switch.
    for (const TaggedPacketIn& packet_in : *control_packet_ins) {
      // Add to (forwarded) switch output for ID.
      Packet& forwarded_output =
          *switch_output_by_id[packet_in.tag].add_packets();

      // Set hex and parsed packet.
      forwarded_output.set_hex(
          absl::BytesToHexString(packet_in.packet_in.payload()));
      *forwarded_output.mutable_parsed() = packet_in.parsed_inner_packet;

      // Set port.
      ASSIGN_OR_RETURN(
          pdpi::IrPacketIn ir_packet_in,
          pdpi::PiPacketInToIr(control_ir_p4info, packet_in.packet_in));
      ASSIGN_OR_RETURN(const P4rtPortId sut_egress_port,
                       GetSutEgressPortFromControlSwitchPacketIn(
                           ir_packet_in, parameters.mirror_testbed_port_map));
      *forwarded_output.mutable_port() = sut_egress_port.GetP4rtEncoding();
    }

    if (parameters.enable_sut_packet_in_collection) {
      // Check the output of SUT.
      absl::StatusOr<std::vector<TaggedPacketIn>> sut_packet_ins =
          CollectStreamMessageResponsesAndReturnTaggedPacketIns(
              sut, parameters.max_expected_packet_in_flight_duration,
              parameters.is_expected_unsolicited_packet);
      RETURN_IF_ERROR(sut_packet_ins.status())
          << "while collecting the output of SUT";
      LOG(INFO) << "Collected " << sut_packet_ins->size()
                << " punted packets (from SUT)";
      statistics.total_packets_punted += sut_packet_ins->size();
      // Processing the output of SUT.
      ASSIGN_OR_RETURN(const pdpi::IrP4Info sut_ir_p4info, GetIrP4Info(sut));
      for (const TaggedPacketIn& packet_in : *sut_packet_ins) {
        // Add to (punted) switch output for ID.
        PacketIn& punted_output =
            *switch_output_by_id[packet_in.tag].add_packet_ins();

        // Set hex and parsed packet.
        punted_output.set_hex(
            absl::BytesToHexString(packet_in.packet_in.payload()));
        *punted_output.mutable_parsed() = packet_in.parsed_inner_packet;

        // Set metadata.
        ASSIGN_OR_RETURN(
            pdpi::IrPacketIn ir_packet_in,
            pdpi::PiPacketInToIr(sut_ir_p4info, packet_in.packet_in));
        *punted_output.mutable_metadata() = ir_packet_in.metadata();
      }
    }
  }
  LOG(INFO) << "Finished injecting and collecting test packets";

  // Create PacketTestRuns.
  PacketTestRuns result;
  result.mutable_test_runs()->Reserve(packet_test_vector_by_id.size());
  for (const auto& [id, packet_test_vector] : packet_test_vector_by_id) {
    PacketTestRun& run = *result.add_test_runs();
    *run.mutable_test_vector() = packet_test_vector;
    *run.mutable_actual_output() = switch_output_by_id[id];
    *run.mutable_input_packet_injection_time() =
        absl::FormatTime(absl::RFC3339_full, packet_injection_time_by_id[id],
                         absl::UTCTimeZone());
  }

  // TODO: Detect problematic packets and log or store them.
  if (switch_output_by_id.size() > packet_test_vector_by_id.size()) {
    // TODO: Decide if we should continue or fail and stop.
    return gutil::FailedPreconditionErrorBuilder()
           << "Switch output contains unexpected test vector IDs ";
  }

  return result;
}

}  // namespace dvaas
