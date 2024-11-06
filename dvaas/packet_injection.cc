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

#include <vector>

#include "absl/container/btree_map.h"
#include "absl/status/statusor.h"
#include "absl/strings/escaping.h"
#include "dvaas/test_vector.h"
#include "dvaas/test_vector.pb.h"
#include "gutil/status.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "tests/forwarding/util.h"

namespace dvaas {
namespace {

// Utils.
// Reads P4Info from the `device` and convert it to IrP4Info.
absl::StatusOr<pdpi::IrP4Info> GetIrP4Info(
    pdpi::P4RuntimeSession& p4rt_session) {
  ASSIGN_OR_RETURN(p4::v1::GetForwardingPipelineConfigResponse response,
                   pdpi::GetForwardingPipelineConfig(&p4rt_session));
  return pdpi::CreateIrP4Info(response.config().p4info());
}

// Processed information about a PacketIn message with a tagged payload.
struct TaggedPacketIn {
  int tag;
  p4::v1::PacketIn packet_in;
  packetlib::Packet parsed_inner_packet;
};

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
          ExtractTestPacketTag(parsed_inner_packet);
      if (test_packet_id.ok()) {
        tagged_packet_ins.push_back({
            .tag = *test_packet_id,
            .packet_in = response.packet(),
            .parsed_inner_packet = parsed_inner_packet,
        });
      } else {
        if (is_expected_unsolicited_packet(parsed_inner_packet)) {
          // TODO: Append to artifact instead of logging.
          LOG(INFO) << "Ignoring expected unsolicited packet "
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

}  // namespace

absl::StatusOr<std::string> GetIngressPortFromIrPacketIn(
    const pdpi::IrPacketIn& packet_in) {
  for (const auto& metadata : packet_in.metadata()) {
    if (metadata.name() == "ingress_port") return metadata.value().str();
  }
  return absl::InvalidArgumentError(
      "IrPacketIn does not contain 'ingress_port' metadata.");
}

absl::StatusOr<PacketTestRuns> SendTestPacketsAndCollectOutputs(
    pdpi::P4RuntimeSession& sut, pdpi::P4RuntimeSession& control_switch,
    const PacketTestVectorById& packet_test_vector_by_id,
    PacketStatistics& statistics,
    std::optional<int> max_packets_to_send_per_second,
    const IsExpectedUnsolicitedPacketFunctionType&
        is_expected_unsolicited_packet) {
  LOG(INFO) << "Injecting test packets into the dataplane "
            << packet_test_vector_by_id.size();
  statistics.total_packets_injected += packet_test_vector_by_id.size();

  // Get IrP4Infos.
  ASSIGN_OR_RETURN(const pdpi::IrP4Info sut_ir_p4info, GetIrP4Info(sut));
  ASSIGN_OR_RETURN(const pdpi::IrP4Info control_ir_p4info,
                   GetIrP4Info(control_switch));

  // Compute per packet injection delay.
  std::optional<absl::Duration> injection_delay;
  if (max_packets_to_send_per_second.has_value()) {
    injection_delay = absl::Milliseconds(1e3 / *max_packets_to_send_per_second);
  }

  // Send packets.
  for (const auto& [test_id, packet_test_vector] : packet_test_vector_by_id) {
    if (packet_test_vector.input().type() == SwitchInput::DATAPLANE) {
      const Packet& packet = packet_test_vector.input().packet();

      // Inject to egress of control switch.
      RETURN_IF_ERROR(pins::InjectEgressPacket(
          packet.port(), absl::HexStringToBytes(packet.hex()),
          control_ir_p4info, &control_switch, injection_delay));
    } else {
      return absl::UnimplementedError(
          absl::StrCat("Test vector input type not supported\n",
                       packet_test_vector.input().DebugString()));
    }
  }
  LOG(INFO) << "Finished injecting test packets";

  // Check the output of the switches.
  const absl::Duration kCollectionDuration = absl::Seconds(3);
  absl::StatusOr<std::vector<TaggedPacketIn>> control_packet_ins =
      CollectStreamMessageResponsesAndReturnTaggedPacketIns(
          control_switch, kCollectionDuration, is_expected_unsolicited_packet);
  RETURN_IF_ERROR(control_packet_ins.status())
      << "while collecting the output of control_switch";
  LOG(INFO) << "Collected " << control_packet_ins->size()
            << " forwarded packets (from control switch)";
  statistics.total_packets_forwarded += control_packet_ins->size();

  absl::StatusOr<std::vector<TaggedPacketIn>> sut_packet_ins =
      CollectStreamMessageResponsesAndReturnTaggedPacketIns(
          sut, kCollectionDuration, is_expected_unsolicited_packet);
  RETURN_IF_ERROR(sut_packet_ins.status())
      << "while  collecting the output of SUT";
  LOG(INFO) << "Collected " << sut_packet_ins->size()
            << " punted packets (from SUT)";
  statistics.total_packets_punted += sut_packet_ins->size();

  absl::btree_map<int, SwitchOutput> switch_output_by_id;
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
    ASSIGN_OR_RETURN(*forwarded_output.mutable_port(),
                     GetIngressPortFromIrPacketIn(ir_packet_in));
  }

  // Processing the output of SUT.
  for (const TaggedPacketIn& packet_in : *sut_packet_ins) {
    // Add to (punted) switch output for ID.
    PacketIn& punted_output =
        *switch_output_by_id[packet_in.tag].add_packet_ins();

    // Set hex and parsed packet.
    punted_output.set_hex(
        absl::BytesToHexString(packet_in.packet_in.payload()));
    *punted_output.mutable_parsed() = packet_in.parsed_inner_packet;

    // Set metadata.
    ASSIGN_OR_RETURN(pdpi::IrPacketIn ir_packet_in,
                     pdpi::PiPacketInToIr(sut_ir_p4info, packet_in.packet_in));
    *punted_output.mutable_metadata() = ir_packet_in.metadata();
  }

  // Create PacketTestRuns.
  PacketTestRuns result;
  result.mutable_test_runs()->Reserve(packet_test_vector_by_id.size());
  for (const auto& [id, packet_test_vector] : packet_test_vector_by_id) {
    PacketTestRun& run = *result.add_test_runs();
    *run.mutable_test_vector() = packet_test_vector;
    *run.mutable_actual_output() = switch_output_by_id[id];
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
