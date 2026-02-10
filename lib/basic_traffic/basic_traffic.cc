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

#include "lib/basic_traffic/basic_traffic.h"

#include <algorithm>
#include <functional>
#include <memory>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

#include "absl/algorithm/container.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/status.h"
#include "lib/basic_traffic/basic_p4rt_util.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/p4rt/p4rt_programming_context.h"
#include "lib/utils/generic_testbed_utils.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.pb.h"
#include "thinkit/control_device.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/switch.h"

namespace pins_test::basic_traffic {
namespace {

// A struct that contains the `packet` that has been modified to be forwarded
// according to a certain set of interface pairs, the `serialized_packet` to be
// actually sent, and the `control_interface` to send it out of.
struct PrecomputedPacket {
  std::string control_interface;
  packetlib::Packet packet;
  std::string serialized_packet;
};

// A struct that represents a key for every flow. This key identifies a flow by
// the index of the packet and the index of the interface pair that packet is
// sent into and expected to be received from.
struct Key {
  int pair_index;
  int packet_index;
};

// Returns the `result` string parsed into an int if present.
absl::StatusOr<int> ToInt(absl::StatusOr<std::string> result) {
  ASSIGN_OR_RETURN(std::string result_string, result);
  int integer;
  if (!absl::SimpleAtoi(result_string, &integer)) {
    return absl::InvalidArgumentError(
        absl::StrCat(result_string, " is not an integer."));
  }
  return integer;
}

// Converts the `key` into a string.
std::string SerializeKey(Key key) {
  return absl::StrCat(key.pair_index, ":", key.packet_index);
}

// Parses the `key` string.
absl::StatusOr<Key> DeserializeKey(absl::string_view key) {
  std::vector<absl::string_view> key_parts = absl::StrSplit(key, ':');
  if (key_parts.size() != 2) {
    return absl::InternalError(absl::StrCat(
        "Key '", key, "' does not match format pair_index:packet_index."));
  }
  int pair_index;
  if (!absl::SimpleAtoi(key_parts[0], &pair_index)) {
    return absl::InternalError(
        absl::StrCat("Key '", key,
                     "' with format pair_index:packet_index, pair_index is not "
                     "an int."));
  }
  int packet_index;
  if (!absl::SimpleAtoi(key_parts[1], &packet_index)) {
    return absl::InternalError(absl::StrCat(
        "Key '", key,
        "' with format pair_index:packet_index, packet_index is not "
        "an int."));
  }
  return Key{.pair_index = pair_index, .packet_index = packet_index};
}

// Precomputes the packets to send to which control interfaces by substituting
// the proper destination IP and payload fields and serializing them. The
// precomputed packets contain the payload key, the final packet proto, and the
// serialized version of that packet.
absl::StatusOr<absl::flat_hash_map<std::string, PrecomputedPacket>>
PrecomputePackets(
    const absl::flat_hash_map<std::string, std::string>& port_id_from_interface,
    const absl::flat_hash_map<std::string, thinkit::InterfaceInfo>&
        info_from_sut_interface,
    absl::Span<const InterfacePair> pairs,
    absl::Span<const packetlib::Packet> packets) {
  absl::flat_hash_map<std::string, PrecomputedPacket> precomputed_packets;
  for (int pair_index = 0; pair_index < pairs.size(); pair_index++) {
    const InterfacePair& pair = pairs[pair_index];
    ASSIGN_OR_RETURN(int egress_port_id,
                     ToInt(gutil::FindOrStatus(port_id_from_interface,
                                               pair.egress_interface)));
    // Find the control interface to send it out from.
    ASSIGN_OR_RETURN(
        thinkit::InterfaceInfo control_info,
        gutil::FindOrStatus(info_from_sut_interface, pair.ingress_interface));

    // Use the `egress_port_id` to populate the packet with the right fields
    // for forwarding and tracking. This creates a copy using the `packets`
    // list as a template and modifies it to be forwarded.
    for (int packet_index = 0; packet_index < packets.size(); packet_index++) {
      std::string key = SerializeKey(
          Key{.pair_index = pair_index, .packet_index = packet_index});
      packetlib::Packet packet = packets[packet_index];
      auto ipv4_header = absl::c_find_if(
          *packet.mutable_headers(),
          [](packetlib::Header& header) { return header.has_ipv4_header(); });
      if (ipv4_header == packet.mutable_headers()->end()) {
        return absl::InvalidArgumentError(absl::StrCat(
            "Packet is missing a IPv4 header: ", packet.DebugString()));
      }
      ipv4_header->mutable_ipv4_header()->set_ipv4_destination(absl::StrFormat(
          "10.0.%d.%d", egress_port_id / 256, egress_port_id % 256));
      // Maintain the same payload size while adding the `key`, using \0.
      packet.set_payload(absl::StrCat(
          key,
          std::string(std::max<int>(0, packet.payload().size() - key.size()),
                      '\0')));

      // Serialize the modified copy.
      RETURN_IF_ERROR(PadPacketToMinimumSize(packet).status());
      RETURN_IF_ERROR(packetlib::UpdateAllComputedFields(packet).status());
      RETURN_IF_ERROR(ValidatePacket(packet));
      ASSIGN_OR_RETURN(std::string serialized_packet,
                       RawSerializePacket(packet));

      precomputed_packets[std::move(key)] = PrecomputedPacket{
          .control_interface = control_info.peer_interface_name,
          .packet = std::move(packet),
          .serialized_packet = std::move(serialized_packet)};
    }
  }
  return precomputed_packets;
}

// Returns the payload with 0-padding removed that might have been added to a
// packet to fulfill minimum length requirements.
absl::string_view RemovePadding(absl::string_view payload) {
  return payload.substr(0, payload.find_first_of('\0'));
}

}  // namespace

absl::Status ProgramRoutes(
    const std::function<absl::Status(p4::v1::WriteRequest&)>& write_request,
    const pdpi::IrP4Info& ir_p4info,
    const absl::flat_hash_map<std::string, std::string>& port_id_from_interface,
    absl::Span<const InterfacePair> pairs) {
  absl::flat_hash_set<std::string> interfaces;
  absl::flat_hash_set<std::string> egress_interfaces;
  for (const InterfacePair& pair : pairs) {
    interfaces.insert(pair.ingress_interface);
    interfaces.insert(pair.egress_interface);
    egress_interfaces.insert(pair.egress_interface);
  }

  RETURN_IF_ERROR(ProgramTrafficVrf(write_request, ir_p4info));
  for (const std::string& interface : interfaces) {
    ASSIGN_OR_RETURN(int port_id, ToInt(gutil::FindOrStatus(
                                      port_id_from_interface, interface)));
    RETURN_IF_ERROR(ProgramRouterInterface(write_request, port_id, ir_p4info));
  }
  for (const std::string& egress_interface : egress_interfaces) {
    ASSIGN_OR_RETURN(
        int egress_port_id,
        ToInt(gutil::FindOrStatus(port_id_from_interface, egress_interface)));
    RETURN_IF_ERROR(ProgramIPv4Route(write_request, egress_port_id, ir_p4info));
  }
  return ProgramL3AdmitTableEntry(write_request, ir_p4info);
}

std::vector<InterfacePair> OneToOne(
    absl::Span<const std::string> sources,
    absl::Span<const std::string> destinations) {
  int resulting_size = std::min(sources.size(), destinations.size());
  std::vector<InterfacePair> pairs;
  pairs.reserve(resulting_size);
  for (int i = 0; i < resulting_size; i++) {
    pairs.push_back(InterfacePair{.ingress_interface = sources[i],
                                  .egress_interface = destinations[i]});
  }
  return pairs;
}

std::vector<InterfacePair> ManyToMany(
    absl::Span<const std::string> sources,
    absl::Span<const std::string> destinations) {
  std::vector<InterfacePair> pairs;
  pairs.reserve(sources.size() * destinations.size());
  for (const std::string& source : sources) {
    for (const std::string& destination : destinations) {
      pairs.push_back(InterfacePair{.ingress_interface = source,
                                    .egress_interface = destination});
    }
  }
  return pairs;
}

std::vector<InterfacePair> AllToAll(absl::Span<const std::string> interfaces) {
  if (interfaces.empty()) {
    return {};
  }
  std::vector<InterfacePair> pairs;
  pairs.reserve(interfaces.size() * (interfaces.size() - 1));
  for (int i = 0; i < interfaces.size(); i++) {
    for (int j = 0; j < interfaces.size(); j++) {
      if (i == j) {
        continue;
      }
      pairs.push_back(InterfacePair{.ingress_interface = interfaces[i],
                                    .egress_interface = interfaces[j]});
    }
  }
  return pairs;
}

absl::StatusOr<std::vector<TrafficStatistic>> SendTraffic(
    thinkit::GenericTestbed& testbed, pdpi::P4RuntimeSession* session,
    const pdpi::IrP4Info& ir_p4info, absl::Span<const InterfacePair> pairs,
    absl::Span<const packetlib::Packet> packets, absl::Duration duration,
    SendTrafficOptions options) {
  // The time to wait for packets to finish passing through the switch and be
  // collected.
  static constexpr absl::Duration kPassthroughWaitTime = absl::Seconds(30);

  // This function currently supports IPv4 packets only.
  bool all_ipv4 = absl::c_all_of(packets, [](const packetlib::Packet& packet) {
    return absl::c_any_of(packet.headers(),
                          [](const packetlib::Header& header) {
                            return header.has_ipv4_header();
                          });
  });
  if (!all_ipv4) {
    return absl::InvalidArgumentError(
        "Packets must all include an IPv4 header.");
  }

  ASSIGN_OR_RETURN(auto gnmi_stub, testbed.Sut().CreateGnmiStub());
  ASSIGN_OR_RETURN(auto port_id_from_sut_interface,
                   GetAllInterfaceNameToPortId(*gnmi_stub));
  P4rtProgrammingContext p4rt_context(session,
                                      std::move(options.write_request));

  if (options.program_routes) {
    // Program the necessary table entries to forward traffic between the
    // interface pair.
    RETURN_IF_ERROR(ProgramRoutes(p4rt_context.GetWriteRequestFunction(),
                                  ir_p4info, port_id_from_sut_interface,
                                  pairs));
  } else {
    LOG(INFO) << "Skipped route programming";
  }

  // Precompute packets to send.
  absl::flat_hash_map<std::string, thinkit::InterfaceInfo>
      info_from_sut_interface = testbed.GetSutInterfaceInfo();
  ASSIGN_OR_RETURN(auto packets_to_send,
                   PrecomputePackets(port_id_from_sut_interface,
                                     info_from_sut_interface, pairs, packets));

  // Send packets.
  absl::flat_hash_map<std::string, int> sent_packets;
  std::vector<std::tuple<std::string, std::string>> received_packets;
  {
    ASSIGN_OR_RETURN(auto finalizer, testbed.ControlDevice().CollectPackets());

    LOG(INFO) << "Starting to send traffic.";
    absl::Time start_time = absl::Now();
    absl::Time last_sent_time = start_time;
    absl::Duration interpacket_time =
        absl::Seconds(1.0f / options.packets_per_second);
    while (absl::Now() - start_time < duration) {
      for (const auto& [key, packet] : packets_to_send) {
        RETURN_IF_ERROR(testbed.ControlDevice().SendPacket(
            packet.control_interface, packet.serialized_packet, std::nullopt));
        sent_packets[key]++;
        if (options.packets_sent != nullptr) {
          (*options.packets_sent)++;
        }
        while (absl::Now() - last_sent_time < interpacket_time) {
        }
        last_sent_time = absl::Now();
      }
    }

    RETURN_IF_ERROR(finalizer->HandlePacketsFor(
        kPassthroughWaitTime,
        [&received_packets](absl::string_view control_interface,
                            absl::string_view packet_string) {
          received_packets.push_back(std::make_tuple(
              std::string(control_interface), std::string(packet_string)));
        }));
  }
  LOG(INFO) << "Traffic sending complete.";

  // Create a map from control interface to SUT interface.
  absl::flat_hash_map<std::string, std::string>
      sut_interface_from_control_interface;
  for (const InterfaceLink& link :
       GetAllControlLinks(info_from_sut_interface)) {
    sut_interface_from_control_interface[link.peer_interface] =
        link.sut_interface;
  }

  // Parse the received packets and bucket them based on their payload. Valid
  // packets are those that came in on the expected egress interface, while
  // invalid packets are those that came in on a different egress interface.
  absl::flat_hash_map<std::string, int> valid_received_packets;
  absl::flat_hash_map<std::string, int> invalid_received_packets;
  for (const auto& [control_interface, packet_string] : received_packets) {
    packetlib::Packet packet = packetlib::ParsePacket(packet_string);
    absl::string_view key_string = RemovePadding(packet.payload());
    absl::StatusOr<Key> key = DeserializeKey(key_string);
    // Skip invalid packets that might have been picked up by PacketIO.
    if (!key.ok()) {
      continue;
    }

    absl::string_view expected_egress_interface =
        pairs[key->pair_index].egress_interface;
    ASSIGN_OR_RETURN(std::string actual_egress_interface,
                     gutil::FindOrStatus(sut_interface_from_control_interface,
                                         control_interface));
    if (expected_egress_interface == actual_egress_interface) {
      valid_received_packets[key_string]++;
    } else {
      invalid_received_packets[key_string]++;
    }
  }

  // Consolidate the statistics for return.
  std::vector<TrafficStatistic> statistics;
  statistics.reserve(pairs.size() * packets.size());
  for (int pair_index = 0; pair_index < pairs.size(); pair_index++) {
    ASSIGN_OR_RETURN(thinkit::InterfaceInfo control_info,
                     gutil::FindOrStatus(info_from_sut_interface,
                                         pairs[pair_index].ingress_interface));
    for (int packet_index = 0; packet_index < packets.size(); packet_index++) {
      std::string key = SerializeKey(
          Key{.pair_index = pair_index, .packet_index = packet_index});
      ASSIGN_OR_RETURN(PrecomputedPacket packet,
                       gutil::FindOrStatus(packets_to_send, key));
      statistics.push_back(TrafficStatistic{
          .interfaces = pairs[pair_index],
          .packets_sent = sent_packets[key],
          .packets_received = valid_received_packets[key],
          .packets_routed_incorrectly = invalid_received_packets[key],
          .packet = std::move(packet.packet)});
    }
  }
  return statistics;
}

}  // namespace pins_test::basic_traffic
