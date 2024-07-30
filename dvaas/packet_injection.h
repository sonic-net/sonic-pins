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

#ifndef PINS_DVAAS_PACKET_INJECTION_H_
#define PINS_DVAAS_PACKET_INJECTION_H_

#include <functional>
#include <optional>
#include <string>
#include <vector>

#include "absl/container/flat_hash_set.h"
#include "absl/status/statusor.h"
#include "dvaas/test_vector.h"
#include "dvaas/test_vector.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"

namespace dvaas {

// Records packet statistics during dataplane validation.
struct PacketStatistics {
  int total_packets_injected = 0;
  int total_packets_forwarded = 0;
  int total_packets_punted = 0;
};

// Type of a function that given an unsolicited (i.e. a packet that is NOT
// a result of a input test packet) received either from the SUT or
// the control switch, determines if the packet is among expected such packets
// or not.
using IsExpectedUnsolicitedPacketFunctionType =
    std::function<bool(const packetlib::Packet& packet)>;

// Unsolicited packets that, for the time being, are acceptable in a GPINS
// testbeds.
inline bool DefaultIsExpectedUnsolicitedPacket(
    const packetlib::Packet& packet) {
  // TODO Switch generates router solicitation packets.
  if (packet.headers().size() == 3 &&
      packet.headers(2).icmp_header().type() == "0x85") {
    return true;
  }
  // TODO Switch generates IPV6 hop_by_hop packets.
  if (packet.headers().size() == 2 &&
      packet.headers(1).ipv6_header().next_header() == "0x00") {
    return true;
  }
  // Switch generates LACP packets if LAGs are present.
  if (packet.headers().size() == 1 &&
      packet.headers(0).ethernet_header().ethertype() == "0x8809") {
    return true;
  }
  return false;
}

// Gets 'ingress_port' value from metadata in `packet_in`. Returns
// InvalidArgumentError if 'ingress_port' metadata is missing.
// TODO: Make this function private.
absl::StatusOr<std::string> GetIngressPortFromIrPacketIn(
    const pdpi::IrPacketIn& packet_in);

// Determines the switch's behavior when receiving test packets by:
// - Injecting those packets to the control switch egress to send to the SUT.
// - Determining the set of packets that were forwarded (punted from control
//   switch) and punted (punted from SUT) for each input packet.
absl::StatusOr<PacketTestRuns> SendTestPacketsAndCollectOutputs(
    pdpi::P4RuntimeSession& sut, pdpi::P4RuntimeSession& control_switch,
    const PacketTestVectorById& packet_test_vector_by_id,
    PacketStatistics& statistics,
    std::optional<int> max_packets_to_send_per_second,
    const IsExpectedUnsolicitedPacketFunctionType&
        is_expected_unsolicited_packet = DefaultIsExpectedUnsolicitedPacket);

}  // namespace dvaas

#endif  // PINS_DVAAS_PACKET_INJECTION_H_
