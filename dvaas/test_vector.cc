// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "dvaas/test_vector.h"

#include <ostream>
#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/escaping.h"
#include "absl/strings/str_cat.h"
#include "dvaas/test_vector.pb.h"
#include "gutil/proto.h"
#include "gutil/status.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "re2/re2.h"

namespace dvaas {

// All test packets (incl. input & output packets) must have payloads that
// contain an ID that matches this regular expression. This ID must be:
// * Uniform across all packets within a packet test vector.
// * Unique across different packet test vectors.
inline constexpr LazyRE2 kTestPacketIdRegexp{R"(test packet #([0-9]+))"};

std::string MakeTestPacketTagFromUniqueId(int unique_test_packet_id) {
  return absl::StrCat("test packet #", unique_test_packet_id);
}

absl::StatusOr<int> ExtractTestPacketTag(const packetlib::Packet& packet) {
  int tag;
  if (!RE2::PartialMatch(packet.payload(), *kTestPacketIdRegexp, &tag)) {
    return gutil::InvalidArgumentErrorBuilder()
           << "test packets must contain a tag of the form '"
           << kTestPacketIdRegexp->pattern()
           << "' in their payload, but the given packet with payload '"
           << packet.payload() << "' does not:\n"
           << gutil::PrintTextProto(packet);
  }
  return tag;
}

std::ostream& operator<<(std::ostream& os, const SwitchOutput& output) {
  return os << output.DebugString();
}

absl::Status UpdateTestTag(packetlib::Packet& packet, int new_tag) {
  // Make a new input packet with updated payload.
  std::string new_payload = packet.payload();
  if (!RE2::Replace(&new_payload, *kTestPacketIdRegexp,
                    MakeTestPacketTagFromUniqueId(new_tag))) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Test packets must contain a tag of the form '"
           << kTestPacketIdRegexp->pattern()
           << "' in their payload, but the given packet with payload '"
           << packet.payload() << "' does not:\n"
           << gutil::PrintTextProto(packet);
  }
  packet.set_payload(new_payload);
  bool status;
  ASSIGN_OR_RETURN(status, PadPacketToMinimumSize(packet),
                   _.LogError() << "Failed to pad packet for tag: " << new_tag);
  ASSIGN_OR_RETURN(status, UpdateAllComputedFields(packet),
                   _.LogError()
                       << "Failed to update payload for tag: " << new_tag);

  return absl::OkStatus();
}

// Returns a serialization of the given `packet` as a hexstring.
absl::StatusOr<std::string> SerializeAsHexString(
    const packetlib::Packet& packet) {
  ASSIGN_OR_RETURN(std::string serialized_packet,
                   packetlib::RawSerializePacket(packet),
                   _ << " where packet = " << packet.DebugString());
  return absl::BytesToHexString(serialized_packet);
}

absl::Status UpdateTestTag(PacketTestVector& packet_test_vector, int new_tag) {
  // Updates the payload of the SwitchInput.
  dvaas::Packet& input_packet =
      *packet_test_vector.mutable_input()->mutable_packet();
  RETURN_IF_ERROR(UpdateTestTag(*input_packet.mutable_parsed(), new_tag));
  ASSIGN_OR_RETURN(const std::string input_packet_updated_hexstr,
                   SerializeAsHexString(input_packet.parsed()));
  input_packet.set_hex(input_packet_updated_hexstr);

  // Update the payload of the SwitchOutput.
  for (SwitchOutput& output_packet :
       *packet_test_vector.mutable_acceptable_outputs()) {
    for (dvaas::Packet& packet_out : *output_packet.mutable_packets()) {
      RETURN_IF_ERROR(UpdateTestTag(*packet_out.mutable_parsed(), new_tag));
      ASSIGN_OR_RETURN(const std::string packet_out_updated_hexstr,
                       SerializeAsHexString(packet_out.parsed()));
      packet_out.set_hex(packet_out_updated_hexstr);
    }
    for (dvaas::PacketIn& packet_in : *output_packet.mutable_packet_ins()) {
      RETURN_IF_ERROR(UpdateTestTag(*packet_in.mutable_parsed(), new_tag));
      ASSIGN_OR_RETURN(const std::string packet_in_updated_hexstr,
                       SerializeAsHexString(packet_in.parsed()));
      packet_in.set_hex(packet_in_updated_hexstr);
    }
  }
  return absl::OkStatus();
}

}  // namespace dvaas
