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
#include "absl/strings/string_view.h"
#include "dvaas/test_vector.pb.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status.h"
#include "p4_infra/p4_pdpi/packetlib/bit_widths.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_infra/p4_pdpi/string_encodings/hex_string.h"
#include "re2/re2.h"

namespace dvaas {

namespace {
// All test packets (incl. input & output packets) must have payloads that
// contain an ID that matches this regular expression. This ID must be:
// * Uniform across all packets within a packet test vector.
// * Unique across different packet test vectors.
// Note: this regexp ends on a `:`, allowing for a description or additional
// bytes after the ID without changing the test packet ID.
constexpr LazyRE2 kTestPacketIdRegexp{R"(test packet #([0-9]+):)"};

// Returns a string with a "tag" that encodes the given test packet ID.
// Prevents the string from getting larger and larger upon each update since
// there is no description.
std::string MakeUnpaddedTestPacketTagFromUniqueId(int unique_test_packet_id) {
  return absl::StrCat("test packet #", unique_test_packet_id);
}

}  // namespace

// Returns a string that can be included anywhere in the packet, however it is
// recommended to be placed in the payload of test packets.
std::string MakeTestPacketTagFromUniqueId(int unique_test_packet_id,
                                          absl::string_view description) {
  std::string payload =
      absl::StrCat(MakeUnpaddedTestPacketTagFromUniqueId(unique_test_packet_id),
                   ": ", description);

  // Adds padding to the packet payload to prevent undersized packets. Any
  // Ethernet packet containing a tag returned by this function will be at
  // least the minimum size required by the Ethernet protocol.
  if (payload.size() < packetlib::kMinNumBytesInEthernetPayload) {
    payload.resize(packetlib::kMinNumBytesInEthernetPayload, ' ');
  }
  return payload;
}

absl::StatusOr<int> ExtractIdFromTaggedPacket(absl::string_view raw_packet) {
  int tag;
  if (!RE2::PartialMatch(raw_packet, *kTestPacketIdRegexp, &tag)) {
    return gutil::InvalidArgumentErrorBuilder()
           << "test packets must contain a tag of the form '"
           << kTestPacketIdRegexp->pattern()
           << "', but the given packet does not:\n"
           << gutil::PrintTextProto(packetlib::ParsePacket(raw_packet));
  }
  return tag;
}

absl::StatusOr<int> ExtractIdFromTaggedPacketInHex(
    absl::string_view packet_hex) {
  ASSIGN_OR_RETURN(std::string raw_packet,
                   pdpi::HexStringToByteString(absl::StrCat("0x", packet_hex)));
  return dvaas::ExtractIdFromTaggedPacket(raw_packet);
}

std::ostream& operator<<(std::ostream& os, const SwitchOutput& output) {
  return os << output.DebugString();
}

absl::Status UpdateTestTag(packetlib::Packet& packet, int new_tag) {
  // Make a new input packet with updated payload.
  std::string new_payload = packet.payload();
  if (!RE2::Replace(
          &new_payload, *kTestPacketIdRegexp,
          absl::StrCat(MakeUnpaddedTestPacketTagFromUniqueId(new_tag), ":"))) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Test packets must contain a tag of the form '"
           << kTestPacketIdRegexp->pattern()
           << "' in their payload, but the given packet with payload '"
           << packet.payload() << "' does not:\n"
           << gutil::PrintTextProto(packet);
  }
  packet.set_payload(new_payload);
  RETURN_IF_ERROR(PadPacketToMinimumSize(packet).status()).SetAppend()
      << "\nwhile trying to update test packet tag to " << new_tag
      << " for packet\n: " << gutil::PrintTextProto(packet);
  RETURN_IF_ERROR(UpdateAllComputedFields(packet).status()).SetAppend()
      << "\nwhile trying to update test packet tag to " << new_tag
      << " for packet\n: " << gutil::PrintTextProto(packet);
  return absl::OkStatus();
}

// Returns a serialization of the given `packet` as a hex string.
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
