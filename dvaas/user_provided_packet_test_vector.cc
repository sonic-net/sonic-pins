#include "dvaas/user_provided_packet_test_vector.h"

#include <string>
#include <utility>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/escaping.h"
#include "absl/types/span.h"
#include "dvaas/test_vector.h"
#include "dvaas/test_vector.pb.h"
#include "gutil/proto.h"
#include "gutil/status.h"
#include "p4_pdpi/packetlib/packetlib.h"

namespace dvaas {

namespace {

// Checks that the given `input_packet` is well-formed, returning it with
// omittable fields filled in if that is the case, or an error otherwise.
absl::StatusOr<Packet> LegitimizePacket(Packet packet) {
  RETURN_IF_ERROR(
      packetlib::UpdateMissingComputedFields(*packet.mutable_parsed())
          .status());
  RETURN_IF_ERROR(packetlib::ValidatePacket(packet.parsed()));
  ASSIGN_OR_RETURN(std::string raw_packet,
                   packetlib::RawSerializePacket(packet.parsed()));
  packet.set_hex(absl::BytesToHexString(raw_packet));
  return packet;
}

// Checks that the given `vector` is well-formed and if so adds it to
// `legitimized_test_vectors_by_id`, or returns error otherwise.
absl::Status LegitimizeTestVector(
    PacketTestVector vector,
    PacketTestVectorById& legitimized_test_vectors_by_id) {
  if (vector.input().type() != SwitchInput::DATAPLANE) {
    return gutil::UnimplementedErrorBuilder()
           << "only supported input type is DATAPLANE; found "
           << SwitchInput::Type_Name(vector.input().type());
  }

  // Legitimize input packet.
  Packet& input_packet = *vector.mutable_input()->mutable_packet();
  ASSIGN_OR_RETURN(int tag, ExtractTestPacketTag(input_packet.parsed()),
                   _.SetPrepend() << "invalid input packet: ");
  ASSIGN_OR_RETURN(input_packet, LegitimizePacket(input_packet),
                   _.SetPrepend() << "invalid input packet: ");

  // Legitimize acceptable outputs.
  if (vector.acceptable_outputs().empty()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "must specify at least 1 acceptable output, but 0 were found";
  }
  for (SwitchOutput& output : *vector.mutable_acceptable_outputs()) {
    // Punted output packets are not supported for now.
    if (!output.packet_ins().empty()) {
      return gutil::UnimplementedErrorBuilder()
             << "TODO: support vectors expecting `packet_ins` "
                "(punting)";
    }
    // Legitimize forwarded output packets.
    for (int i = 0; i < output.packets().size(); ++i) {
      Packet& output_packet = *output.mutable_packets(i);
      ASSIGN_OR_RETURN(
          int output_tag, ExtractTestPacketTag(output_packet.parsed()),
          _.SetPrepend() << "output packet #" << (i + 1) << " invalid: ");
      ASSIGN_OR_RETURN(output_packet, LegitimizePacket(output_packet),
                       _.SetPrepend()
                           << "output packet #" << (i + 1) << " invalid: ");
      if (output_tag != tag) {
        return gutil::InvalidArgumentErrorBuilder()
               << "mismatch of input packet tag vs output packet tag for "
                  "output packet #"
               << (i + 1) << ": " << tag << " vs " << output_tag;
      }
    }
  }

  // Add internalized vector to result.
  const auto& [it, inserted] =
      legitimized_test_vectors_by_id.insert({tag, vector});
  if (!inserted) {
    return gutil::InvalidArgumentErrorBuilder()
           << "user-provided packet test vectors must be tagged with unique "
              "IDs in their payload, but found multiple test vectors with ID "
           << tag << ". Dumping offending test vectors:\n<"
           << gutil::PrintTextProto(it->second) << ">\n<"
           << gutil::PrintTextProto(vector) << ">\n";
  }
  return absl::OkStatus();
}

}  // namespace

absl::StatusOr<PacketTestVectorById> LegitimizeUserProvidedTestVectors(
    absl::Span<const PacketTestVector> user_provided_test_vectors) {
  PacketTestVectorById legitimized_test_vectors_by_id;
  for (const PacketTestVector& vector : user_provided_test_vectors) {
    absl::Status status =
        LegitimizeTestVector(vector, legitimized_test_vectors_by_id);
    if (!status.ok()) {
      return gutil::StatusBuilder(status.code())
             << "problem in user-provided packet test vector: "
             << status.message() << "\nDumping offending test vector:\n"
             << gutil::PrintTextProto(vector);
    }
  }
  return legitimized_test_vectors_by_id;
}

}  // namespace dvaas
