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
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/packetlib/packetlib.h"

namespace dvaas {

namespace {

absl::StatusOr<std::string> LegitimizeParsedPacketAndReturnAsHex(
    packetlib::Packet& packet) {
  RETURN_IF_ERROR(packetlib::UpdateMissingComputedFields(packet).status());
  RETURN_IF_ERROR(packetlib::ValidatePacket(packet));
  ASSIGN_OR_RETURN(std::string raw_packet,
                   packetlib::RawSerializePacket(packet));
  return absl::BytesToHexString(raw_packet);
}

// Checks that the given `input_packet` is well-formed, returning it with
// omittable fields filled in if that is the case, or an error otherwise.
absl::StatusOr<Packet> LegitimizePacket(Packet packet) {
  ASSIGN_OR_RETURN(*packet.mutable_hex(), LegitimizeParsedPacketAndReturnAsHex(
                                              *packet.mutable_parsed()));
  return packet;
}

// Checks that the given `packet_in`'s metadata is well-formed and if so
// returns it, or returns error otherwise.
absl::Status LegitimizePacketInMetadata(const PacketIn& packet_in,
                                        const pdpi::IrP4Info& ir_info) {
  // Check that PacketIn metadata is valid according to P4Runtime, in particular
  // "Section 16.1: Packet I/O".
  pdpi::IrPacketIn ir_packet_in;
  for (const pdpi::IrPacketMetadata& metadata : packet_in.metadata()) {
    *ir_packet_in.add_metadata() = metadata;
  }

  // Translate IR `packet_in` into PI to validate its metadata is well-formed.
  // If not, return an error.
  return pdpi::IrPacketInToPi(ir_info, ir_packet_in).status();
}

absl::StatusOr<PacketIn> LegitimizePacketIn(PacketIn packet_in,
                                            const pdpi::IrP4Info& ir_info) {
  RETURN_IF_ERROR(LegitimizePacketInMetadata(packet_in, ir_info));
  ASSIGN_OR_RETURN(
      *packet_in.mutable_hex(),
      LegitimizeParsedPacketAndReturnAsHex(*packet_in.mutable_parsed()));
  return packet_in;
}

// Checks that the given input `vector` is well-formed using
// `ir_info` and if so adds it to `legitimized_test_vectors_by_id`, or returns
// error otherwise.
absl::Status LegitimizeTestVector(
    PacketTestVector vector, const pdpi::IrP4Info& ir_info,
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
    for (int i = 0; i < output.packet_ins().size(); ++i) {
      PacketIn& output_packet_ins = *output.mutable_packet_ins(i);
      ASSIGN_OR_RETURN(
          int output_tag, ExtractTestPacketTag(output_packet_ins.parsed()),
          _.SetPrepend() << "output packet in #" << (i + 1) << " invalid: ");
      ASSIGN_OR_RETURN(
          output_packet_ins, LegitimizePacketIn(output_packet_ins, ir_info),
          _.SetPrepend() << "output packet in #" << (i + 1) << " invalid: ");
      if (output_tag != tag) {
        return gutil::InvalidArgumentErrorBuilder()
               << "mismatch of input packet in tag vs output packet in tag "
                  "for output packet in #"
               << (i + 1) << ": " << tag << " vs " << output_tag;
      }
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
    absl::Span<const PacketTestVector> user_provided_test_vectors,
    const pdpi::IrP4Info& ir_info) {
  PacketTestVectorById legitimized_test_vectors_by_id;
  for (const PacketTestVector& vector : user_provided_test_vectors) {
    absl::Status status =
        LegitimizeTestVector(vector, ir_info, legitimized_test_vectors_by_id);
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
