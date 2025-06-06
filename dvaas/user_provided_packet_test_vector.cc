#include "dvaas/user_provided_packet_test_vector.h"

#include <string>
#include <utility>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/escaping.h"
#include "absl/types/span.h"
#include "dvaas/test_vector.h"
#include "dvaas/test_vector.pb.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/packetlib/packetlib.h"

namespace dvaas {

namespace {

absl::StatusOr<std::string> LegitimizeParsedPacketAndReturnRawBytes(
    packetlib::Packet& packet) {
  RETURN_IF_ERROR(packetlib::UpdateMissingComputedFields(packet).status());
  RETURN_IF_ERROR(packetlib::ValidatePacket(packet));
  return packetlib::RawSerializePacket(packet);
}

// Checks that `packet` is well-formed and modifies it with omittable fields
// filled in if that is the case. It returns the test tag id or returns an error
// otherwise. Also, it generates an updated hex string representation of the
// packet.
absl::StatusOr<int> LegitimizePacketAndReturnId(Packet& packet) {
  ASSIGN_OR_RETURN(std::string bytes, LegitimizeParsedPacketAndReturnRawBytes(
                                          *packet.mutable_parsed()));
  *packet.mutable_hex() = absl::BytesToHexString(bytes);
  return ExtractIdFromTaggedPacket(bytes);
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

// Checks that the given `packet_in` is well-formed and modifies it with
// omittable fields filled in. It returns the test tag id or returns an error
// otherwise. Also, it generates an updated hex string representation of the
// packet.
absl::StatusOr<int> LegitimizePacketInAndReturnId(
    PacketIn& packet_in, const pdpi::IrP4Info& ir_info) {
  RETURN_IF_ERROR(LegitimizePacketInMetadata(packet_in, ir_info));
  ASSIGN_OR_RETURN(std::string bytes, LegitimizeParsedPacketAndReturnRawBytes(
                                          *packet_in.mutable_parsed()));
  *packet_in.mutable_hex() = absl::BytesToHexString(bytes);
  return ExtractIdFromTaggedPacket(bytes);
}

// Checks that the given input `vector` is well-formed using
// `ir_info` and if so adds it to `legitimized_test_vectors_by_id`, or returns
// error otherwise.
absl::Status LegitimizeTestVector(
    PacketTestVector vector, const pdpi::IrP4Info& ir_info,
    PacketTestVectorById& legitimized_test_vectors_by_id) {

  // Legitimize input packet.
  Packet& input_packet = *vector.mutable_input()->mutable_packet();

  // TODO: Revisit this when the decision about what to do with
  // input ports for submit_to_ingress test vectors is finalized.
  if (vector.input().type() == SwitchInput::SUBMIT_TO_INGRESS) {
    // The port will be ignored for submit_to_ingress packets so using an
    // arbitrary port is fine.
    if (input_packet.port().empty()) {
      input_packet.set_port("1");
    }
  }
  ASSIGN_OR_RETURN(int id, LegitimizePacketAndReturnId(input_packet),
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
          int output_id,
          LegitimizePacketInAndReturnId(output_packet_ins, ir_info),
          _.SetPrepend() << "output packet in #" << (i + 1) << " invalid: ");
      if (output_id != id) {
        return gutil::InvalidArgumentErrorBuilder()
	       << "mismatch of input packet in id vs output packet in id "
                  "for output packet in #"
	       << (i + 1) << ": " << id << " vs " << output_id;
      }
    }
    // Legitimize forwarded output packets.
    for (int i = 0; i < output.packets().size(); ++i) {
      Packet& output_packet = *output.mutable_packets(i);
      ASSIGN_OR_RETURN(
	  int output_id, LegitimizePacketAndReturnId(output_packet),
          _.SetPrepend() << "output packet #" << (i + 1) << " invalid: ");
      if (output_id != id) {
        return gutil::InvalidArgumentErrorBuilder()
	       << "mismatch of input packet id vs output packet id for "
                  "output packet #"
	       << (i + 1) << ": " << id << " vs " << output_id;
      }
    }
  }

  // Add internalized vector to result.
  const auto& [it, inserted] =
      legitimized_test_vectors_by_id.insert({id, vector});
  if (!inserted) {
    return gutil::InvalidArgumentErrorBuilder()
           << "user-provided packet test vectors must be tagged with unique "
              "IDs in their payload, but found multiple test vectors with ID "
	   << id << ". Dumping offending test vectors:\n<"
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
