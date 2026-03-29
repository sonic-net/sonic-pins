#include "fourward/test_vector_generation.h"

#include <string>
#include <vector>

#include "absl/status/statusor.h"
#include "absl/strings/escaping.h"
#include "absl/strings/str_cat.h"
#include "absl/types/span.h"
#include "dvaas/test_vector.h"
#include "dvaas/test_vector.pb.h"
#include "fourward/fourward_oracle.h"
#include "fourward/trace_conversion.h"
#include "gutil/status.h"
#include "lib/p4rt/p4rt_port.h"
#include "packetlib/packetlib.h"
#include "packetlib/packetlib.pb.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesizer.pb.h"

namespace dvaas {
namespace {

// Builds a dvaas::Packet proto from raw bytes and a P4RT port ID.
absl::StatusOr<Packet> MakeDvaasPacket(absl::string_view raw_bytes,
                                       absl::string_view port) {
  Packet packet;
  packet.set_port(std::string(port));
  packet.set_hex(absl::BytesToHexString(raw_bytes));
  *packet.mutable_parsed() = packetlib::ParsePacket(raw_bytes);
  return packet;
}

// Tags a synthesized packet with a test ID and returns the raw bytes.
// The tag is embedded in the payload so DVaaS can correlate outputs with inputs.
absl::StatusOr<std::string> TagAndSerialize(
    const p4_symbolic::packet_synthesizer::SynthesizedPacket& synthesized,
    int test_id, const pins_test::P4rtPortId& default_ingress_port) {
  packetlib::Packet parsed = packetlib::ParsePacket(synthesized.packet());

  // Replace payload with tagged version.
  std::string tag = MakeTestPacketTagFromUniqueId(test_id, "4ward");
  parsed.set_payload(tag);

  // Pad and recompute checksums.
  RETURN_IF_ERROR(packetlib::PadPacketToMinimumSize(parsed).status());
  RETURN_IF_ERROR(packetlib::UpdateAllComputedFields(parsed).status());

  return packetlib::SerializePacket(parsed);
}

}  // namespace

absl::StatusOr<PacketTestVectorById> GeneratePacketTestVectorsUsingFourward(
    FourwardOracle& oracle,
    std::vector<p4_symbolic::packet_synthesizer::SynthesizedPacket>&
        synthesized_packets,
    const pins_test::P4rtPortId& default_ingress_port) {
  // Tag each packet and prepare inputs for the oracle.
  std::vector<PacketInput> oracle_inputs;
  oracle_inputs.reserve(synthesized_packets.size());

  for (int i = 0; i < synthesized_packets.size(); ++i) {
    const p4_symbolic::packet_synthesizer::SynthesizedPacket& synthesized =
        synthesized_packets[i];

    ASSIGN_OR_RETURN(std::string tagged_bytes,
                     TagAndSerialize(synthesized, /*test_id=*/i + 1,
                                    default_ingress_port));

    std::string port = synthesized.ingress_port().empty()
                           ? default_ingress_port.GetP4rtEncoding()
                           : synthesized.ingress_port();

    oracle_inputs.push_back({.ingress_port = port, .payload = tagged_bytes});
  }

  // Predict all outputs in a single streaming batch.
  ASSIGN_OR_RETURN(std::vector<PacketPrediction> predictions,
                   oracle.PredictAll(oracle_inputs));

  // Build test vectors from predictions.
  PacketTestVectorById result;
  for (int i = 0; i < predictions.size(); ++i) {
    int test_id = i + 1;
    const PacketPrediction& prediction = predictions[i];
    const PacketInput& input = oracle_inputs[i];

    PacketTestVector test_vector;

    // Input.
    SwitchInput* switch_input = test_vector.mutable_input();
    switch_input->set_type(SwitchInput::DATAPLANE);
    ASSIGN_OR_RETURN(*switch_input->mutable_packet(),
                     MakeDvaasPacket(input.payload, input.ingress_port));

    // Expected output — one acceptable output with all predicted packets.
    SwitchOutput* expected_output = test_vector.add_acceptable_outputs();
    for (const PacketPrediction::OutputPacket& output :
         prediction.output_packets) {
      ASSIGN_OR_RETURN(*expected_output->add_packets(),
                       MakeDvaasPacket(output.bytes, output.port));
    }

    // Attach trace.
    *expected_output->mutable_packet_trace() =
        FourwardTraceTreeToDvaasPacketTrace(prediction.trace);

    result[test_id] = std::move(test_vector);
  }

  return result;
}

}  // namespace dvaas
