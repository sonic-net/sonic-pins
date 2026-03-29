// Generates PacketTestVectors using 4ward for output prediction and traces.
//
// This is the 4ward equivalent of DataplaneValidationBackend's
// GeneratePacketTestVectors. It takes synthesized packets, tags them with
// test IDs, predicts outputs via FourwardOracle, and builds test vectors
// with traces attached.

#ifndef PINS_FOURWARD_TEST_VECTOR_GENERATION_H_
#define PINS_FOURWARD_TEST_VECTOR_GENERATION_H_

#include <vector>

#include "absl/status/statusor.h"
#include "absl/types/span.h"
#include "dvaas/test_vector.h"
#include "dvaas/test_vector.pb.h"
#include "fourward/fourward_oracle.h"
#include "lib/p4rt/p4rt_port.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesizer.pb.h"

namespace dvaas {

// Generates test vectors with output prediction from 4ward.
//
// For each synthesized packet:
//   1. Tags with a unique test ID (for correlating SUT outputs).
//   2. Pads to minimum Ethernet size and recomputes checksums.
//   3. Predicts outputs and traces via the oracle.
//   4. Builds a PacketTestVector with input, expected outputs, and trace.
//
// If `ingress_port` is empty in a synthesized packet, `default_ingress_port`
// is used.
absl::StatusOr<PacketTestVectorById> GeneratePacketTestVectorsUsingFourward(
    FourwardOracle& oracle,
    std::vector<p4_symbolic::packet_synthesizer::SynthesizedPacket>&
        synthesized_packets,
    const pins_test::P4rtPortId& default_ingress_port);

}  // namespace dvaas

#endif  // PINS_FOURWARD_TEST_VECTOR_GENERATION_H_
