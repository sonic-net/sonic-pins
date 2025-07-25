// Empowers users to specify custom packet test vectors that can be validated
// by DVaaS or Arriba.

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

#ifndef PINS_USER_PROVIDED_PACKET_TEST_VECTOR_H_
#define PINS_USER_PROVIDED_PACKET_TEST_VECTOR_H_

#include "absl/status/statusor.h"
#include "absl/types/span.h"
#include "dvaas/test_vector.h"
#include "dvaas/test_vector.pb.h"

namespace dvaas {

// Checks user-provided test vectors for well-formedness and prepares them for
// internal use by DVaaS/Arriba:
// * Fills in "omittable fields", see definition below.
// * Checks that each test vector is "well-formed", see definition below.
// * Returns updated, well-formed test vectors organized by ID, or returns an
//   actionable, user-facing error if a test vector is not well-formed.
//
// The following `dvaas::Packet` message fields can be omitted by the user:
// * All `hex` fields.
// * All subfields of `packetlib::Packet` messages that are considered "computed
//   fields" by packetlib. This includes checksum and length fields. See the
//   packetlib library for the exact definition.
//
// To be "well-formed", a test vector must meet the following requirements:
// * Must specify at least 1 acceptable output.
// * Each input and output packet must:
//   * Be valid according to `packetlib::ValidatePacket` after computed fields
//     have been filled in.
//   * Contain a test packet ID/tag according to `ExtractTestPacketTag`.
//     This ID must be:
//     * Shared among all packets within the test vector.
//     * Unique among all test vectors.
// * The input must be of type `DATAPLANE` (other types may be supported in the
//   future).
// * Switch output packet ins must have valid metadata conforming to P4Runtime
//   "Section 16.1: Packet I/O".
absl::StatusOr<PacketTestVectorById> LegitimizeUserProvidedTestVectors(
    absl::Span<const PacketTestVector> user_provided_test_vectors,
    const pdpi::IrP4Info &ir_info);

} // namespace dvaas

#endif // PINS_USER_PROVIDED_PACKET_TEST_VECTOR_H_
