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

#ifndef PINS_TESTS_FORWARDING_TEST_VECTOR_H_
#define PINS_TESTS_FORWARDING_TEST_VECTOR_H_

#include <ostream>
#include <string>

#include "absl/container/btree_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "dvaas/test_vector.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"

namespace dvaas {

// A map of packet tags to corresponding test vectors.
using PacketTestVectorById = absl::btree_map<int, PacketTestVector>;

// Returns a string that should be included in the payload of test packets.
// This "tag" encodes the given test packet ID, which must be:
// * Uniform across all packets within a packet test vector, incl. input &
//   output packets.
// * Unique across different packet test vectors.
// Any Ethernet packet containing a tag returned by this function will
// be at least the minimum size required by the Ethernet protocol. 
std::string MakeTestPacketTagFromUniqueId(int unique_test_packet_id,
                                          absl::string_view description);

// Given a raw packet containing a tag returned by `MakeTestPacketTag`, extracts
// the ID from the tag. Returns an error if the raw packet has an unexpected
// format, e.g. for untagged packets.
// TODO: Implement and use a unified (open-source) API for test
// packet tag embedding and extraction.
absl::StatusOr<int> ExtractIdFromTaggedPacket(absl::string_view raw_packet);

// Given the hex string representation of a packet containing a tag, extract
// the ID from the tag. Returns an error if the raw packet has an unexpected
// format, e.g. for untagged packets. The hex string must be of the form
// "[0-9a-f]+", note that it omits the "0x" prefix.
absl::StatusOr<int> ExtractIdFromTaggedPacketInHex(
    absl::string_view packet_hex);

// Needed to make gUnit produce human-readable output in open source.
std::ostream &operator<<(std::ostream &os, const SwitchOutput &output);

// Updates the test tag (to `new_tag`) and all computed fields of all packets
// (input, acceptable outputs) in the given `packet_test_vector`. Returns an
// error if the packets are not already tagged.
absl::Status UpdateTestTag(PacketTestVector &packet_test_vector, int new_tag);

} // namespace dvaas

#endif // PINS_TESTS_FORWARDING_TEST_VECTOR_H_
