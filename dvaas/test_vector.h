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
#include <vector>

#include "absl/container/btree_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/status/statusor.h"
#include "absl/types/optional.h"
#include "dvaas/test_vector.pb.h"
#include "google/protobuf/descriptor.h"
#include "p4_pdpi/ir.pb.h"
#include "re2/re2.h"

namespace dvaas {

// Returns a string that must be included in the payload of test packets.
// This "tag" encodes the given test packet ID, which must be:
// * Uniform across all packets within a packet test vector, incl. input &
//   output packets.
// * Unique across different packet test vectors.
std::string MakeTestPacketTagFromUniqueId(int unique_test_packet_id);

// Given a tagged packet (according to `MakeTestPacketTag`), extracts the ID
// from the tag in its payload. Returns an error if the payload has an
// unexpected format, e.g. for untagged packets.
// TODO: Implement and use a unified (open-source) API for test
// packet tag embedding and extraction.
absl::StatusOr<int> ExtractTestPacketTag(const packetlib::Packet& packet);

// Needed to make gUnit produce human-readable output in open source.
std::ostream& operator<<(std::ostream& os, const SwitchOutput& output);

using PacketTestVectorById = absl::btree_map<int, PacketTestVector>;

}  // namespace dvaas

#endif  // PINS_TESTS_FORWARDING_TEST_VECTOR_H_
