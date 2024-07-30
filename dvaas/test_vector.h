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

namespace dvaas {

// Given a tagged packet, extracts the tag in its payload. Returns an
// error if the payload has an unexpected format, e.g. for untagged packets.
// TODO: Implement and use a unified (open-source) API for test
// packet tag embedding and extraction.
absl::StatusOr<int> ExtractTestPacketTag(const packetlib::Packet& packet);

// Needed to make gUnit produce human-readable output in open source.
inline std::ostream& operator<<(std::ostream& os, const SwitchOutput& output) {
  return os << output.DebugString();
}

using PacketTestVectorById = absl::btree_map<int, PacketTestVector>;

// Holds a PacketTestVector along with the actual SUT output generated in
// response to the test vector's input. The actual output may be empty, if the
// switch drops the input packet. The test vector may be empty, if the switch
// generates packets that do not correspond to an input, or if the output cannot
// be mapped to a test input.
struct PacketTestVectorAndActualOutput {
  PacketTestVector packet_test_vector;
  SwitchOutput actual_output;
};

// Gets 'ingress_port' value from metadata in `packet_in`. Returns
// InvalidArgumentError if 'ingress_port' metadata is missing.
absl::StatusOr<std::string> GetIngressPortFromIrPacketIn(
    const pdpi::IrPacketIn& packet_in);

// Checks if the `actual_output` conforms to the `packet_test_vector`
// when ignoring the given `ignored_fields` and 'ignored_packet_in_metadata', if
// any. All `ignored_fields` should belong to packetlib::Packet. Returns a
// failure description in case of a mismatch, or `absl::nullopt` otherwise.
absl::optional<std::string> CheckForPacketTestVectorFailure(
    const PacketTestVector& packet_test_vector,
    const SwitchOutput& actual_output,
    const absl::flat_hash_set<std::string>& ignored_packet_in_metadata = {},
    const std::vector<const google::protobuf::FieldDescriptor*>&
        ignored_fields = {});

}  // namespace dvaas

#endif  // PINS_TESTS_FORWARDING_TEST_VECTOR_H_
