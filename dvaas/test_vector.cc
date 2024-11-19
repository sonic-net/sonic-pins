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

#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "gutil/proto.h"
#include "gutil/status.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "re2/re2.h"

namespace dvaas {

// All test packets (incl. input & output packets) must have payloads that
// contain an ID that matches this regular expression. This ID must be:
// * Uniform across all packets within a packet test vector.
// * Unique across different packet test vectors.
inline constexpr LazyRE2 kTestPacketIdRegexp{R"(test packet #([0-9]+))"};

std::string MakeTestPacketTagFromUniqueId(int unique_test_packet_id) {
  return absl::StrCat("test packet #", unique_test_packet_id);
}

absl::StatusOr<int> ExtractTestPacketTag(const packetlib::Packet& packet) {
  int tag;
  if (!RE2::PartialMatch(packet.payload(), *kTestPacketIdRegexp, &tag)) {
    return gutil::InvalidArgumentErrorBuilder()
           << "test packets must contain a tag of the form '"
           << kTestPacketIdRegexp->pattern()
           << "' in their payload, but the given packet with payload '"
           << packet.payload() << "' does not:\n"
           << gutil::PrintTextProto(packet);
  }
  return tag;
}

std::ostream& operator<<(std::ostream& os, const SwitchOutput& output) {
  return os << output.DebugString();
}

}  // namespace dvaas
