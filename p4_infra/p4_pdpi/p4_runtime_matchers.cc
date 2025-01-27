// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "p4_pdpi/p4_runtime_matchers.h"

#include <ostream>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"

namespace pdpi::internal {

void IsPacketInWhoseParsedPayloadSatisfiesMatcher::DescribeTo(
    std::ostream* os, bool negate) const {
  if (os == nullptr) return;
  *os << "is " << (negate ? "not " : "")
      << "a P4Runtime StreamMessageResponse containing a `packet` whose "
         "`payload` parsed as a packetlib.Packet ";
  inner_matcher_.DescribeTo(os);
}

bool IsPacketInWhoseParsedPayloadSatisfiesMatcher::MatchAndExplain(
    const p4::v1::StreamMessageResponse& response,
    testing::MatchResultListener* listener) const {
  auto HasPacket = gutil::HasOneofCaseMatcher<p4::v1::StreamMessageResponse>(
      "update", p4::v1::StreamMessageResponse::kPacket);
  bool has_packet = testing::ExplainMatchResult(HasPacket, response, listener);
  if (!has_packet) return false;
  packetlib::Packet packet =
      packetlib::ParsePacket(response.packet().payload());
  *listener << ", whose `payload` parses to the packetlib.Packet <\n"
            << packet.DebugString() << ">, ";
  return testing::ExplainMatchResult(inner_matcher_, packet, listener);
}

}  // namespace pdpi::internal
