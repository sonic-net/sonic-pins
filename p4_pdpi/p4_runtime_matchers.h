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

#ifndef PINS_P4_PDPI_P4_RUNTIME_MATCHERS_H_
#define PINS_P4_PDPI_P4_RUNTIME_MATCHERS_H_

#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"

namespace pdpi {

// gMock matcher that checks if its argument, a
// `p4::v1::StreamMessageResponse`, contains a `p4::v1::PacketIn`.
//
// Sample usage:
// ```
// EXPECT_THAT(p4_runtime_session.ReadStreamChannelResponsesAndFinish(),
//             IsOkAndHolds(Each(HasPacketIn())));
// ```
MATCHER(HasPacketIn,
        absl::StrCat("is a P4Runtime `StreamMessageResponse` containing ",
                     negation ? "no" : "a", " `packet`")) {
  auto HasPacket = gutil::HasOneofCaseMatcher<p4::v1::StreamMessageResponse>(
      "update", p4::v1::StreamMessageResponse::kPacket);
  return testing::ExplainMatchResult(HasPacket, arg, result_listener);
}

// gMock matcher that checks if its argument, a
// `p4::v1::StreamMessageResponse`, contains a `p4::v1::PacketIn` that matches
// the given `packet_in_matcher`.
//
// Sample usage:
// ```
// EXPECT_THAT(p4_runtime_session.GetNextStreamMessage(absl::Seconds(1)),
//             IsOkAndHolds(HasPacketIn(EqualsProto(expected_packet_in))));
// ```
MATCHER_P(HasPacketIn, packet_in_matcher,
          absl::StrCat(testing::DescribeMatcher<p4::v1::StreamMessageResponse>(
                           HasPacketIn(), negation),
                       negation ? ", or a `packet` that " : " that ",
                       testing::DescribeMatcher<p4::v1::PacketIn>(
                           packet_in_matcher, negation))) {
  return testing::ExplainMatchResult(HasPacketIn(), arg, result_listener) &&
         testing::ExplainMatchResult(packet_in_matcher, arg.packet(),
                                     result_listener);
}

// gMock matcher that checks if its argument, a `p4::v1::PacketIn`, has a
// `payload` that, parsed as a `packetlib::Packet` matches the given
// `parsed_payload_matcher`.
//
// Sample usage:
// ```
// EXPECT_THAT(p4_runtime_session.ReadStreamChannelResponsesAndFinish(),
//             IsOkAndHolds(ElementsAre(HasPacketIn(
//                 ParsedPayloadIs(EqualsProto(expected_punt_packet))))));
// ```
MATCHER_P(ParsedPayloadIs, parsed_payload_matcher,
          absl::StrCat(
              "contains a `payload` that (when parsed as a packetlib.Packet) ",
              testing::DescribeMatcher<packetlib::Packet>(
                  parsed_payload_matcher, negation))) {
  const p4::v1::PacketIn &packet_in = arg;
  packetlib::Packet packet = packetlib::ParsePacket(packet_in.payload());
  *result_listener << ", whose `payload` parses to the packetlib.Packet <\n"
                   << packet.DebugString() << ">, ";
  return testing::ExplainMatchResult(parsed_payload_matcher, packet,
                                     result_listener);
}

} // namespace pdpi

#endif  // PINS_P4_PDPI_P4_RUNTIME_MATCHERS_H_
