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

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/testing.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/packetlib/packetlib.h"

namespace pdpi {
namespace {

using ::gutil::EqualsProto;
using ::p4::v1::StreamMessageResponse;
using ::testing::_;
using ::testing::Not;

TEST(IsPacketInWhoseParsedPayloadSatisfiesTest, IsPacketIn) {
  EXPECT_THAT(gutil::ParseProtoOrDie<StreamMessageResponse>(R"pb(
                packet {}
              )pb"),
              IsPacketInWhoseParsedPayloadSatisfies(_));
  EXPECT_THAT(gutil::ParseProtoOrDie<StreamMessageResponse>(R"pb(
                packet { payload: "1234" }
              )pb"),
              IsPacketInWhoseParsedPayloadSatisfies(_));
}

TEST(IsPacketInWhoseParsedPayloadSatisfiesTest, NotIsPacketIn) {
  EXPECT_THAT(gutil::ParseProtoOrDie<StreamMessageResponse>(R"pb()pb"),
              Not(IsPacketInWhoseParsedPayloadSatisfies(_)));
  EXPECT_THAT(gutil::ParseProtoOrDie<StreamMessageResponse>(R"pb(
                arbitration {}
              )pb"),
              Not(IsPacketInWhoseParsedPayloadSatisfies(_)));
  EXPECT_THAT(gutil::ParseProtoOrDie<StreamMessageResponse>(R"pb(
                digest {}
              )pb"),
              Not(IsPacketInWhoseParsedPayloadSatisfies(_)));
}

TEST(IsPacketInWhoseParsedPayloadSatisfiesTest, IsParticularPacketIn) {
  EXPECT_THAT(gutil::ParseProtoOrDie<StreamMessageResponse>(R"pb(
                packet { payload: "my amazing packet" }
              )pb"),
              IsPacketInWhoseParsedPayloadSatisfies(
                  EqualsProto(packetlib::ParsePacket("my amazing packet"))));
  EXPECT_THAT(gutil::ParseProtoOrDie<StreamMessageResponse>(R"pb(
                packet { payload: "my amazing packet" }
              )pb"),
              IsPacketInWhoseParsedPayloadSatisfies(
                  Not(EqualsProto(packetlib::ParsePacket("another packet")))));
  EXPECT_THAT(gutil::ParseProtoOrDie<StreamMessageResponse>(R"pb(
                packet { payload: "my amazing packet" }
              )pb"),
              Not(IsPacketInWhoseParsedPayloadSatisfies(
                  EqualsProto(packetlib::ParsePacket("another packet")))));
}

TEST(IsPacketInWhoseParsedPayloadSatisfiesTest, Description) {
  auto describe = [](const auto& matcher) {
    return testing::DescribeMatcher<const StreamMessageResponse&>(matcher);
  };
  EXPECT_EQ(describe(IsPacketInWhoseParsedPayloadSatisfies(_)),
            "is a P4Runtime StreamMessageResponse containing a `packet` whose "
            "`payload` parsed as a packetlib.Packet is anything");
  EXPECT_EQ(describe(Not(IsPacketInWhoseParsedPayloadSatisfies(
                EqualsProto(R"pb(payload: "test packet")pb")))),
            "is not a P4Runtime StreamMessageResponse containing a `packet` "
            "whose `payload` parsed as a packetlib.Packet is equal to <\n"
            "payload: \"test packet\">");
}

}  // namespace
}  // namespace pdpi
