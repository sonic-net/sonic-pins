// Copyright 2023 Google LLC
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

#include "p4_infra/p4_runtime/p4_runtime_matchers.h"

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/testing.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/packetlib/packetlib.h"

namespace p4_runtime {
namespace {

using ::gutil::EqualsProto;
using ::p4::v1::PacketIn;
using ::p4::v1::StreamMessageResponse;
using ::testing::_;
using ::testing::Not;

TEST(HasPacketTest, DoesHavePacket) {
  EXPECT_THAT(gutil::ParseProtoOrDie<StreamMessageResponse>(R"pb(
                packet {}
              )pb"),
              HasPacketIn());
  EXPECT_THAT(gutil::ParseProtoOrDie<StreamMessageResponse>(R"pb(
                packet {}
              )pb"),
              HasPacketIn(_));
  EXPECT_THAT(gutil::ParseProtoOrDie<StreamMessageResponse>(R"pb(
                packet { payload: "hi" }
              )pb"),
              HasPacketIn(EqualsProto(R"pb(payload: "hi")pb")));
  EXPECT_THAT(gutil::ParseProtoOrDie<StreamMessageResponse>(R"pb(
                packet { payload: "hi" }
              )pb"),
              HasPacketIn(Not(EqualsProto(""))));
}

TEST(HasPacketTest, DoesNotHavePacket) {
  EXPECT_THAT(gutil::ParseProtoOrDie<StreamMessageResponse>(""),
              Not(HasPacketIn()));
  EXPECT_THAT(gutil::ParseProtoOrDie<StreamMessageResponse>(""),
              Not(HasPacketIn(_)));
  EXPECT_THAT(gutil::ParseProtoOrDie<StreamMessageResponse>(R"pb(
                arbitration {}
              )pb"),
              Not(HasPacketIn()));
  EXPECT_THAT(gutil::ParseProtoOrDie<StreamMessageResponse>(R"pb(
                arbitration {}
              )pb"),
              Not(HasPacketIn(_)));
}

TEST(HasPacketTest, Describtion) {
  auto describe = [](const auto& matcher) {
    return testing::DescribeMatcher<const StreamMessageResponse&>(matcher);
  };

  EXPECT_EQ(describe(HasPacketIn()),
            "is a P4Runtime `StreamMessageResponse` containing a `packet`");
  EXPECT_EQ(describe(HasPacketIn(_)),
            "is a P4Runtime `StreamMessageResponse` containing a `packet`"
            " that is anything");

  EXPECT_EQ(describe(Not(HasPacketIn())),
            "is a P4Runtime `StreamMessageResponse` containing no `packet`");
  EXPECT_EQ(describe(Not(HasPacketIn(_))),
            "is a P4Runtime `StreamMessageResponse` containing no `packet`, or "
            "a `packet` that never matches");
}

TEST(ParsedPayloadIsTest, PayloadIs) {
  EXPECT_THAT(PacketIn(), ParsedPayloadIs(_));
  EXPECT_THAT(gutil::ParseProtoOrDie<PacketIn>(R"(payload: "1234")"),
              ParsedPayloadIs(EqualsProto(packetlib::ParsePacket("1234"))));
  EXPECT_THAT(PacketIn(), ParsedPayloadIs(_));
  EXPECT_THAT(
      gutil::ParseProtoOrDie<PacketIn>(R"(payload: "1234")"),
      ParsedPayloadIs(Not(EqualsProto(packetlib::ParsePacket("4321")))));
}

TEST(ParsedPayloadIsTest, PayloadIsNot) {
  EXPECT_THAT(
      PacketIn(),
      Not(ParsedPayloadIs(EqualsProto(packetlib::ParsePacket("1234")))));
  EXPECT_THAT(PacketIn(), Not(ParsedPayloadIs(Not(_))));
  EXPECT_THAT(
      gutil::ParseProtoOrDie<PacketIn>(R"(payload: "1234")"),
      Not(ParsedPayloadIs(EqualsProto(packetlib::ParsePacket("4321")))));
}

TEST(ParsedPayloadIsTest, Description) {
  auto describe = [](const auto& matcher) {
    return testing::DescribeMatcher<const PacketIn&>(matcher);
  };

  EXPECT_EQ(describe(ParsedPayloadIs(_)),
            "contains a `payload` that (when parsed as a packetlib.Packet) is "
            "anything");
  EXPECT_EQ(describe(ParsedPayloadIs(EqualsProto("nonsense"))),
            "contains a `payload` that (when parsed as a packetlib.Packet) is "
            "equal to <\nnonsense>");

  EXPECT_EQ(describe(Not(ParsedPayloadIs(_))),
            "contains a `payload` that (when parsed as a packetlib.Packet) "
            "never matches");
  EXPECT_EQ(describe(Not(ParsedPayloadIs(EqualsProto("nonsense")))),
            "contains a `payload` that (when parsed as a packetlib.Packet) "
            "is not equal to <\nnonsense>");
  EXPECT_EQ(describe(Not(ParsedPayloadIs(Not(EqualsProto("nonsense"))))),
            "contains a `payload` that (when parsed as a packetlib.Packet) "
            "is equal to <\nnonsense>");
}

// Make sure the `HasPacketIn` and `ParsedPayloadIs` matchers work well when
// combined.
TEST(HasPacketInParsedPayloadIsTest, Description) {
  auto describe = [](const auto& matcher) {
    return testing::DescribeMatcher<const StreamMessageResponse&>(matcher);
  };
  EXPECT_EQ(describe(HasPacketIn(ParsedPayloadIs(_))),
            "is a P4Runtime `StreamMessageResponse` containing a `packet` that "
            "contains a `payload` that (when parsed as a packetlib.Packet) is "
            "anything");
  EXPECT_EQ(describe(Not(HasPacketIn(ParsedPayloadIs(
                EqualsProto(R"pb(payload: "test packet")pb"))))),
            "is a P4Runtime `StreamMessageResponse` containing no `packet`, or "
            "a `packet` that contains a `payload` that (when parsed as a "
            "packetlib.Packet) is not equal to <\npayload: \"test packet\">");
}

}  // namespace
}  // namespace p4_runtime
