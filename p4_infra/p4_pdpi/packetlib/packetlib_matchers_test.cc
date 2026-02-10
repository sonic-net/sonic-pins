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

#include "p4_infra/p4_pdpi/packetlib/packetlib_matchers.h"

#include "gmock/gmock.h"
#include "google/protobuf/repeated_ptr_field.h"
#include "gtest/gtest.h"
#include "gutil/gutil/testing.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.pb.h"

namespace packetlib {
namespace {

using ::testing::ElementsAre;
using ::testing::Not;
using ::testing::ResultOf;

google::protobuf::RepeatedPtrField<Header> GetHeaders(const Packet& packet) {
  return packet.headers();
}

TEST(HasHeaderCaseTest, DoesHaveHeaderCase) {
  EXPECT_THAT(gutil::ParseProtoOrDie<Header>(R"pb(
                ethernet_header {}
              )pb"),
              HasHeaderCase(Header::kEthernetHeader));
  EXPECT_THAT(gutil::ParseProtoOrDie<Header>(R"pb(
                ipv4_header {}
              )pb"),
              HasHeaderCase(Header::kIpv4Header));
  EXPECT_THAT(
      gutil::ParseProtoOrDie<Packet>(R"pb(
        headers { ethernet_header {} }
        headers { ipv4_header {} }
        headers { udp_header {} }
      )pb"),
      ResultOf(GetHeaders, ElementsAre(HasHeaderCase(Header::kEthernetHeader),
                                       HasHeaderCase(Header::kIpv4Header),
                                       HasHeaderCase(Header::kUdpHeader))));
}

TEST(HasHeaderCaseTest, NotHasHeaderCase) {
  EXPECT_THAT(gutil::ParseProtoOrDie<Header>(R"pb()pb"),
              Not(HasHeaderCase(Header::kEthernetHeader)));
  EXPECT_THAT(gutil::ParseProtoOrDie<Header>(R"pb(
                ipv4_header {}
              )pb"),
              Not(HasHeaderCase(Header::kEthernetHeader)));
  EXPECT_THAT(gutil::ParseProtoOrDie<Header>(R"pb(
                ethernet_header {}
              )pb"),
              Not(HasHeaderCase(Header::kIpv4Header)));
}

TEST(HasHeaderCaseTest, Description) {
  auto describe = [](const auto& matcher) {
    return testing::DescribeMatcher<packetlib::Header>(matcher);
  };
  EXPECT_EQ(describe(HasHeaderCase(Header::kEthernetHeader)),
            "is a `packetlib.Header` protobuf message whose oneof field "
            "`header` has case `ethernet_header`");
  EXPECT_EQ(describe(Not(HasHeaderCase(Header::kEthernetHeader))),
            "is a `packetlib.Header` protobuf message whose oneof field "
            "`header` does not have case `ethernet_header`");
}

}  // namespace
}  // namespace packetlib
