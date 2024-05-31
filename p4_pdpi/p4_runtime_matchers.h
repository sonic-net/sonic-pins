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

#include <ostream>
#include <utility>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"

namespace pdpi {

// gMock matcher that checks if its argument, a `p4::v1::StreamMessageResponse`,
// contains a `p4::v1::PacketIn` whose `payload` parsed as a `packetlib::Packet`
// matches the given `inner_matcher`.
//
// Sample usage:
// ```
//   EXPECT_THAT(p4_runtime_session.ReadStreamChannelResponsesAndFinish(),
//               IsOkAndHolds(ElementsAre(IsPacketInWhoseParsedPayloadSatisfies(
//                   EqualsProto(expected_punt_packet)))));
// ```
//
// TODO: Replace this matcher with more-granular and more-reusable
// matchers.
template <class InnerMatcher>
testing::Matcher<const p4::v1::StreamMessageResponse&>
IsPacketInWhoseParsedPayloadSatisfies(InnerMatcher&& inner_matcher);

// == END OF PUBLIC API ========================================================
// Implementation details follow.

namespace internal {

class IsPacketInWhoseParsedPayloadSatisfiesMatcher {
 public:
  using is_gtest_matcher = void;
  using InnerMatcher = testing::Matcher<const packetlib::Packet&>;

  IsPacketInWhoseParsedPayloadSatisfiesMatcher(InnerMatcher&& inner_matcher)
      : inner_matcher_(inner_matcher) {}

  void DescribeTo(std::ostream* os, bool negate) const;
  void DescribeTo(std::ostream* os) const { DescribeTo(os, false); }
  void DescribeNegationTo(std::ostream* os) const { DescribeTo(os, true); }

  bool MatchAndExplain(const p4::v1::StreamMessageResponse& response,
                       testing::MatchResultListener* listener) const;

 private:
  InnerMatcher inner_matcher_;
};

}  // namespace internal

template <class InnerMatcher>
testing::Matcher<const p4::v1::StreamMessageResponse&>
IsPacketInWhoseParsedPayloadSatisfies(InnerMatcher&& inner_matcher) {
  return internal::IsPacketInWhoseParsedPayloadSatisfiesMatcher(
      testing::SafeMatcherCast<const packetlib::Packet&>(
          std::forward<InnerMatcher>(inner_matcher)));
}

}  // namespace pdpi

#endif  // PINS_P4_PDPI_P4_RUNTIME_MATCHERS_H_
