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

#include "sai_p4/instantiations/google/test_tools/test_entries.h"

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"

namespace sai {
namespace {

using gutil::IsOkAndHolds;
using testing::_;

using TestEntriesTest = ::testing::TestWithParam<sai::Instantiation>;

TEST_P(TestEntriesTest, MakePiEntryPuntingAllPacketsDoesNotError) {
  ASSERT_THAT(MakePiEntryPuntingAllPackets(PuntAction::kCopy,
                                           sai::GetIrP4Info(GetParam())),
              IsOkAndHolds(_));
  ASSERT_THAT(MakePiEntryPuntingAllPackets(PuntAction::kTrap,
                                           sai::GetIrP4Info(GetParam())),
              IsOkAndHolds(_));
}
TEST_P(TestEntriesTest, MakeIrEntryPuntingAllPacketsDoesNotError) {
  ASSERT_THAT(MakeIrEntryPuntingAllPackets(PuntAction::kCopy,
                                           sai::GetIrP4Info(GetParam())),
              IsOkAndHolds(_));
  ASSERT_THAT(MakeIrEntryPuntingAllPackets(PuntAction::kTrap,
                                           sai::GetIrP4Info(GetParam())),
              IsOkAndHolds(_));
}
TEST_P(TestEntriesTest, MakePdEntryPuntingAllPacketsDoesNotError) {
  ASSERT_THAT(MakePdEntryPuntingAllPackets(PuntAction::kCopy), IsOkAndHolds(_));
  ASSERT_THAT(MakePdEntryPuntingAllPackets(PuntAction::kTrap), IsOkAndHolds(_));
}

TEST_P(TestEntriesTest,
       MakePiEntriesForwardingIpPacketsToGivenPortDoesNotError) {
  ASSERT_THAT(MakePiEntriesForwardingIpPacketsToGivenPort(
                  /*egress_port=*/"42", sai::GetIrP4Info(GetParam())),
              IsOkAndHolds(_));
}
TEST_P(TestEntriesTest,
       MakeIrEntriesForwardingIpPacketsToGivenPortDoesNotError) {
  ASSERT_THAT(MakeIrEntriesForwardingIpPacketsToGivenPort(
                  /*egress_port=*/"42", sai::GetIrP4Info(GetParam())),
              IsOkAndHolds(_));
}
TEST_P(TestEntriesTest,
       MakePdEntriesForwardingIpPacketsToGivenPortDoesNotError) {
  ASSERT_THAT(MakePdEntriesForwardingIpPacketsToGivenPort(/*egress_port=*/"42"),
              IsOkAndHolds(_));
}

INSTANTIATE_TEST_SUITE_P(, TestEntriesTest,
                         testing::ValuesIn(sai::AllSaiInstantiations()),
                         [](const auto& info) -> std::string {
                           return sai::InstantiationToString(info.param);
                         });

}  // namespace
}  // namespace sai
