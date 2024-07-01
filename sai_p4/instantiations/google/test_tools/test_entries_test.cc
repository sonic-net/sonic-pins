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
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"

namespace sai {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::testing::_;
using ::testing::SizeIs;

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

// -- PdEntryBuilder tests -----------------------------------------------------

TEST(PdEntryBuilder,
     GetDedupedEntriesReturnsNothingForDefaultConstructedBuilder) {
  EXPECT_THAT(PdEntryBuilder().GetDedupedEntries().entries(),
              testing::IsEmpty());
}

TEST(PdEntryBuilder, GetDedupedEntriesReturnsEntriesPassedToConstructor) {
  auto entries = gutil::ParseProtoOrDie<sai::TableEntries>(
      R"pb(
        entries { l3_admit_table_entry { controller_metadata: "test" } }
      )pb");
  EXPECT_THAT(PdEntryBuilder(entries).GetDedupedEntries(),
              EqualsProto(entries));
}

TEST(PdEntryBuilder, GetDedupedEntriesRemovesDuplicates) {
  auto entries = gutil::ParseProtoOrDie<sai::TableEntries>(
      R"pb(
        entries { l3_admit_table_entry { controller_metadata: "test" } }
        entries { l3_admit_table_entry { controller_metadata: "test" } }
      )pb");
  auto deduped_entries = gutil::ParseProtoOrDie<sai::TableEntries>(
      R"pb(
        entries { l3_admit_table_entry { controller_metadata: "test" } }
      )pb");
  EXPECT_THAT(PdEntryBuilder(entries).GetDedupedEntries(),
              EqualsProto(deduped_entries));
}

TEST(PdEntryBuilder, AddEntryPuntingAllPacketsDoesNotAddsEntry) {
  EXPECT_THAT(PdEntryBuilder()
                  .AddEntryPuntingAllPackets(PuntAction::kCopy)
                  .AddEntryPuntingAllPackets(PuntAction::kTrap)
                  .GetDedupedEntries()
                  .entries(),
              SizeIs(2));
}

TEST(PdEntryBuilder, AddEntriesForwardingIpPacketsToGivenPortAddsEntries) {
  EXPECT_THAT(PdEntryBuilder()
                  .AddEntriesForwardingIpPacketsToGivenPort("egress port")
                  .GetDedupedEntries()
                  .entries(),
              SizeIs(8));
}

TEST(PdEntryBuilder, AddVrfEntryAddsEntry) {
  EXPECT_THAT(PdEntryBuilder()
                  .AddVrfEntry("vrf-1")
                  .AddVrfEntry("vrf-2")
                  .AddVrfEntry("vrf-3")
                  .GetDedupedEntries()
                  .entries(),
              SizeIs(3));
}

TEST(PdEntryBuilder, AddEntryAdmittingAllPacketsToL3AddsEntry) {
  EXPECT_THAT(PdEntryBuilder()
                  .AddEntryAdmittingAllPacketsToL3()
                  .GetDedupedEntries()
                  .entries(),
              SizeIs(1));
}

TEST(PdEntryBuilder,
     AddDefaultRouteForwardingAllPacketsToGivenPortAddsEntries) {
  EXPECT_THAT(PdEntryBuilder()
                  .AddDefaultRouteForwardingAllPacketsToGivenPort(
                      "egress port 1", IpVersion::kIpv4, "vrf-1")
                  .AddDefaultRouteForwardingAllPacketsToGivenPort(
                      "egress port 2", IpVersion::kIpv6, "vrf-2")
                  .AddDefaultRouteForwardingAllPacketsToGivenPort(
                      "egress port 3", IpVersion::kIpv4And6, "vrf-3")
                  .GetDedupedEntries()
                  .entries(),
              SizeIs(13));
}

TEST(PdEntryBuilder, AddPreIngressAclEntryAssigningVrfForGivenIpTypeAddsEntry) {
  EXPECT_THAT(PdEntryBuilder()
                  .AddPreIngressAclEntryAssigningVrfForGivenIpType(
                      "vrf-1", IpVersion::kIpv4)
                  .AddPreIngressAclEntryAssigningVrfForGivenIpType(
                      "vrf-1", IpVersion::kIpv6)
                  .AddPreIngressAclEntryAssigningVrfForGivenIpType(
                      "vrf-1", IpVersion::kIpv4And6)
                  .GetDedupedEntries()
                  .entries(),
              SizeIs(3));
}

TEST(PdEntryBuilder,
     AddEntryDecappingAllIpInIpv6PacketsAndSettingVrfAddsEntry) {
  EXPECT_THAT(PdEntryBuilder()
                  .AddEntryDecappingAllIpInIpv6PacketsAndSettingVrf("vrf-1")
                  .AddEntryDecappingAllIpInIpv6PacketsAndSettingVrf("vrf-2")
                  .AddEntryDecappingAllIpInIpv6PacketsAndSettingVrf("vrf-3")
                  .GetDedupedEntries()
                  .entries(),
              SizeIs(3));
}

}  // namespace
}  // namespace sai
