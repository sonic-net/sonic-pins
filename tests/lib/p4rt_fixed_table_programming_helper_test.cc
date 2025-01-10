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
#include "tests/lib/p4rt_fixed_table_programming_helper.h"

#include "absl/status/status.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"

namespace pins {
namespace {

using ::gutil::StatusIs;
using ::testing::HasSubstr;

MATCHER_P(HasExactMatch, value, "") {
  for (const auto& match_field : arg.entity().table_entry().match()) {
    if (match_field.exact().value() == value) {
      return true;
    }
  }
  return false;
}

MATCHER_P2(HasLpmMatch, value, prefix, "") {
  for (const auto& match_field : arg.entity().table_entry().match()) {
    if (match_field.lpm().value() == value &&
        match_field.lpm().prefix_len() == prefix) {
      return true;
    }
  }
  return false;
}

MATCHER_P2(HasTernaryMatch, value, mask, "") {
  for (const auto& match_field : arg.entity().table_entry().match()) {
    if (match_field.ternary().value() == value &&
        match_field.ternary().mask() == mask) {
      return true;
    }
  }
  return false;
}

MATCHER_P(HasOptionalMatch, value, "") {
  for (const auto& match_field : arg.entity().table_entry().match()) {
    if (match_field.optional().value() == value) {
      return true;
    }
  }
  return false;
}

MATCHER_P(HasActionParam, value, "") {
  for (const auto& action_param :
       arg.entity().table_entry().action().action().params()) {
    if (action_param.value() == value) {
      return true;
    }
  }
  return false;
}

// The L3 route programming tests verify that a given P4Info can translate all
// the flows needed to do L3 routing.
using L3RouteProgrammingTest = testing::TestWithParam<sai::Instantiation>;

TEST_P(L3RouteProgrammingTest, RouterInterfaceId) {
  ASSERT_OK_AND_ASSIGN(p4::v1::Update pi_update,
		       pins::RouterInterfaceTableUpdate(
                           sai::GetIrP4Info(GetParam()), p4::v1::Update::INSERT,
                           /*router_interface_id=*/"rid-0",
                           /*port=*/"1",
                           /*src_mac=*/"00:01:02:03:04:05"));

  EXPECT_THAT(pi_update, HasExactMatch("rid-0"));
  EXPECT_THAT(pi_update, HasActionParam("1"));
  EXPECT_THAT(pi_update, HasActionParam("\001\002\003\004\005"));
}

TEST_P(L3RouteProgrammingTest, RouterInterfaceIdFailsWithInvalidMacAddress) {
  EXPECT_THAT(pins::RouterInterfaceTableUpdate(sai::GetIrP4Info(GetParam()),
                                         p4::v1::Update::INSERT,
                                         /*router_interface_id=*/"rid-0",
                                         /*port=*/"1",
                                         /*src_mac=*/"invalid_format"),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       HasSubstr("Invalid MAC address")));
}

TEST_P(L3RouteProgrammingTest, NeighborId) {
  ASSERT_OK_AND_ASSIGN(
      p4::v1::Update pi_update,
      pins::NeighborTableUpdate(sai::GetIrP4Info(GetParam()), p4::v1::Update::INSERT,
                          /*router_interface_id=*/"rid-1",
                          /*neighbor_id=*/"::1",
                          /*dst_mac=*/"00:01:02:03:04:05"));

  EXPECT_THAT(pi_update, HasExactMatch("rid-1"));
  EXPECT_THAT(pi_update, HasExactMatch("\001"));
  EXPECT_THAT(pi_update, HasActionParam("\001\002\003\004\005"));
}

TEST_P(L3RouteProgrammingTest, NeighborIdFailsWithInvalidMacAddress) {
  EXPECT_THAT(
      pins::NeighborTableUpdate(sai::GetIrP4Info(GetParam()), p4::v1::Update::INSERT,
                          /*router_interface_id=*/"rid-1",
                          /*neighbor_id=*/"fe80::201:02ff:fe03:0405",
                          /*dst_mac=*/"invalid_format"),
      StatusIs(absl::StatusCode::kInvalidArgument,
               HasSubstr("Invalid MAC address")));
}

TEST_P(L3RouteProgrammingTest, NexthopId) {
  ASSERT_OK_AND_ASSIGN(
      p4::v1::Update pi_update,
      NexthopTableUpdate(sai::GetIrP4Info(GetParam()), p4::v1::Update::INSERT,
                         /*nexthop_id=*/"nexthop-2",
                         /*router_interface_id=*/"rid-2",
                         /*neighbor_id=*/"::1"));
  EXPECT_THAT(pi_update, HasExactMatch("nexthop-2"));
  EXPECT_THAT(pi_update, HasActionParam("rid-2"));
  EXPECT_THAT(pi_update, HasActionParam("\001"));
}

TEST_P(L3RouteProgrammingTest, VrfTableAddFailsWithEmptyId) {
  EXPECT_THAT(
      pins::VrfTableUpdate(sai::GetIrP4Info(GetParam()), p4::v1::Update::INSERT,
                     /*vrf_id=*/""),
      StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_P(L3RouteProgrammingTest, Ipv4TableDoesNotRequireAnAction) {
  // The helper class will assume a default (e.g. drop).
  ASSERT_OK_AND_ASSIGN(
      p4::v1::Update pi_update,
      pins::Ipv4TableUpdate(sai::GetIrP4Info(GetParam()), p4::v1::Update::INSERT,
                      pins::IpTableOptions{.vrf_id = "vrf-0"}));

  EXPECT_THAT(pi_update, HasExactMatch("vrf-0"));
}

TEST_P(L3RouteProgrammingTest, Ipv4TableWithSetNexthopAction) {
  ASSERT_OK_AND_ASSIGN(
      p4::v1::Update pi_update,
      pins::Ipv4TableUpdate(sai::GetIrP4Info(GetParam()), p4::v1::Update::INSERT,
                      pins::IpTableOptions{
                          .vrf_id = "vrf-0",
                          .dst_addr_lpm = std::make_pair("10.1.1.1", 32),
                          .action = pins::IpTableOptions::Action::kSetNextHopId,
                          .nexthop_id = "nexthop-0",
                      }));

  EXPECT_THAT(pi_update, HasExactMatch("vrf-0"));
  EXPECT_THAT(pi_update, HasLpmMatch("\n\001\001\001", 32));
  EXPECT_THAT(pi_update, HasActionParam("nexthop-0"));
}

TEST_P(L3RouteProgrammingTest, Ipv4TableEntryFailsWihInvalidParameters) {
  EXPECT_THAT(
      pins::Ipv4TableUpdate(sai::GetIrP4Info(GetParam()), p4::v1::Update::INSERT,
                      pins::IpTableOptions{
                          .vrf_id = "vrf-0",
                          .action = pins::IpTableOptions::Action::kDrop,
                          .nexthop_id = "nexthop-0",
                      }),
      StatusIs(absl::StatusCode::kInvalidArgument,
               HasSubstr("Expected 0 parameters")));
}

TEST_P(L3RouteProgrammingTest, L3AdmitTableWithoutInPort) {
  ASSERT_OK_AND_ASSIGN(
      p4::v1::Update pi_update,
      pins::L3AdmitTableUpdate(sai::GetIrP4Info(GetParam()), p4::v1::Update::INSERT,
                         pins::L3AdmitOptions{
                             .priority = 10,
                             .dst_mac = std::make_pair("01:02:03:04:05:06",
                                                       "FF:FF:FF:FF:FF:FF"),
                         }));

  EXPECT_THAT(pi_update, HasTernaryMatch("\001\002\003\004\005\006",
                                         "\377\377\377\377\377\377"));
}

TEST_P(L3RouteProgrammingTest, L3AdmitTableWithInPort) {
  ASSERT_OK_AND_ASSIGN(
      p4::v1::Update pi_update,
      pins::L3AdmitTableUpdate(sai::GetIrP4Info(GetParam()), p4::v1::Update::INSERT,
                         pins::L3AdmitOptions{
                             .priority = 10,
                             .dst_mac = std::make_pair("01:02:03:04:05:06",
                                                       "FF:FF:FF:FF:FF:FF"),
                             .in_port = "in-port-1",
                         }));

  EXPECT_THAT(pi_update, HasOptionalMatch("in-port-1"));
  EXPECT_THAT(pi_update, HasTernaryMatch("\001\002\003\004\005\006",
                                         "\377\377\377\377\377\377"));
}

TEST_P(L3RouteProgrammingTest, L3AdmitTableMustSetPriority) {
  EXPECT_THAT(
      pins::L3AdmitTableUpdate(sai::GetIrP4Info(GetParam()), p4::v1::Update::INSERT,
                         pins::L3AdmitOptions{
                             .dst_mac = std::make_pair("01:02:03:04:05:06",
                                                       "FF:FF:FF:FF:FF:FF"),
                         }),
      StatusIs(absl::StatusCode::kInvalidArgument,
               HasSubstr("require a positive non-zero priority")));
}

INSTANTIATE_TEST_SUITE_P(
    L3RouteProgrammingTestInstance, L3RouteProgrammingTest,
    testing::Values(sai::Instantiation::kMiddleblock,
                    sai::Instantiation::kFabricBorderRouter),
    [](const testing::TestParamInfo<L3RouteProgrammingTest::ParamType>& param) {
      return sai::InstantiationToString(param.param);
    });

}  // namespace
}  // namespace pins
