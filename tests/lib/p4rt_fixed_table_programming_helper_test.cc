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

#include <list>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/types/span.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"

namespace pins {
namespace {

using ::gutil::StatusIs;
using ::testing::HasSubstr;
using ::testing::StrEq;

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

MATCHER_P2(HasReplica, port, instance, "") {
  for (const auto &replica : arg.entity()
                                 .packet_replication_engine_entry()
                                 .multicast_group_entry()
                                 .replicas()) {
    if (replica.port() == port && replica.instance() == instance) {
      return true;
    }
  }
  return false;
}

MATCHER_P(HasGroupId, id, "") {
  if (arg.entity()
          .packet_replication_engine_entry()
          .multicast_group_entry()
          .multicast_group_id() == id) {
    return true;
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

TEST_P(L3RouteProgrammingTest, VlanEntry) {
  ASSERT_OK_AND_ASSIGN(p4::v1::Update pi_update,
                       VlanTableUpdate(sai::GetIrP4Info(GetParam()),
                                       p4::v1::Update::INSERT, /*vlan=*/2));
  EXPECT_THAT(pi_update, HasExactMatch("\002"));
}

TEST_P(L3RouteProgrammingTest, VlanMemberTagEntry) {
  ASSERT_OK_AND_ASSIGN(p4::v1::Update pi_update,
                       VlanMemberTableUpdate(
                           sai::GetIrP4Info(GetParam()), p4::v1::Update::INSERT,
                           /*port_id=*/1, /*vlan=*/2, /*tag=*/true));
  EXPECT_THAT(pi_update, HasExactMatch("\002"));
  EXPECT_THAT(pi_update, HasExactMatch("1"));
}

TEST_P(L3RouteProgrammingTest, VlanMemberUntagEntry) {
  ASSERT_OK_AND_ASSIGN(p4::v1::Update pi_update,
                       VlanMemberTableUpdate(
                           sai::GetIrP4Info(GetParam()), p4::v1::Update::INSERT,
                           /*port_id=*/1, /*vlan=*/2, /*tag=*/false));
  EXPECT_THAT(pi_update, HasExactMatch("\002"));
  EXPECT_THAT(pi_update, HasExactMatch("1"));
}

TEST_P(L3RouteProgrammingTest, MulticastRouterInterfaceEntry) {
  MulticastReplica replica = MulticastReplica(/*port=*/"1", /*instance=*/0x120,
                                              /*src_mac=*/"00:01:02:03:04:05",
                                              /*vlan=*/2, /*is_ip_mcast=*/true);
  ASSERT_OK_AND_ASSIGN(
      p4::v1::Update pi_update,
      MulticastRouterInterfaceTableUpdate(sai::GetIrP4Info(GetParam()),
                                          p4::v1::Update::INSERT, replica));

  EXPECT_THAT(pi_update, HasExactMatch("1"));
  EXPECT_THAT(pi_update, HasExactMatch("\x01\x20"));
  EXPECT_THAT(pi_update, HasActionParam("\001\002\003\004\005"));
  EXPECT_THAT(pi_update, HasActionParam("\002"));
}

TEST_P(L3RouteProgrammingTest, L2MulticastRouterInterfaceEntry) {
  MulticastReplica replica =
      MulticastReplica(/*port=*/"1", /*instance=*/0x120,
                       /*src_mac=*/"00:01:02:03:04:05",
                       /*vlan=*/2, /*is_ip_mcast=*/false);
  ASSERT_OK_AND_ASSIGN(
      p4::v1::Update pi_update,
      MulticastRouterInterfaceTableUpdate(sai::GetIrP4Info(GetParam()),
                                          p4::v1::Update::INSERT, replica));

  EXPECT_THAT(pi_update, HasExactMatch("1"));
  EXPECT_THAT(pi_update, HasExactMatch("\x01\x20"));
}

TEST_P(L3RouteProgrammingTest,
       MulticastRouterInterfaceEntryCreatedSuccessfullyWhenInstanceIsZero) {
  MulticastReplica replica = MulticastReplica(/*port=*/"1", /*instance=*/0,
                                              /*src_mac=*/"00:01:02:03:04:05",
                                              /*vlan=*/2, /*is_ip_mcast=*/true);
  ASSERT_OK_AND_ASSIGN(
      p4::v1::Update pi_update,
      MulticastRouterInterfaceTableUpdate(sai::GetIrP4Info(GetParam()),
                                          p4::v1::Update::INSERT, replica));

  EXPECT_THAT(pi_update, HasExactMatch("1"));
  EXPECT_THAT(pi_update, HasExactMatch(std::string("\0", 1)));
  EXPECT_THAT(pi_update, HasActionParam("\001\002\003\004\005"));
  EXPECT_THAT(pi_update, HasActionParam("\002"));
}

TEST_P(L3RouteProgrammingTest,
       MulticastRouterInterfaceEntryFailsWithInvalidMacAddress) {
  MulticastReplica replica = MulticastReplica(/*port=*/"1", /*instance=*/0x120,
                                              /*src_mac=*/"invalid_format",
                                              /*vlan=*/2, /*is_ip_mcast=*/true);
  EXPECT_THAT(MulticastRouterInterfaceTableUpdate(sai::GetIrP4Info(GetParam()),
                                                  p4::v1::Update::INSERT,
                                                  replica),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       HasSubstr("Invalid MAC address")));
}

TEST_P(L3RouteProgrammingTest, MulticastGroupEntry) {
  std::vector<MulticastReplica> replicas;
  replicas.push_back(MulticastReplica(/*port=*/"1", /*instance=*/4,
                                      /*src_mac=*/"00:01:02:03:04:05",
                                      /*vlan=*/2, /*is_ip_mcast=*/true));
  replicas.push_back(MulticastReplica(/*port=*/"2", /*instance=*/3,
                                      /*src_mac=*/"00:01:02:03:04:05",
                                      /*vlan=*/2, /*is_ip_mcast=*/true));
  absl::Span<MulticastReplica> replicas_span{replicas};
  ASSERT_OK_AND_ASSIGN(p4::v1::Update pi_update,
                       MulticastGroupUpdate(sai::GetIrP4Info(GetParam()),
                                            p4::v1::Update::INSERT,
                                            /*group_id=*/1, replicas_span));
  EXPECT_THAT(pi_update, HasGroupId(1));
  EXPECT_THAT(pi_update, HasReplica("1", 4));
  EXPECT_THAT(pi_update, HasReplica("2", 3));
}

TEST_P(L3RouteProgrammingTest, Ipv4MulticastRouteEntry) {
  ASSERT_OK_AND_ASSIGN(
      p4::v1::Update pi_update,
      Ipv4MulticastRouteUpdate(sai::GetIrP4Info(GetParam()),
                               p4::v1::Update::INSERT, "vrf-0", "10.1.1.1",
                               /*group_id=*/1));

  EXPECT_THAT(pi_update, HasExactMatch("vrf-0"));
  EXPECT_THAT(pi_update, HasExactMatch("\n\001\001\001"));
  EXPECT_THAT(pi_update, HasActionParam("\001"));
}

TEST_P(L3RouteProgrammingTest, Ipv6MulticastRouteEntry) {
  ASSERT_OK_AND_ASSIGN(
      p4::v1::Update pi_update,
      Ipv6MulticastRouteUpdate(sai::GetIrP4Info(GetParam()),
                               p4::v1::Update::INSERT, "vrf-0", "2000::",
                               /*group_id=*/1));

  EXPECT_THAT(pi_update, HasExactMatch("vrf-0"));
  std::string ipv6_addr(
      " \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000", 16);
  EXPECT_THAT(pi_update, HasExactMatch(ipv6_addr));
  EXPECT_THAT(pi_update, HasActionParam("\001"));
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

TEST_P(L3RouteProgrammingTest, TunnelEntry) {
  ASSERT_OK_AND_ASSIGN(p4::v1::Update pi_update,
                       TunnelTableUpdate(sai::GetIrP4Info(GetParam()),
                                         p4::v1::Update::INSERT,
                                         /*tunnel_id=*/"tid-1",
                                         /*encap_dst_ip=*/"::1",
                                         /*encap_src_ip=*/"::2",
                                         /*router_interface_id=*/"rid-1"));

  EXPECT_THAT(pi_update, HasExactMatch("tid-1"));
  EXPECT_THAT(pi_update, HasActionParam("\001"));
  EXPECT_THAT(pi_update, HasActionParam("\002"));
  EXPECT_THAT(pi_update, HasActionParam("rid-1"));
}

TEST_P(L3RouteProgrammingTest, VrfTableAddId) {
  ASSERT_OK_AND_ASSIGN(p4::v1::Update pi_update,
                       VrfTableUpdate(sai::GetIrP4Info(GetParam()),
                                      p4::v1::Update::INSERT,
                                      /*vrf_id=*/"vrf-1"));
  EXPECT_THAT(pi_update, HasExactMatch("vrf-1"));
}

TEST_P(L3RouteProgrammingTest, VrfTableAddFailsWithEmptyId) {
  EXPECT_THAT(
      pins::VrfTableUpdate(sai::GetIrP4Info(GetParam()), p4::v1::Update::INSERT,
                     /*vrf_id=*/""),
      StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_P(L3RouteProgrammingTest, IpTableDoesNotRequireAnAction) {
  // The helper class will assume a default (e.g. drop).
  ASSERT_OK_AND_ASSIGN(
      p4::v1::Update pi_update,
      pins::Ipv4TableUpdate(sai::GetIrP4Info(GetParam()), p4::v1::Update::INSERT,
                      pins::IpTableOptions{.vrf_id = "vrf-0"}));

  EXPECT_THAT(pi_update, HasExactMatch("vrf-0"));
}

TEST_P(L3RouteProgrammingTest, IpTableWithSetNexthopAction) {
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

TEST_P(L3RouteProgrammingTest, IpTableWithSetWcmpGroupIdAction) {
  ASSERT_OK_AND_ASSIGN(
      p4::v1::Update pi_update,
      Ipv4TableUpdate(sai::GetIrP4Info(GetParam()), p4::v1::Update::INSERT,
                      IpTableOptions{
                          .vrf_id = "vrf-0",
                          .dst_addr_lpm = std::make_pair("10.1.1.1", 32),
                          .action = IpTableOptions::Action::kSetWcmpGroupId,
                          .wcmp_group_id = "group-0",
                      }));

  EXPECT_THAT(pi_update, HasExactMatch("vrf-0"));
  EXPECT_THAT(pi_update, HasLpmMatch("\n\001\001\001", 32));
  EXPECT_THAT(pi_update, HasActionParam("group-0"));
}

TEST_P(L3RouteProgrammingTest, IpTableEntryFailsWihInvalidParameters) {
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

TEST_P(L3RouteProgrammingTest, Ipv4TableEntryCannotHaveIPv6Address) {
  EXPECT_THAT(Ipv4TableUpdate(sai::GetIrP4Info(GetParam()),
                              p4::v1::Update::INSERT,
                              IpTableOptions{
                                  .dst_addr_lpm = std::make_pair("FE80::1", 32),
                              }),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       HasSubstr("Invalid IPv4 address")));
}

TEST_P(L3RouteProgrammingTest, Ipv6TableEntryCannotHaveIPv4Address) {
  EXPECT_THAT(
      Ipv6TableUpdate(sai::GetIrP4Info(GetParam()), p4::v1::Update::INSERT,
                      IpTableOptions{
                          .dst_addr_lpm = std::make_pair("10.1.1.1", 32),
                      }),
      StatusIs(absl::StatusCode::kInvalidArgument,
               HasSubstr("invalid IPv6 address")));
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

TEST_P(L3RouteProgrammingTest, L3AdmitTableAllPacketsDoesNotSetAMatchKey) {
  ASSERT_OK_AND_ASSIGN(p4::v1::Update pi_update,
                       L3AdmitAllTableUpdate(sai::GetIrP4Info(GetParam()),
                                             p4::v1::Update::INSERT));
  EXPECT_TRUE(pi_update.entity().table_entry().match().empty());
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

TEST_P(L3RouteProgrammingTest, WcmpGroupCanHaveMultipleNextHops) {
  ASSERT_OK_AND_ASSIGN(
      p4::v1::Update pi_update,
      WcmpGroupTableUpdate(sai::GetIrP4Info(GetParam()), p4::v1::Update::INSERT,
                           /*wcmp_group_id=*/"group-1",
                           {WcmpAction{.nexthop_id = "nh-2", .weight = 1},
                            WcmpAction{.nexthop_id = "nh-3", .weight = 2}}));

  EXPECT_THAT(pi_update, HasExactMatch("group-1"));
  EXPECT_EQ(pi_update.entity()
                .table_entry()
                .action()
                .action_profile_action_set()
                .action_profile_actions_size(),
            2);
}

TEST_P(L3RouteProgrammingTest, WcmpGroupActionCannotHaveWeightZero) {
  EXPECT_THAT(
      WcmpGroupTableUpdate(sai::GetIrP4Info(GetParam()), p4::v1::Update::INSERT,
                           /*wcmp_group_id=*/"group-1",
                           {WcmpAction{.nexthop_id = "nh-3", .weight = 0}}),
      StatusIs(absl::StatusCode::kInvalidArgument,
               HasSubstr("Expected positive action set weight")));
}

TEST_P(L3RouteProgrammingTest, WcmpGroupActionCanSetWatchPort) {
  ASSERT_OK_AND_ASSIGN(p4::v1::Update pi_update,
                       WcmpGroupTableUpdate(sai::GetIrP4Info(GetParam()),
                                            p4::v1::Update::INSERT,
                                            /*wcmp_group_id=*/"group-1",
                                            {WcmpAction{
                                                .nexthop_id = "nh-3",
                                                .weight = 2,
                                                .watch_port = "1",
                                            }}));
  ASSERT_EQ(pi_update.entity()
                .table_entry()
                .action()
                .action_profile_action_set()
                .action_profile_actions_size(),
            1);
  EXPECT_THAT(pi_update.entity()
                  .table_entry()
                  .action()
                  .action_profile_action_set()
                  .action_profile_actions(0)
                  .watch_port(),
              StrEq("1"));
}

std::string GetTestName(sai::Instantiation instantiation) {
  return gutil::SnakeCaseToCamelCase(sai::InstantiationToString(instantiation));
}

INSTANTIATE_TEST_SUITE_P(
    L3RouteProgrammingTestInstance, L3RouteProgrammingTest,
    testing::ValuesIn(sai::AllSaiInstantiations()),
    [](const testing::TestParamInfo<L3RouteProgrammingTest::ParamType>& param) {
      return GetTestName(param.param);
    });

struct IpTableUpdateTestCase {
  std::string name;
  IpTableOptions options;
  std::string output;  // Expected table entry in IR format.
};

using IpTableUpdateTest = testing::TestWithParam<
    std::tuple<IpTableUpdateTestCase, sai::Instantiation>>;

TEST_P(IpTableUpdateTest, IPv4OptionsSetProducesExpectedUpdate) {
  const pdpi::IrP4Info& ir_p4info = sai::GetIrP4Info(std::get<1>(GetParam()));
  const IpTableOptions& options = std::get<0>(GetParam()).options;
  SCOPED_TRACE(absl::StrCat("Options:\n", options));

  if (options.dst_addr_lpm.has_value() &&
      absl::StrContains(options.dst_addr_lpm->first, ':')) {
    EXPECT_FALSE(
        Ipv4TableUpdate(ir_p4info, p4::v1::Update::INSERT, options).ok());
    return;
  }

  pdpi::IrTableEntry ir_expected = gutil::ParseProtoOrDie<pdpi::IrTableEntry>(
      std::get<0>(GetParam()).output);
  ir_expected.set_table_name("ipv4_table");
  ASSERT_OK_AND_ASSIGN(p4::v1::TableEntry expected,
                       pdpi::IrTableEntryToPi(ir_p4info, ir_expected));

  ASSERT_OK_AND_ASSIGN(
      p4::v1::Update pi_update,
      Ipv4TableUpdate(ir_p4info, p4::v1::Update::INSERT, options));
  EXPECT_THAT(pi_update.entity().table_entry(), gutil::EqualsProto(expected));
}

TEST_P(IpTableUpdateTest, IPv6OptionsSetProducesExpectedUpdate) {
  const pdpi::IrP4Info& ir_p4info = sai::GetIrP4Info(std::get<1>(GetParam()));
  const IpTableOptions& options = std::get<0>(GetParam()).options;
  SCOPED_TRACE(absl::StrCat("Options:\n", options));

  if (options.dst_addr_lpm.has_value() &&
      absl::StrContains(options.dst_addr_lpm->first, '.')) {
    EXPECT_FALSE(
        Ipv6TableUpdate(ir_p4info, p4::v1::Update::INSERT, options).ok());
    return;
  }

  pdpi::IrTableEntry ir_expected = gutil::ParseProtoOrDie<pdpi::IrTableEntry>(
      std::get<0>(GetParam()).output);
  ir_expected.set_table_name("ipv6_table");
  ASSERT_OK_AND_ASSIGN(p4::v1::TableEntry expected,
                       pdpi::IrTableEntryToPi(ir_p4info, ir_expected));

  ASSERT_OK_AND_ASSIGN(
      p4::v1::Update pi_update,
      Ipv6TableUpdate(ir_p4info, p4::v1::Update::INSERT, options));
  EXPECT_THAT(pi_update.entity().table_entry(), gutil::EqualsProto(expected));
}

std::vector<IpTableUpdateTestCase> IpTableUpdateTestCases() {
  return {
      {
          .name = "IPv4Drop",
          .options =
              {
                  .vrf_id = "vrf-80",
                  .dst_addr_lpm = std::make_pair("10.11.0.0", 16),
                  .action = IpTableOptions::Action::kDrop,
              },
          .output = R"pb(matches {
                           name: "vrf_id"
                           exact { str: "vrf-80" }
                         }
                         matches {
                           name: "ipv4_dst"
                           lpm {
                             value { ipv4: "10.11.0.0" }
                             prefix_length: 16
                           }
                         }
                         action { name: "drop" })pb",
      },
      {
          .name = "IPv6Drop",
          .options =
              {
                  .vrf_id = "vrf-80",
                  .dst_addr_lpm = std::make_pair("2000::", 32),
                  .action = IpTableOptions::Action::kDrop,
              },
          .output = R"pb(matches {
                           name: "vrf_id"
                           exact { str: "vrf-80" }
                         }
                         matches {
                           name: "ipv6_dst"
                           lpm {
                             value { ipv6: "2000::" }
                             prefix_length: 32
                           }
                         }
                         action { name: "drop" })pb",
      },
      {
          .name = "VrfDrop",
          .options =
              {
                  .vrf_id = "vrf-80",
                  .action = IpTableOptions::Action::kDrop,
              },
          .output = R"pb(matches {
                           name: "vrf_id"
                           exact { str: "vrf-80" }
                         }
                         action { name: "drop" })pb",
      },
      {
          .name = "VrfSetMetadataAndDrop",
          .options =
              {
                  .vrf_id = "vrf-80",
                  .action = IpTableOptions::Action::kDrop,
                  .metadata = 15,
              },
          .output = R"pb(matches {
                           name: "vrf_id"
                           exact { str: "vrf-80" }
                         }
                         action {
                           name: "set_metadata_and_drop"
                           params {
                             name: "route_metadata"
                             value { hex_str: "0x0f" }
                           }
                         })pb",
      },
      {
          .name = "SetNexthop",
          .options =
              {
                  .vrf_id = "vrf-80",
                  .action = IpTableOptions::Action::kSetNextHopId,
                  .nexthop_id = "nexthop_1",
              },
          .output = R"pb(matches {
                           name: "vrf_id"
                           exact { str: "vrf-80" }
                         }
                         action {
                           name: "set_nexthop_id"
                           params {
                             name: "nexthop_id"
                             value { str: "nexthop_1" }
                           }
                         })pb",
      },
      {
          .name = "SetNexthopAndMetadata",
          .options =
              {
                  .vrf_id = "vrf-80",
                  .action = IpTableOptions::Action::kSetNextHopId,
                  .nexthop_id = "nexthop_1",
                  .metadata = 15,
              },
          .output = R"pb(matches {
                           name: "vrf_id"
                           exact { str: "vrf-80" }
                         }
                         action {
                           name: "set_nexthop_id_and_metadata"
                           params {
                             name: "nexthop_id"
                             value { str: "nexthop_1" }
                           }
                           params {
                             name: "route_metadata"
                             value { hex_str: "0x0f" }
                           }
                         })pb",
      },
      {
          .name = "SetWcmpGroupId",
          .options =
              {
                  .vrf_id = "vrf-80",
                  .action = IpTableOptions::Action::kSetWcmpGroupId,
                  .wcmp_group_id = "wcmp_group_1",
              },
          .output = R"pb(matches {
                           name: "vrf_id"
                           exact { str: "vrf-80" }
                         }
                         action {
                           name: "set_wcmp_group_id"
                           params {
                             name: "wcmp_group_id"
                             value { str: "wcmp_group_1" }
                           }
                         })pb",
      },
      {
          .name = "SetWcmpGroupIdAndMetadata",
          .options =
              {
                  .vrf_id = "vrf-80",
                  .action = IpTableOptions::Action::kSetWcmpGroupId,
                  .wcmp_group_id = "wcmp_group_1",
                  .metadata = 15,
              },
          .output = R"pb(matches {
                           name: "vrf_id"
                           exact { str: "vrf-80" }
                         }
                         action {
                           name: "set_wcmp_group_id_and_metadata"
                           params {
                             name: "wcmp_group_id"
                             value { str: "wcmp_group_1" }
                           }
                           params {
                             name: "route_metadata"
                             value { hex_str: "0x0f" }
                           }
                         })pb",
      },
  };
}

INSTANTIATE_TEST_SUITE_P(
    Options, IpTableUpdateTest,
    testing::Combine(testing::ValuesIn(IpTableUpdateTestCases()),
                     testing::ValuesIn(sai::AllSaiInstantiations())),
    [](const testing::TestParamInfo<IpTableUpdateTest::ParamType> info) {
      return absl::StrCat(std::get<0>(info.param).name, "For",
                          GetTestName(std::get<1>(info.param)));
    });

using IpTableOptionsTest = testing::TestWithParam<IpTableUpdateTestCase>;

bool HasSubstringsInOrder(absl::string_view str,
                          std::vector<std::string> substrs) {
  int position = 0;
  for (const auto& substr : substrs) {
    position = str.find(substr);
    if (position == str.npos) return false;
    position += substr.size();
  }
  return true;
}

TEST_P(IpTableOptionsTest, StringifyContainsComponents) {
  const IpTableOptions options = GetParam().options;
  const std::string& options_str = absl::StrCat(options);

  std::list<absl::string_view> params = absl::StrSplit(options_str, '\n');
  auto find_and_erase_param = [&params](std::vector<std::string> components) {
    for (auto param = params.begin(); param != params.end(); ++param) {
      if (HasSubstringsInOrder(*param, components)) {
        params.erase(param);
        return true;
      }
    }
    return false;
  };
  const absl::flat_hash_map<IpTableOptions::Action, std::string> action_names =
      {
          {IpTableOptions::Action::kDrop, "Drop"},
          {IpTableOptions::Action::kSetNextHopId, "SetNextHopId"},
          {IpTableOptions::Action::kSetWcmpGroupId, "SetWcmpGroupId"},
      };

  SCOPED_TRACE(absl::StrCat("Options:\n", options_str));
  EXPECT_TRUE(find_and_erase_param({"vrf_id", options.vrf_id}));
  EXPECT_TRUE(
      find_and_erase_param({"action", action_names.at(options.action)}));
  if (options.dst_addr_lpm.has_value()) {
    EXPECT_TRUE(
        find_and_erase_param({"dst_addr_lpm", options.dst_addr_lpm->first,
                              absl::StrCat(options.dst_addr_lpm->second)}));
  }
  if (options.nexthop_id.has_value()) {
    EXPECT_TRUE(find_and_erase_param({"nexthop_id", *options.nexthop_id}));
  }
  if (options.wcmp_group_id.has_value()) {
    EXPECT_TRUE(
        find_and_erase_param({"wcmp_group_id", *options.wcmp_group_id}));
  }
  if (options.metadata.has_value()) {
    EXPECT_TRUE(
        find_and_erase_param({"metadata", absl::StrCat(*options.metadata)}));
  }

  EXPECT_THAT(params, testing::IsEmpty()) << "Found unmatched parameters.";
}

INSTANTIATE_TEST_SUITE_P(
    Options, IpTableOptionsTest, testing::ValuesIn(IpTableUpdateTestCases()),
    [](const testing::TestParamInfo<IpTableOptionsTest::ParamType> info) {
      return info.param.name;
    });

}  // namespace
}  // namespace pins
