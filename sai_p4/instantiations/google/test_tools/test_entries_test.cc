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

#include <bitset>
#include <optional>
#include <vector>

#include "absl/types/span.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/netaddr/ipv4_address.h"
#include "p4_pdpi/netaddr/ipv6_address.h"
#include "p4_pdpi/netaddr/mac_address.h"
#include "p4_pdpi/pd.h"
#include "p4_pdpi/string_encodings/hex_string.h"
#include "p4_pdpi/ternary.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"

namespace sai {
namespace {

using ::gutil::EqualsProto;
using ::gutil::HasOneofCase;
using ::gutil::IsOkAndHolds;
using ::testing::AllOf;
using ::testing::ElementsAre;
using ::testing::IsEmpty;
using ::testing::IsSupersetOf;
using ::testing::Pointwise;
using ::testing::SizeIs;
using ::testing::UnorderedElementsAre;

// -- EntryBuilder tests --------------------------------------------------

TEST(EntryBuilder,
     GetDedupedIrEntitiesReturnsNothingForDefaultConstructedBuilder) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder().LogPdEntries().GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), IsEmpty());
}

TEST(EntryBuilder, GetDedupedEntitiesReturnsEntriesPassedToConstructor) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  auto entries = gutil::ParseProtoOrDie<sai::TableEntries>(
      R"pb(
        entries {
          l3_admit_table_entry {
            action { admit_to_l3 {} }
            priority: 1
          }
        }
      )pb");

  // Construct IrEntities.
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities ir_entities,
                       pdpi::PdTableEntriesToIrEntities(kIrP4Info, entries));
  EXPECT_THAT(
      EntryBuilder(entries).LogPdEntries().GetDedupedIrEntities(kIrP4Info),
      IsOkAndHolds(EqualsProto(ir_entities)));

  // Construct Pi Entities.
  ASSERT_OK_AND_ASSIGN(std::vector<p4::v1::Entity> pi_entities,
                       pdpi::PdTableEntriesToPiEntities(kIrP4Info, entries));
  EXPECT_THAT(
      EntryBuilder(entries).LogPdEntries().GetDedupedPiEntities(kIrP4Info),
      IsOkAndHolds(Pointwise(EqualsProto(), pi_entities)));
}

TEST(EntryBuilder, GetDedupedEntitiesRemovesDuplicates) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  auto entries = gutil::ParseProtoOrDie<sai::TableEntries>(
      R"pb(
        entries {
          l3_admit_table_entry {
            action { admit_to_l3 {} }
            priority: 1
          }
        }
        entries {
          l3_admit_table_entry {
            action { admit_to_l3 {} }
            priority: 1
          }
        }
      )pb");

  // Construct deduped IrEntities.
  auto deduped_entries = gutil::ParseProtoOrDie<sai::TableEntries>(
      R"pb(
        entries {
          l3_admit_table_entry {
            action { admit_to_l3 {} }
            priority: 1
          }
        }
      )pb");
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities deduped_entities,
      pdpi::PdTableEntriesToIrEntities(kIrP4Info, deduped_entries));
  EXPECT_THAT(
      EntryBuilder(entries).LogPdEntries().GetDedupedIrEntities(kIrP4Info),
      IsOkAndHolds(EqualsProto(deduped_entities)));

  // Construct Deduped Pi Entities.
  ASSERT_OK_AND_ASSIGN(
      std::vector<p4::v1::Entity> deduped_pi_entities,
      pdpi::PdTableEntriesToPiEntities(kIrP4Info, deduped_entries));
  EXPECT_THAT(
      EntryBuilder(entries).LogPdEntries().GetDedupedPiEntities(kIrP4Info),
      IsOkAndHolds(Pointwise(EqualsProto(), deduped_pi_entities)));
}

TEST(EntryBuilder, AddEntryPuntingAllPacketsDoesNotAddEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities entities,
                       EntryBuilder()
                           .AddEntryPuntingAllPackets(PuntAction::kCopy)
                           .AddEntryPuntingAllPackets(PuntAction::kTrap)
                           .LogPdEntries()
                           .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), SizeIs(2));
}

TEST(EntryBuilder, AddEntriesForwardingIpPacketsToGivenPortIpv4AndIpv6) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities ipv4_and_ipv6_entities,
                       EntryBuilder()
                           .AddEntriesForwardingIpPacketsToGivenPort(
                               "egress port", IpVersion::kIpv4And6)
                           .LogPdEntries()
                           .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(ipv4_and_ipv6_entities.entities(),
              AllOf(Contains(Partially(EqualsProto(
                        R"pb(table_entry {
                               table_name: "acl_pre_ingress_table"
                               matches {
                                 name: "is_ip"
                                 optional { value { hex_str: "0x1" } }
                               }
                             }
                        )pb"))),
                    Not(Contains(Partially(EqualsProto(
                        R"pb(table_entry {
                               table_name: "acl_pre_ingress_table"
                               matches {
                                 name: "is_ipv4"
                                 optional { value { hex_str: "0x1" } }
                               }
                             }
                        )pb")))),
                    Not(Contains(Partially(EqualsProto(
                        R"pb(table_entry {
                               table_name: "acl_pre_ingress_table"
                               matches {
                                 name: "is_ipv6"
                                 optional { value { hex_str: "0x1" } }
                               }
                             }
                        )pb"))))));
};

TEST(EntryBuilder, AddEntriesForwardingIpPacketsToGivenPortIpv4) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities ipv4_entities,
                       EntryBuilder()
                           .AddEntriesForwardingIpPacketsToGivenPort(
                               "egress port", IpVersion::kIpv4)
                           .LogPdEntries()
                           .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(ipv4_entities.entities(),
              AllOf(Contains(Partially(EqualsProto(
                        R"pb(table_entry {
                               table_name: "acl_pre_ingress_table"
                               matches {
                                 name: "is_ipv4"
                                 optional { value { hex_str: "0x1" } }
                               }
                             }
                        )pb"))),
                    Not(Contains(Partially(EqualsProto(
                        R"pb(table_entry {
                               table_name: "acl_pre_ingress_table"
                               matches {
                                 name: "is_ip"
                                 optional { value { hex_str: "0x1" } }
                               }
                             }
                        )pb")))),
                    Not(Contains(Partially(EqualsProto(
                        R"pb(table_entry {
                               table_name: "acl_pre_ingress_table"
                               matches {
                                 name: "is_ipv6"
                                 optional { value { hex_str: "0x1" } }
                               }
                             }
                        )pb"))))));
}

TEST(EntryBuilder, AddEntriesForwardingIpPacketsToGivenPortIpv6) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities ipv6_entities,
                       EntryBuilder()
                           .AddEntriesForwardingIpPacketsToGivenPort(
                               "egress port", IpVersion::kIpv6)
                           .LogPdEntries()
                           .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(ipv6_entities.entities(),
              AllOf(Contains(Partially(EqualsProto(
                        R"pb(table_entry {
                               table_name: "acl_pre_ingress_table"
                               matches {
                                 name: "is_ipv6"
                                 optional { value { hex_str: "0x1" } }
                               }
                             }
                        )pb"))),
                    Not(Contains(Partially(EqualsProto(
                        R"pb(table_entry {
                               table_name: "acl_pre_ingress_table"
                               matches {
                                 name: "is_ip"
                                 optional { value { hex_str: "0x1" } }
                               }
                             }
                        )pb")))),
                    Not(Contains(Partially(EqualsProto(
                        R"pb(table_entry {
                               table_name: "acl_pre_ingress_table"
                               matches {
                                 name: "is_ipv4"
                                 optional { value { hex_str: "0x1" } }
                               }
                             }
                        )pb"))))));
}

TEST(EntryBuilder,
     AddEntriesForwardingIpPacketsToGivenPortWithIpForwardingParams) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  Ipv4Lpm ipv4_lpm = {
      .dst_ip = netaddr::Ipv4Address(1, 2, 3, 4),
  };
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities entities,
                       EntryBuilder()
                           .AddEntriesForwardingIpPacketsToGivenPort(
                               "egress port", {.ipv4_lpm = ipv4_lpm})
                           .LogPdEntries()
                           .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), SizeIs(8));
}

TEST(EntryBuilder, AddEntriesForwardingIpPacketsToGivenPortAddsEntries) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddEntriesForwardingIpPacketsToGivenPort("egress port")
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), SizeIs(8));
}

TEST(EntryBuilder,
     AddEntriesForwardingIpPacketsToGivenPortRespectsRewriteOptions) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddEntriesForwardingIpPacketsToGivenPort(
              "egress port", IpVersion::kIpv4And6,
              NexthopRewriteOptions{
                  .disable_decrement_ttl = true,
                  .src_mac_rewrite = netaddr::MacAddress(1, 2, 3, 4, 5, 6),
                  .dst_mac_rewrite = std::nullopt,
              })
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(),
              Contains(Partially(EqualsProto(
                  R"pb(table_entry {
                         action {
                           name: "set_ip_nexthop_and_disable_rewrites"
                           params {
                             name: "disable_decrement_ttl"
                             value { hex_str: "0x1" }
                           }
                           params {
                             name: "disable_src_mac_rewrite"
                             value { hex_str: "0x0" }
                           }
                           params {
                             name: "disable_dst_mac_rewrite"
                             value { hex_str: "0x1" }
                           }
                         }
                       })pb"))));
}

TEST(EntryBuilder, AddVrfEntryAddsEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities entities,
                       EntryBuilder()
                           .AddVrfEntry("vrf-1")
                           .AddVrfEntry("vrf-2")
                           .AddVrfEntry("vrf-3")
                           .LogPdEntries()
                           .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), SizeIs(3));
}

TEST(EntryBuilder, AddIpv6TunnelTerminationEntryAddsEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  sai::Ipv6TunnelTerminationParams params{
      .src_ipv6 =
          P4RuntimeTernary<netaddr::Ipv6Address>{
              .value = netaddr::Ipv6Address(0x77, 0x4455, 0, 0, 0, 0, 0, 0),
              .mask = netaddr::Ipv6Address(0xFFFF, 0xFFFF, 0, 0, 0, 0, 0, 0),
          },
      .dst_ipv6 = P4RuntimeTernary<netaddr::Ipv6Address>{
          .value = netaddr::Ipv6Address(0x11, 0x2233, 0, 0, 0, 0, 0, 0),
          .mask = netaddr::Ipv6Address(0xFFFF, 0xFFFF, 0, 0, 0, 0, 0, 0),
      }};
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities entities,
                       EntryBuilder()
                           .AddIpv6TunnelTerminationEntry(params)
                           .LogPdEntries()
                           .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), SizeIs(1));
}

TEST(EntryBuilder, AddEntryAdmittingAllPacketsToL3AddsEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities entities,
                       EntryBuilder()
                           .AddEntryAdmittingAllPacketsToL3()
                           .LogPdEntries()
                           .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), SizeIs(1));
}

TEST(EntryBuilder, AddDefaultRouteForwardingAllPacketsToGivenPortAddsEntries) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities entities,
                       EntryBuilder()
                           .AddDefaultRouteForwardingAllPacketsToGivenPort(
                               "egress port 1", IpVersion::kIpv4, "vrf-1")
                           .AddDefaultRouteForwardingAllPacketsToGivenPort(
                               "egress port 2", IpVersion::kIpv6, "vrf-2")
                           .AddDefaultRouteForwardingAllPacketsToGivenPort(
                               "egress port 3", IpVersion::kIpv4And6, "vrf-3")
                           .LogPdEntries()
                           .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), SizeIs(13));
}

TEST(EntryBuilder, AddIpv4EntryWithNextHopAction) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddIpv4TableEntry(IpTableEntryParams{
              .vrf = "vrf", .action = SetNextHopId{.nexthop_id = "nexthop"}})
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), SizeIs(1));
  EXPECT_THAT(entities.entities(), Contains(Partially(EqualsProto(R"pb(
                table_entry {
                  table_name: "ipv4_table"
                  action {
                    name: "set_nexthop_id"
                    params {
                      name: "nexthop_id"
                      value { str: "nexthop" }
                    }
                  }
                }
              )pb"))));
  EXPECT_THAT(entities.entities(), Not(Contains(Partially(EqualsProto(R"pb(
                table_entry {
                  table_name: "ipv4_table"
                  matches { name: "ipv4_dst" }
                }
              )pb")))));
}

TEST(EntryBuilder, AddIpv4EntryWithWcmpGroupIdAction) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddIpv4TableEntry(IpTableEntryParams{
              .vrf = "vrf",
              .action = SetWcmpGroupId{.wcmp_group_id = "wcmp_group_id"}})
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), SizeIs(1));
  EXPECT_THAT(entities.entities(), Contains(Partially(EqualsProto(R"pb(
                table_entry {
                  table_name: "ipv4_table"
                  action {
                    name: "set_wcmp_group_id"
                    params {
                      name: "wcmp_group_id"
                      value { str: "wcmp_group_id" }
                    }
                  }
                }
              )pb"))));
  EXPECT_THAT(entities.entities(), Not(Contains(Partially(EqualsProto(R"pb(
                table_entry {
                  table_name: "ipv4_table"
                  action { name: "set_nexthop_id" }
                }
              )pb")))));
}

TEST(EntryBuilder, AddIpv4EntryAddsLpmEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
	  .AddIpv4TableEntry(
              IpTableEntryParams{
                  .vrf = "vrf",
                  .action = SetNextHopId{.nexthop_id = "nexthop"}},
              Ipv4Lpm{.dst_ip = netaddr::Ipv4Address(10, 0, 0, 0),
                      .prefix_len = 24})
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), SizeIs(1));
  EXPECT_THAT(entities.entities(), Contains(Partially(EqualsProto(R"pb(
                table_entry {
                  table_name: "ipv4_table"
                  matches {
                    name: "ipv4_dst"
                    lpm {
                      value { ipv4: "10.0.0.0" }
                      prefix_length: 24
                    }
                  }
                }
              )pb"))));
}

TEST(EntryBuilder, AddIpv6EntryWithNextHopAction) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddIpv6TableEntry(IpTableEntryParams{
              .vrf = "vrf", .action = SetNextHopId{.nexthop_id = "nexthop"}})
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), SizeIs(1));
  EXPECT_THAT(entities.entities(), Contains(Partially(EqualsProto(R"pb(
                table_entry {
                  table_name: "ipv6_table"
                  action {
                    name: "set_nexthop_id"
                    params {
                      name: "nexthop_id"
                      value { str: "nexthop" }
                    }
                  }
                }
              )pb"))));
  EXPECT_THAT(entities.entities(), Not(Contains(Partially(EqualsProto(R"pb(
                table_entry {
                  table_name: "ipv6_table"
                  matches { name: "ipv6_dst" }
                }
              )pb")))));
}

TEST(EntryBuilder, AddIpv6EntryWithWcmpGroupIdAction) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddIpv6TableEntry(IpTableEntryParams{
              .vrf = "vrf",
              .action = SetWcmpGroupId{.wcmp_group_id = "wcmp_group_id"}})
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), SizeIs(1));
  EXPECT_THAT(entities.entities(), Contains(Partially(EqualsProto(R"pb(
                table_entry {
                  table_name: "ipv6_table"
                  action {
                    name: "set_wcmp_group_id"
                    params {
                      name: "wcmp_group_id"
                      value { str: "wcmp_group_id" }
                    }
                  }
                }
              )pb"))));
  EXPECT_THAT(entities.entities(), Not(Contains(Partially(EqualsProto(R"pb(
                table_entry {
                  table_name: "ipv6_table"
                  action { name: "set_nexthop_id" }
                }
              )pb")))));
}

TEST(EntryBuilder, AddIpv6EntryAddsLpmEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
	  .AddIpv6TableEntry(
              IpTableEntryParams{
                  .vrf = "vrf",
                  .action = SetNextHopId{.nexthop_id = "nexthop"}},
              Ipv6Lpm{
                  .dst_ip = netaddr::Ipv6Address(0x2001, 0x102),
                  .prefix_len = 64,
              })
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), SizeIs(1));
  EXPECT_THAT(entities.entities(), Contains(Partially(EqualsProto(R"pb(
                table_entry {
                  table_name: "ipv6_table"
                  matches {
                    name: "ipv6_dst"
                    lpm {
                      value { ipv6: "2001:102::" }
                      prefix_length: 64
                    }
                  }
                }
              )pb"))));
}

TEST(EntryBuilder, AddPreIngressAclTableEntryForGivenIpTypeAddsEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddPreIngressAclTableEntry("vrf-1",
                                      AclPreIngressMatchFields{.is_ip = true})
          .AddPreIngressAclTableEntry("vrf-2",
                                      AclPreIngressMatchFields{.is_ipv4 = true})
          .AddPreIngressAclTableEntry("vrf-3",
                                      AclPreIngressMatchFields{.is_ipv6 = true})
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(),
              UnorderedElementsAre(
                  Partially(EqualsProto(
                      R"pb(table_entry {
                             table_name: "acl_pre_ingress_table"
                             matches {
                               name: "is_ip"
                               optional { value { hex_str: "0x1" } }
                             }
                             action { params { value { str: "vrf-1" } } }
                           })pb")),
                  Partially(EqualsProto(
                      R"pb(table_entry {
                             table_name: "acl_pre_ingress_table"
                             matches {
                               name: "is_ipv4"
                               optional { value { hex_str: "0x1" } }
                             }
                             action { params { value { str: "vrf-2" } } }
                           })pb")),
                  Partially(EqualsProto(
                      R"pb(table_entry {
                             table_name: "acl_pre_ingress_table"
                             matches {
                               name: "is_ipv6"
                               optional { value { hex_str: "0x1" } }
                             }
                             action { params { value { str: "vrf-3" } } }
                           })pb"))));
}

TEST(EntryBuilder, AddPreIngressAclTableEntryForAllIpMatchFields) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddPreIngressAclTableEntry(
              "vrf-1",
              AclPreIngressMatchFields{
                  .is_ip = true, .is_ipv4 = true, .is_ipv6 = true})
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(),
              ElementsAre(Partially(EqualsProto(
                  R"pb(table_entry {
                         table_name: "acl_pre_ingress_table"
                         matches {
                           name: "is_ip"
                           optional { value { hex_str: "0x1" } }
                         }
                         matches {
                           name: "is_ipv4"
                           optional { value { hex_str: "0x1" } }
                         }
                         matches {
                           name: "is_ipv6"
                           optional { value { hex_str: "0x1" } }
                         }
                       })pb"))));
}

TEST(EntryBuilder,
     AddPreIngressAclTableEntryWithVlanMaskOfZeroCreatesWildcard) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddPreIngressAclTableEntry(
              "vrf-1",
              AclPreIngressMatchFields{
                  .vlan_id = pdpi::Ternary<std::bitset<kVlanIdBitwidth>>(
                      0x00a, 0x000)})
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), ElementsAre(Partially(EqualsProto(R"pb(
                table_entry {
                  table_name: "acl_pre_ingress_table"
                  action {
                    name: "set_vrf"
                    params {
                      name: "vrf_id"
                      value { str: "vrf-1" }
                    }
                  }
                }
              )pb"))));
}

TEST(EntryBuilder,
     AddPreIngressAclTableEntryCreatesTableWithWildcardAndDefaultPriority) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities entities,
                       EntryBuilder()
		           .AddPreIngressAclTableEntry("vrf-1")
                           .LogPdEntries()
                           .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), ElementsAre(Partially(EqualsProto(R"pb(
                table_entry {
                  table_name: "acl_pre_ingress_table"
                  priority: 1
                  action {
                    name: "set_vrf"
                    params {
                      name: "vrf_id"
                      value { str: "vrf-1" }
                    }
                  }
                }
              )pb"))));
}

TEST(EntryBuilder, AddEntryTunnelTerminatingAllIpInIpv6PacketsAddsEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities entities,
                       EntryBuilder()
                           .AddEntryTunnelTerminatingAllIpInIpv6Packets()
                           .LogPdEntries()
                           .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), SizeIs(1));
}
TEST(EntryBuilder, AddEntryPuntingPacketsWithTtlZeroAndOneHasOneEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities entities,
                       EntryBuilder()
                           .AddEntryPuntingPacketsWithTtlZeroAndOne()
                           .LogPdEntries()
                           .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), SizeIs(1));
}
TEST(EntryBuilder, AddEntryPuntingPacketsWithDstMacHasOneEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities entities,
                       EntryBuilder()
                           .AddEntryPuntingPacketsWithDstMac(
                               netaddr::MacAddress(1, 2, 3, 4, 5, 6).ToString())
                           .LogPdEntries()
                           .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), ElementsAre(Partially(EqualsProto(R"pb(
                table_entry {
                  table_name: "acl_ingress_table"
                  matches {
                    name: "dst_mac"
                    ternary {
                      value { mac: "01:02:03:04:05:06" }
                      mask { mac: "ff:ff:ff:ff:ff:ff" }
                    }
                  }
                }
              )pb"))));
}

TEST(EntryBuilder, AddEntryPuntingPacketsWithDstMacWithPuntAction) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities entities,
                       EntryBuilder()
                           .AddEntryPuntingPacketsWithDstMac(
                               netaddr::MacAddress(1, 2, 3, 4, 5, 6).ToString(),
                               PuntAction::kCopy, "0x8")
                           .LogPdEntries()
                           .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), ElementsAre(Partially(EqualsProto(R"pb(
                table_entry {
                  table_name: "acl_ingress_table"
                  matches {
                    name: "dst_mac"
                    ternary {
                      value { mac: "01:02:03:04:05:06" }
                      mask { mac: "ff:ff:ff:ff:ff:ff" }
                    }
                  }
                  priority: 1
                  action {
                    name: "acl_copy"
                    params {
                      name: "qos_queue"
                      value { str: "0x8" }
                    }
                  }
                }
              )pb"))));
}

TEST(EntryBuilder, AddMulticastGroupEntryReplicaOverloadAddsEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities replica_overload_entities,
      EntryBuilder()
          .AddMulticastGroupEntry(
              123,
              {
                  Replica{.egress_port = "\1",
                          .instance = 11,
                          .backup_replicas = {BackupReplica{.egress_port = "\3",
                                                            .instance = 33},
                                              BackupReplica{.egress_port = "\4",
                                                            .instance = 44}}},
                  Replica{.egress_port = "\2", .instance = 22},
              })
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(replica_overload_entities.entities(),
              ElementsAre(HasOneofCase<pdpi::IrEntity>(
                  "entity", pdpi::IrEntity::kPacketReplicationEngineEntry)));

  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities port_overload_entities,
                       EntryBuilder()
                           .AddMulticastGroupEntry(123, {"1", "2"})
                           .LogPdEntries()
                           .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(port_overload_entities.entities(),
              ElementsAre(HasOneofCase<pdpi::IrEntity>(
                  "entity", pdpi::IrEntity::kPacketReplicationEngineEntry)));
}

TEST(EntryBuilder, AddMulticastGroupEntryPortOverloadAddsUniqueReplicas) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities entities,
                       EntryBuilder()
                           .AddMulticastGroupEntry(123, {"1", "1", "1"})
                           .LogPdEntries()
                           .GetDedupedIrEntities(kIrP4Info));
  ASSERT_THAT(entities.entities(), SizeIs(1));
  const auto& replicas = entities.entities(0)
                             .packet_replication_engine_entry()
                             .multicast_group_entry()
                             .replicas();
  ASSERT_THAT(replicas, SizeIs(3));
  EXPECT_NE(replicas[0].instance(), replicas[1].instance());
  EXPECT_NE(replicas[0].instance(), replicas[2].instance());
  EXPECT_NE(replicas[1].instance(), replicas[2].instance());
}

TEST(EntryBuilder, AddRouterInterfaceTableEntryAddsEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddRouterInterfaceTableEntry(RouterInterfaceTableParams{
              .egress_port = "\1",
              .src_mac = netaddr::MacAddress(1, 2, 3, 4, 5, 6),
              .vlan_id = std::nullopt,
          })
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), ElementsAre(Partially(EqualsProto(R"pb(
                table_entry {
                  table_name: "router_interface_table"
                  action { name: "unicast_set_port_and_src_mac" }
                }
              )pb"))));
}

TEST(EntryBuilder, AddMrifEntryRewritingSrcMacAddsEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddMrifEntryRewritingSrcMac(
              /*egress_port=*/"\1", /*replica_instance=*/15,
              /*src_mac=*/netaddr::MacAddress(1, 2, 3, 4, 5, 6))
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), ElementsAre(Partially(EqualsProto(R"pb(
                table_entry {
                  table_name: "multicast_router_interface_table"
                  action { name: "multicast_set_src_mac" }
                }
              )pb"))));
}

TEST(EntryBuilder, AddMrifEntryRewritingSrcMacAndVlanIdAddsEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddMrifEntryRewritingSrcMacAndVlanId(
              /*egress_port=*/"\1", /*replica_instance=*/15,
              /*src_mac=*/netaddr::MacAddress(1, 2, 3, 4, 5, 6),
              /*vlan_id=*/123)
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), ElementsAre(Partially(EqualsProto(R"pb(
                table_entry {
                  table_name: "multicast_router_interface_table"
                  action { name: "multicast_set_src_mac_and_vlan_id" }
                }
              )pb"))));
}

TEST(EntryBuilder, AddMrifEntryRewritingSrcMacDstMacAndVlanIdAddsEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddMrifEntryRewritingSrcMacDstMacAndVlanId(
              /*egress_port=*/"\1", /*replica_instance=*/15,
              /*src_mac=*/netaddr::MacAddress(1, 2, 3, 4, 5, 6),
              /*dst_mac=*/netaddr::MacAddress(7, 8, 9, 10, 11, 12),
              /*vlan_id=*/123)
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(
      entities.entities(), ElementsAre(Partially(EqualsProto(R"pb(
        table_entry {
          table_name: "multicast_router_interface_table"
          action { name: "multicast_set_src_mac_and_dst_mac_and_vlan_id" }
        }
      )pb"))));
}

TEST(EntryBuilder,
     AddMrifEntryRewritingSrcMacAndPreservingIngressVlanIdAddsEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddMrifEntryRewritingSrcMacAndPreservingIngressVlanId(
              /*egress_port=*/"\1", /*replica_instance=*/15,
              /*src_mac=*/netaddr::MacAddress(1, 2, 3, 4, 5, 6))
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(
      entities.entities(), ElementsAre(Partially(EqualsProto(R"pb(
        table_entry {
          table_name: "multicast_router_interface_table"
          action { name: "multicast_set_src_mac_and_preserve_ingress_vlan_id" }
        }
      )pb"))));
}

TEST(EntryBuilder, AddL2MrifEntryAddsEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities entities,
                       EntryBuilder()
                           .AddL2MrifEntry(
                               /*egress_port=*/"1", /*replica_instance=*/15)
                           .LogPdEntries()
                           .GetDedupedIrEntities(kIrP4Info));

  EXPECT_THAT(entities.entities(), ElementsAre(Partially(EqualsProto(R"pb(
                table_entry {
                  table_name: "multicast_router_interface_table"
                  matches {
                    name: "multicast_replica_port"
                    exact { str: "1" }
                  }
                  matches {
                    name: "multicast_replica_instance"
                    exact { hex_str: "0x000f" }
                  }
                  action { name: "l2_multicast_passthrough" }
                }
              )pb"))));
}

TEST(EntryBuilder, AddMulticastRouteAddsIpv4Entry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(auto dst_ip,
                       netaddr::Ipv4Address::OfString("225.10.20.32"));
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities entities,
                       EntryBuilder()
                           .AddMulticastRoute("vrf-1", dst_ip, 0x42)
                           .LogPdEntries()
                           .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), Contains(Partially(EqualsProto(R"pb(
                table_entry {
                  table_name: "ipv4_multicast_table"
                  matches {
                    name: "vrf_id"
                    exact { str: "vrf-1" }
                  }
                  matches {
                    name: "ipv4_dst"
                    exact { ipv4: "225.10.20.32" }
                  }
                  action {
                    name: "set_multicast_group_id"
                    params {
                      name: "multicast_group_id"
                      value { hex_str: "0x0042" }
                    }
                  }
                }
              )pb"))));
}

TEST(EntryBuilder, AddMulticastRouteAddsIpv6Entry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(auto dst_ip,
                       netaddr::Ipv6Address::OfString(
                           "ff00:8888:1111:2222:3333:4444:5555:6666"));
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities entities,
                       EntryBuilder()
                           .AddMulticastRoute("vrf-2", dst_ip, 0x123)
                           .LogPdEntries()
                           .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), Contains(Partially(EqualsProto(R"pb(
                table_entry {
                  table_name: "ipv6_multicast_table"
                  matches {
                    name: "vrf_id"
                    exact { str: "vrf-2" }
                  }
                  matches {
                    name: "ipv6_dst"
                    exact { ipv6: "ff00:8888:1111:2222:3333:4444:5555:6666" }
                  }
                  action {
                    name: "set_multicast_group_id"
                    params {
                      name: "multicast_group_id"
                      value { hex_str: "0x0123" }
                    }
                  }
                }
              )pb"))));
}

TEST(EntryBuilder, AddIngressAclDroppingAllPacketsAddsEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities entities,
                       EntryBuilder()
                           .AddIngressAclDroppingAllPackets()
                           .AddIngressAclDroppingAllPackets()
                           .AddIngressAclDroppingAllPackets()
                           .LogPdEntries()
                           .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), ElementsAre(Partially(EqualsProto(R"pb(
                table_entry { table_name: "acl_ingress_table" }
              )pb"))));
}

TEST(EntryBuilder, AddEgressAclDroppingIpPacketsAddsEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities entities,
                       EntryBuilder()
                           .AddEgressAclDroppingIpPackets()
                           .LogPdEntries()
                           .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(),
              ElementsAre(Partially(EqualsProto(R"pb(
                            table_entry {
                              table_name: "acl_egress_table"
                              matches { name: "is_ipv4" }
                              action { name: "acl_drop" }
                            }
                          )pb")),
                          Partially(EqualsProto(R"pb(
                            table_entry {
                              table_name: "acl_egress_table"
                              matches { name: "is_ipv6" }
                              action { name: "acl_drop" }
                            }
                          )pb"))));
}

TEST(EntryBuilder, AddMirrorSessionTableEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kTor);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddMirrorSessionTableEntry(MirrorSessionParams{
              .mirror_session_id = "mirror_session_id",
              .monitor_port = "monitor_port",
              .mirror_encap_src_mac =
                  netaddr::MacAddress(1, 1, 1, 1, 1, 1).ToString(),
              .mirror_encap_dst_mac =
                  netaddr::MacAddress(1, 2, 3, 4, 5, 6).ToString(),
              .mirror_encap_vlan_id = "0x123",
              .mirror_encap_src_ip = "::1",
              .mirror_encap_dst_ip = "::2",
              .mirror_encap_udp_src_port = "0x1234",
              .mirror_encap_udp_dst_port = "0x1235",
          })
          .LogPdEntries()
          // TODO: Remove unsupported once the
          // switch supports mirroring-related tables.
          .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), ElementsAre(Partially(EqualsProto(R"pb(
                table_entry { table_name: "mirror_session_table" }
              )pb"))));
}

TEST(EntryBuilder, AddMarkToMirrorAclEntryTest) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kTor);
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities entities,
                       EntryBuilder()
                           .AddMarkToMirrorAclEntry(MarkToMirrorParams{
                               .ingress_port = "1",
                               .mirror_session_id = "id",
                           })
                           .LogPdEntries()
                           // TODO: Remove unsupported once the
                           // switch supports mirroring-related tables.
                           .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(
      entities.entities(), ElementsAre(Partially(EqualsProto(R"pb(
        table_entry { table_name: "acl_ingress_mirror_and_redirect_table" }
      )pb"))));
}

TEST(EntryBuilder, AddIngressAclEntryRedirectingToNexthopAddsEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kTor);
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities entities,
                       EntryBuilder()
                           .AddIngressAclEntryRedirectingToNexthop("nexthop")
                           .LogPdEntries()
                           .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(
      entities.entities(), ElementsAre(Partially(EqualsProto(R"pb(
        table_entry { table_name: "acl_ingress_mirror_and_redirect_table" }
      )pb"))));
}

TEST(EntryBuilder,
     AddIngressAclEntryRedirectingToNexthopWithMatchFieldOptionsAddsEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kTor);
  MirrorAndRedirectMatchFields match_fields = {
      .in_port = "1",
      .route_hit = true,
      .vlan_id = 1,
      .is_ipv4 = true,
      .dst_ip =
          sai::P4RuntimeTernary<netaddr::Ipv4Address>{
              .value = netaddr::Ipv4Address(0x10, 0, 0, 0x1),
              .mask = netaddr::Ipv4Address(0xff, 0xff, 0xff, 0xff),
          },
      .is_ipv6 = true,
      .dst_ipv6 =
          sai::P4RuntimeTernary<netaddr::Ipv6Address>{
              .value = netaddr::Ipv6Address(0x10, 0, 0, 0, 0, 0, 0, 0x1),
              .mask = netaddr::Ipv6Address(0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                                           0xff, 0xff),
          },
      .vrf = "vrf-1",
  };
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddIngressAclEntryRedirectingToNexthop("nexthop", match_fields)
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), Contains(Partially(EqualsProto(R"pb(
                table_entry {
                  table_name: "acl_ingress_mirror_and_redirect_table"
                  matches { name: "vlan_id" }
                  matches { name: "in_port" }
                  matches { name: "route_hit" }
                  matches { name: "is_ipv4" }
                  matches { name: "dst_ip" }
                  matches { name: "is_ipv6" }
                  matches { name: "dst_ipv6" }
                  matches { name: "vrf_id" }
                })pb"))));
}

TEST(EntryBuilder,
     AddIngressAclEntryRedirectingToNexthopWithIpmcTableHitWorks) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kTor);
  *kIrP4Info.mutable_pkg_info()->mutable_version() = "3.2.6";
  MirrorAndRedirectMatchFields match_fields = {
      .in_port = "1",
      .route_hit = true,
      .vlan_id = 1,
      .is_ipv4 = true,
      .dst_ip =
          sai::P4RuntimeTernary<netaddr::Ipv4Address>{
              .value = netaddr::Ipv4Address(0x10, 0, 0, 0x1),
              .mask = netaddr::Ipv4Address(0xff, 0xff, 0xff, 0xff),
          },
      .is_ipv6 = true,
      .dst_ipv6 =
          sai::P4RuntimeTernary<netaddr::Ipv6Address>{
              .value = netaddr::Ipv6Address(0x10, 0, 0, 0, 0, 0, 0, 0x1),
              .mask = netaddr::Ipv6Address(0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                                           0xff, 0xff),
          },
      .vrf = "vrf-1",
  };
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddIngressAclEntryRedirectingToNexthop("nexthop", match_fields)
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), Contains(Partially(EqualsProto(R"pb(
                table_entry {
                  table_name: "acl_ingress_mirror_and_redirect_table"
                  matches { name: "vlan_id" }
                  matches { name: "in_port" }
                  matches { name: "ipmc_table_hit" }
                  matches { name: "is_ipv4" }
                  matches { name: "dst_ip" }
                  matches { name: "is_ipv6" }
                  matches { name: "dst_ipv6" }
                  matches { name: "vrf_id" }
                })pb"))));
}

TEST(EntryBuilder, AddIngressAclEntryRedirectingToMulticastGroupAddsEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kTor);
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities entities,
                       EntryBuilder()
                           .AddIngressAclEntryRedirectingToMulticastGroup(123)
                           .LogPdEntries()
                           .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(
      entities.entities(), ElementsAre(Partially(EqualsProto(R"pb(
        table_entry { table_name: "acl_ingress_mirror_and_redirect_table" }
      )pb"))));
}

TEST(EntryBuilder,
     AddIngressAclEntryRedirectingToMulticastGroupWithMatchFieldOptionsAdds) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kTor);
  MirrorAndRedirectMatchFields match_fields = {
      .in_port = "1",
      .route_hit = true,
      .vlan_id = 1,
      .is_ipv4 = true,
      .dst_ip =
          sai::P4RuntimeTernary<netaddr::Ipv4Address>{
              .value = netaddr::Ipv4Address(0x10, 0, 0, 0x1),
              .mask = netaddr::Ipv4Address(0xff, 0xff, 0xff, 0xff),
          },
      .is_ipv6 = true,
      .dst_ipv6 =
          sai::P4RuntimeTernary<netaddr::Ipv6Address>{
              .value = netaddr::Ipv6Address(0x10, 0, 0, 0, 0, 0, 0, 0x1),
              .mask = netaddr::Ipv6Address(0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                                           0xff, 0xff),
          },
      .vrf = "vrf-1",
  };
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddIngressAclEntryRedirectingToMulticastGroup(123, match_fields)
          .LogPdEntries()
	  .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), Contains(Partially(EqualsProto(R"pb(
                table_entry {
                  table_name: "acl_ingress_mirror_and_redirect_table"
                  matches { name: "vlan_id" }
                  matches { name: "in_port" }
                  matches { name: "route_hit" }
                  matches { name: "is_ipv4" }
                  matches { name: "dst_ip" }
                  matches { name: "is_ipv6" }
                  matches { name: "dst_ipv6" }
                  matches { name: "vrf_id" }
                })pb"))));
}

TEST(EntryBuilder, AddDisableIngressVlanChecksEntryAddsCorrectEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kTor);
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities entities,
                       EntryBuilder()
                           .AddDisableIngressVlanChecksEntry()
                           .LogPdEntries()
                           .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), ElementsAre(Partially(EqualsProto(R"pb(
                table_entry { table_name: "disable_ingress_vlan_checks_table" }
              )pb"))));
}

TEST(EntryBuilder, AddDisableEgressVlanChecksEntryAddsCorrectEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kTor);
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities entities,
                       EntryBuilder()
                           .AddDisableEgressVlanChecksEntry()
                           .LogPdEntries()
                           .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), ElementsAre(Partially(EqualsProto(R"pb(
                table_entry { table_name: "disable_egress_vlan_checks_table" }
              )pb"))));
}

TEST(EntryBuilder, AddVlanEntryAddsCorrectEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kTor);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder().AddVlanEntry("0x00a").LogPdEntries().GetDedupedIrEntities(
          kIrP4Info));
  EXPECT_THAT(entities.entities(), ElementsAre((EqualsProto(R"pb(
                table_entry {
                  table_name: "vlan_table"
                  matches {
                    name: "vlan_id"
                    exact { hex_str: "0x00a" }
                  }
                  action { name: "no_action" }
                }
              )pb"))));
}

TEST(EntryBuilder, AddVlanMembershipEntryAddsCorrectEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kTor);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddVlanMembershipEntry(/*vlan_id_hexstr=*/"0x00a", /*port=*/"1",
                                  VlanTaggingMode::kTagged)
          .AddVlanMembershipEntry(/*vlan_id_hexstr=*/"0x00b", /*port=*/"2",
                                  VlanTaggingMode::kUntagged)
          .LogPdEntries()
	  .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(),
              UnorderedElementsAre(EqualsProto(R"pb(
                                     table_entry {
                                       table_name: "vlan_membership_table"
                                       matches {
                                         name: "vlan_id"
                                         exact { hex_str: "0x00a" }
                                       }
                                       matches {
                                         name: "port"
                                         exact { str: "1" }
                                       }
                                       action { name: "make_tagged_member" }
                                     }
                                   )pb"),
                                   EqualsProto(R"pb(
                                     table_entry {
                                       table_name: "vlan_membership_table"
                                       matches {
                                         name: "vlan_id"
                                         exact { hex_str: "0x00b" }
                                       }
                                       matches {
                                         name: "port"
                                         exact { str: "2" }
                                       }
                                       action { name: "make_untagged_member" }
                                     }
                                   )pb")));
}

TEST(EntryBuilder, AddPreIngressAclEntryMatchingInPortForVrfWithPriority) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kTor);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddPreIngressAclTableEntry("vrf-1", {.in_port = "ingress-port-1"})
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), ElementsAre(Partially(EqualsProto(R"pb(
                table_entry {
                  table_name: "acl_pre_ingress_table"
                  matches {
                    name: "in_port"
                    optional { value { str: "ingress-port-1" } }
                  }
                  priority: 1
                  action {
                    name: "set_vrf"
                    params {
                      name: "vrf_id"
                      value { str: "vrf-1" }
                    }
                  }
                }
              )pb"))));
}

TEST(EntryBuilder, AddWcmpGroupTableEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kTor);
  std::vector<WcmpGroupAction> wcmp_group_actions = {
      {.nexthop_id = "nexthop-1", .weight = 1},
      {.nexthop_id = "nexthop-2", .weight = 2, .watch_port = "watchport-1"}};

  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddWcmpGroupTableEntry("group-1", absl::MakeSpan(wcmp_group_actions))
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), ElementsAre(Partially(EqualsProto(R"pb(
                table_entry {
                  table_name: "wcmp_group_table"
                  matches {
                    name: "wcmp_group_id"
                    exact { str: "group-1" }
                  }
                  action_set {
                    actions {
                      action {
                        name: "set_nexthop_id"
                        params {
                          name: "nexthop_id"
                          value { str: "nexthop-1" }
                        }
                      }
                      weight: 1
                    }
                    actions {
                      action {
                        name: "set_nexthop_id"
                        params {
                          name: "nexthop_id"
                          value { str: "nexthop-2" }
                        }
                      }
                      weight: 2
                      watch_port: "watchport-1"
                    }
                  }
                })pb"))));
}

TEST(AddNexthopRifNeighborEntriesTest, SetIpNexthopWithDefaultMacRewrite) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kTor);
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities entities,
                       EntryBuilder()
                           .AddNexthopRifNeighborEntries("nexthop-1", "port-1")
                           .LogPdEntries()
                           .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(),
              UnorderedElementsAre(
                  Partially(EqualsProto(R"pb(table_entry {
                                               table_name: "neighbor_table"
                                             })pb")),
                  Partially(EqualsProto(
                      R"pb(table_entry {
                             table_name: "nexthop_table"
                             matches {
                               name: "nexthop_id"
                               exact { str: "nexthop-1" }
                             }
                             action {
                               name: "set_ip_nexthop"
                               params { name: "router_interface_id" }
                             }
                           })pb")),
                  Partially(EqualsProto(
                      R"pb(table_entry {
                             table_name: "router_interface_table"
                             matches { name: "router_interface_id" }
                             action {
                               name: "unicast_set_port_and_src_mac"
                               params {
                                 name: "port"
                                 value { str: "port-1" }
                               }
                             }
                           })pb"))));
}

TEST(AddNexthopRifNeighborEntriesTest,
     DstMacRewriteDisabledAndSrcMacRewriteEnabled) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kTor);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddNexthopRifNeighborEntries(
              "nexthop-1", "port-1",
              NexthopRewriteOptions{.disable_decrement_ttl = true,
                                    .src_mac_rewrite = netaddr::MacAddress(
                                        0x01, 0x23, 0x45, 0x67, 0x89, 0xab),
                                    .dst_mac_rewrite = std::nullopt})
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(
      entities.entities(),
      IsSupersetOf({Partially(EqualsProto(
                        R"pb(table_entry {
                               table_name: "nexthop_table"
                               action {
                                 name: "set_ip_nexthop_and_disable_rewrites"
                                 params { name: "router_interface_id" }
                                 params { name: "neighbor_id" }
                                 params {
                                   name: "disable_decrement_ttl"
                                   value { hex_str: "0x1" }
                                 }
                                 params {
                                   name: "disable_src_mac_rewrite"
                                   value { hex_str: "0x0" }
                                 }
                                 params {
                                   name: "disable_dst_mac_rewrite"
                                   value { hex_str: "0x1" }
                                 }
                                 params {
                                   name: "disable_vlan_rewrite"
                                   value { hex_str: "0x0" }
                                 }
                               }
                             }
                        )pb")),
                    Partially(EqualsProto(
                        R"pb(table_entry {
                               table_name: "router_interface_table"
                               action {
                                 name: "unicast_set_port_and_src_mac"
                                 params {
                                   name: "src_mac"
                                   value { mac: "01:23:45:67:89:ab" }
                                 }
                               }
                             }
                        )pb")),
                    Partially(EqualsProto(
                        R"pb(table_entry {
                               table_name: "neighbor_table"
                               action { name: "set_dst_mac" }
                             }
                        )pb"))}));
}

TEST(AddNexthopRifNeighborEntriesTest, HasMyMacProgramming) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kTor);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddNexthopRifNeighborEntries(
              "nexthop-1", "port-1",
	      NexthopRewriteOptions{.skip_my_mac_programming = false})
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(),
              UnorderedElementsAre(
                  Partially(EqualsProto(R"pb(table_entry {
                                               table_name: "neighbor_table"
                                             })pb")),
                  Partially(EqualsProto(
                      R"pb(table_entry {
                             table_name: "nexthop_table"
                             action { name: "set_ip_nexthop" }
                           }
                      )pb")),
                  Partially(EqualsProto(
                      R"pb(table_entry {
                             table_name: "router_interface_table"
                             action { name: "set_port_and_src_mac" }
                           })pb"))));
}

TEST(AddNexthopRifNeighborEntriesTest,
     SrcMacRewriteDisabledAndDstMacRewriteEnabled) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kTor);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddNexthopRifNeighborEntries(
              "nexthop-1", "port-1",
              NexthopRewriteOptions{.disable_decrement_ttl = false,
                                    .src_mac_rewrite = std::nullopt,
                                    .dst_mac_rewrite = netaddr::MacAddress(
                                        0x01, 0x23, 0x45, 0x67, 0x89, 0xab),
                                    .disable_vlan_rewrite = true})
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(
      entities.entities(),
      IsSupersetOf({Partially(EqualsProto(
                        R"pb(table_entry {
                               table_name: "nexthop_table"
                               action {
                                 name: "set_ip_nexthop_and_disable_rewrites"
                                 params { name: "router_interface_id" }
                                 params { name: "neighbor_id" }
                                 params {
                                   name: "disable_decrement_ttl"
                                   value { hex_str: "0x0" }
                                 }
                                 params {
                                   name: "disable_src_mac_rewrite"
                                   value { hex_str: "0x1" }
                                 }
                                 params {
                                   name: "disable_dst_mac_rewrite"
                                   value { hex_str: "0x0" }
                                 }
                                 params {
                                   name: "disable_vlan_rewrite"
                                   value { hex_str: "0x1" }
                                 }
                               }
                             }
                        )pb")),
                    Partially(EqualsProto(
                        R"pb(table_entry {
                               table_name: "router_interface_table"
                               action { name: "unicast_set_port_and_src_mac" }
                             }
                        )pb")),
                    Partially(EqualsProto(
                        R"pb(table_entry {
                               table_name: "neighbor_table"
                               action {
                                 name: "set_dst_mac"
                                 params {
                                   name: "dst_mac"
                                   value { mac: "01:23:45:67:89:ab" }
                                 }
                               }
                             }
                        )pb"))}));
}

TEST(AddNexthopRifNeighborEntriesTest, AllRewritesEnabled) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kTor);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddNexthopRifNeighborEntries("nexthop-1", "port-1",
                                        {.disable_decrement_ttl = true,
                                         .src_mac_rewrite = std::nullopt,
                                         .dst_mac_rewrite = std::nullopt,
                                         .disable_vlan_rewrite = true})
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(),
              IsSupersetOf({Partially(EqualsProto(
                  R"pb(table_entry {
                         table_name: "nexthop_table"
                         action {
                           name: "set_ip_nexthop_and_disable_rewrites"
                           params { name: "router_interface_id" }
                           params { name: "neighbor_id" }
                           params {
                             name: "disable_decrement_ttl"
                             value { hex_str: "0x1" }
                           }
                           params {
                             name: "disable_src_mac_rewrite"
                             value { hex_str: "0x1" }
                           }
                           params {
                             name: "disable_dst_mac_rewrite"
                             value { hex_str: "0x1" }
                           }
                           params {
                             name: "disable_vlan_rewrite"
                             value { hex_str: "0x1" }
                           }
                         }
                       }
                  )pb"))}));
}

TEST(AddNexthopRifNeighborEntriesTest, RewritesPassedToDisableRewrites) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kTor);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddNexthopRifNeighborEntries(
              "nexthop-1", "port-1",
              NexthopRewriteOptions{.disable_decrement_ttl = false,
                                    .disable_vlan_rewrite = false})
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), IsSupersetOf({Partially(EqualsProto(
                                       R"pb(table_entry {
                                              table_name: "nexthop_table"
                                              action { name: "set_ip_nexthop" }
                                            }
                                       )pb"))}));
}

TEST(EntryBuilder,
     AddPreIngressAclTableEntryMatchingVlanIdAndSetVlanIdAndAclMetadata) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(std::bitset<kVlanIdBitwidth> vlan_id,
                       pdpi::HexStringToBitset<kVlanIdBitwidth>("0x00a"));
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddPreIngressAclEntrySettingVlanAndAclMetadata(
              /*vlan_id_hexstr=*/"0x00a", "0x12345678",
              AclPreIngressVlanTableMatchFields{
                  .vlan_id =
                      pdpi::Ternary<std::bitset<kVlanIdBitwidth>>(vlan_id)},
              1)
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), ElementsAre(Partially(EqualsProto(R"pb(
                table_entry {
                  table_name: "acl_pre_ingress_vlan_table"
                  matches {
                    name: "vlan_id"
                    ternary {
                      value { hex_str: "0x00a" }
                      mask { hex_str: "0xfff" }
                    }
                  }
                  priority: 1
                  action {
                    name: "set_outer_vlan_id_and_acl_metadata"
                    params {
                      name: "vlan_id"
                      value { hex_str: "0x00a" }
                    }
                    params {
                      name: "acl_metadata"
                      value { hex_str: "0x12345678" }
                    }
                  }
                }
              )pb"))));
}

TEST(EntryBuilder,
     AddIngressAclEntryRedirectingToPortWithMatchOnAclMetadataAddsEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kTor);
  MirrorAndRedirectMatchFields match_fields = {
      .acl_metadata = pdpi::Ternary<std::bitset<kAclMetadataBitwidth>>(
          std::bitset<kAclMetadataBitwidth>(0x10))};
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddIngressAclEntryRedirectingToPort(/*port=*/"1", match_fields)
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), Contains(Partially(EqualsProto(R"pb(
                table_entry {
                  table_name: "acl_ingress_mirror_and_redirect_table"
                  matches {
                    name: "acl_metadata"
                    ternary {
                      value { hex_str: "0x10" }
                      mask { hex_str: "0xff" }
                    }
                  }
                  priority: 1
                  action {
                    name: "redirect_to_port"
                    params {
                      name: "redirect_port"
                      value { str: "1" }
                    }
                  }
                })pb"))));
}

TEST(EntryBuilder,
     AddIngressAclTableEntryMatchingIngressPortAndInsertingTimestamp) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kTor);
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities entities,
                       EntryBuilder()
                           .AddIngressQoSTimestampingAclEntry(/*in_port =*/"1")
                           .LogPdEntries()
                           .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), ElementsAre(Partially(EqualsProto(R"pb(
                table_entry {
                  table_name: "acl_ingress_qos_table"
                  matches {
                    name: "in_port"
                    optional { value { str: "1" } }
                  }
                  action {
                    name: "append_ingress_and_egress_timestamp"
                    params {
                      name: "append_ingress_timestamp"
                      value { hex_str: "0x01" }
                    }
                    params {
                      name: "append_egress_timestamp"
                      value { hex_str: "0x01" }
                    }
                  }
                }
              )pb"))));
}

TEST(EntryBuilder, AddAclIngressQosDropTableEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kTor);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddAclIngressQosDropTableEntry(AclIngressQosMatchFields{
              .dst_mac = pdpi::Ternary<netaddr::MacAddress>(
                  netaddr::MacAddress(0x01, 0x23, 0x45, 0x67, 0x89, 0xab))})
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), ElementsAre(Partially(EqualsProto(R"pb(
                table_entry {
                  table_name: "acl_ingress_qos_table"
                  matches {
                    name: "dst_mac"
                    ternary {
                      value { mac: "01:23:45:67:89:ab" }
                      mask { mac: "ff:ff:ff:ff:ff:ff" }
                    }
                  }
                  action { name: "acl_drop" }
                }
              )pb"))));
}

}  // namespace
}  // namespace sai
