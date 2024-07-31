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

#include <algorithm>
#include <optional>
#include <string>
#include <vector>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "p4_pdpi/netaddr/mac_address.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/netaddr/ipv4_address.h"
#include "p4_pdpi/netaddr/ipv6_address.h"
#include "p4_pdpi/netaddr/mac_address.h"
#include "p4_pdpi/pd.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"

namespace sai {
namespace {

using ::gutil::EqualsProto;
using ::gutil::HasOneofCase;
using ::gutil::IsOkAndHolds;
using ::testing::ElementsAre;
using ::testing::IsEmpty;
using ::testing::Pointwise;
using ::testing::SizeIs;

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
          .GetDedupedIrEntities(kIrP4Info, /*allow_unsupported=*/true));
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

void EraseNexthop(pdpi::IrEntities& entities) {
  entities.mutable_entities()->erase(std::remove_if(
      entities.mutable_entities()->begin(), entities.mutable_entities()->end(),
      [](const pdpi::IrEntity& entity) {
        return entity.table_entry().table_name() == "nexthop_table";
      }));
}

// TODO: Re-enable this test once prefix IPMC routes are supported
// by SAI P4.
TEST(EntryBuilder,
     DISABLED_AddEntriesForwardingIpPacketsToGivenMulticastGroupAddsEntries) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddEntriesForwardingIpPacketsToGivenMulticastGroup(123)
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info, /*allow_unsupported=*/true));
  EXPECT_THAT(entities.entities(), SizeIs(5));
}

// TODO: Re-enable this test once prefix IPMC routes are supported
// by SAI P4.
TEST(EntryBuilder,
     DISABLED_AddEntriesForwardingIpPacketsToGivenMulticastGroupSetsMulticastGroup) {  // NOLINT
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddEntriesForwardingIpPacketsToGivenMulticastGroup(123)
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info, /*allow_unsupported=*/true));
  EXPECT_THAT(entities.entities(), Contains(Partially(EqualsProto(R"pb(
                table_entry {
                  table_name: "ipv4_table"
                  action {
                    name: "set_multicast_group_id"
                    params {
                      name: "multicast_group_id"
                      value { hex_str: "0x007b" }
                    }
                  }
                }
              )pb"))));
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

TEST(EntryBuilder, AddIpv4EntryAddsDefaultEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities entities,
                       EntryBuilder()
                           .AddIpv4EntrySettingNexthopId("nexthop", "vrf")
                           .LogPdEntries()
                           .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), SizeIs(1));
  EXPECT_THAT(entities.entities(), Contains(Partially(EqualsProto(R"pb(
                table_entry { table_name: "ipv4_table" }
              )pb"))));
  EXPECT_THAT(entities.entities(), Not(Contains(Partially(EqualsProto(R"pb(
                table_entry {
                  table_name: "ipv4_table"
                  matches { name: "ipv4_dst" }
                }
              )pb")))));
}

TEST(EntryBuilder, AddIpv4EntryAddsLpmEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddIpv4EntrySettingNexthopId(
              "nexthop", "vrf",
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

TEST(EntryBuilder, AddIpv6EntryAddsDefaultEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities entities,
                       EntryBuilder()
                           .AddIpv6EntrySettingNexthopId("nexthop", "vrf")
                           .LogPdEntries()
                           .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), SizeIs(1));
  EXPECT_THAT(entities.entities(), Contains(Partially(EqualsProto(R"pb(
                table_entry { table_name: "ipv6_table" }
              )pb"))));
  EXPECT_THAT(entities.entities(), Not(Contains(Partially(EqualsProto(R"pb(
                table_entry {
                  table_name: "ipv6_table"
                  matches { name: "ipv6_dst" }
                }
              )pb")))));
}

TEST(EntryBuilder, AddIpv6EntryAddsLpmEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddIpv6EntrySettingNexthopId(
              "nexthop", "vrf",
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

TEST(EntryBuilder, AddPreIngressAclEntryAssigningVrfForGivenIpTypeAddsEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities entities,
                       EntryBuilder()
                           .AddPreIngressAclEntryAssigningVrfForGivenIpType(
                               "vrf-1", IpVersion::kIpv4)
                           .AddPreIngressAclEntryAssigningVrfForGivenIpType(
                               "vrf-1", IpVersion::kIpv6)
                           .AddPreIngressAclEntryAssigningVrfForGivenIpType(
                               "vrf-1", IpVersion::kIpv4And6)
                           .LogPdEntries()
                           .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(entities.entities(), SizeIs(3));
}

TEST(EntryBuilder, AddEntryDecappingAllIpInIpv6PacketsAddsEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddEntryDecappingAllIpInIpv6Packets()
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info, /*allow_unsupported=*/true));
  EXPECT_THAT(entities.entities(), SizeIs(1));
}

TEST(EntryBuilder, AddMulticastGroupEntryReplicaOverloadAddsEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(pdpi::IrEntities replica_overload_entities,
                       EntryBuilder()
                           .AddMulticastGroupEntry(
                               123,
                               {
                                   Replica{.egress_port = "\1", .instance = 11},
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

TEST(EntryBuilder, AddMulticastRouterInterfaceEntryAddsEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
                      .AddMulticastRouterInterfaceEntry({
                      .multicast_replica_port = "\1",
                      .multicast_replica_instance = 15,
                      .src_mac = netaddr::MacAddress(1, 2, 3, 4, 5, 6),
                  })
                  .LogPdEntries()
                  .GetDedupedIrEntities(kIrP4Info, /*allow_unsupported=*/true));
  EXPECT_THAT(entities.entities(), ElementsAre(Partially(EqualsProto(R"pb(
                table_entry {
                  table_name: "multicast_router_interface_table"
                  action { name: "set_multicast_src_mac" }
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
          .GetDedupedIrEntities(kIrP4Info, /*allow_unsupported=*/true));
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
          .GetDedupedIrEntities(kIrP4Info, /*allow_unsupported=*/true));
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
          .GetDedupedIrEntities(kIrP4Info, /*allow_unsupported=*/true));
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
          .GetDedupedIrEntities(kIrP4Info, /*allow_unsupported=*/true));
  EXPECT_THAT(
      entities.entities(), ElementsAre(Partially(EqualsProto(R"pb(
        table_entry {
          table_name: "multicast_router_interface_table"
          action { name: "multicast_set_src_mac_and_preserve_ingress_vlan_id" }
        }
      )pb"))));
}

TEST(EntryBuilder, AddMulticastRouteAddsIpv4Entry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kFabricBorderRouter);
  ASSERT_OK_AND_ASSIGN(auto dst_ip,
                       netaddr::Ipv4Address::OfString("225.10.20.32"));
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddMulticastRoute("vrf-1", dst_ip, 0x42)
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info, /*allow_unsupported=*/true));
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
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddMulticastRoute("vrf-2", dst_ip, 0x123)
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info, /*allow_unsupported=*/true));
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
          .GetDedupedIrEntities(kIrP4Info, /*allow_unsupported=*/true));
  EXPECT_THAT(entities.entities(), ElementsAre(Partially(EqualsProto(R"pb(
                table_entry { table_name: "mirror_session_table" }
              )pb"))));
}

TEST(EntryBuilder, AddMarkToMirrorAclEntryTest) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kTor);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddMarkToMirrorAclEntry(MarkToMirrorParams{
              .ingress_port = "1",
              .mirror_session_id = "id",
          })
          .LogPdEntries()
          // TODO: Remove unsupported once the
          // switch supports mirroring-related tables.
          .GetDedupedIrEntities(kIrP4Info, /*allow_unsupported=*/true));
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
  };
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddIngressAclEntryRedirectingToNexthop("nexthop", match_fields)
          .LogPdEntries()
          .GetDedupedIrEntities(kIrP4Info));
  EXPECT_THAT(
      entities.entities(), ElementsAre(Partially(EqualsProto(R"pb(
        table_entry { table_name: "acl_ingress_mirror_and_redirect_table" }
      )pb"))));
}

TEST(EntryBuilder, AddIngressAclEntryRedirectingToMulticastGroupAddsEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kTor);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder()
          .AddIngressAclEntryRedirectingToMulticastGroup(123)
          .LogPdEntries()
          // TODO: Remove `allow_unsupported` flag once the switch
          // supports multicast-related entries.
          .GetDedupedIrEntities(kIrP4Info, /*allow_unsupported=*/true));
  EXPECT_THAT(
      entities.entities(), ElementsAre(Partially(EqualsProto(R"pb(
        table_entry { table_name: "acl_ingress_mirror_and_redirect_table" }
      )pb"))));
}

TEST(EntryBuilder, AddVlanEntryAddsCorrectEntry) {
  pdpi::IrP4Info kIrP4Info = GetIrP4Info(Instantiation::kTor);
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrEntities entities,
      EntryBuilder().AddVlanEntry("0x00a").LogPdEntries().GetDedupedIrEntities(
          kIrP4Info, /*allow_unsupported=*/true));
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
          .GetDedupedIrEntities(kIrP4Info, /*allow_unsupported=*/true));
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

}  // namespace
}  // namespace sai
