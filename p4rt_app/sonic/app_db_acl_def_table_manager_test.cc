// Copyright 2020 Google LLC
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
#include "p4rt_app/sonic/app_db_acl_def_table_manager.h"

#include <memory>

#include "absl/log/log.h"
#include "absl/strings/substitute.h"
#include "gmock/gmock.h"
#include "google/protobuf/text_format.h"
#include "gtest/gtest.h"
#include "include/nlohmann/json.hpp"
#include "gutil/status_matchers.h"
#include "p4rt_app/sonic/adapters/fake_notification_producer_adapter.h"
#include "p4rt_app/sonic/adapters/fake_sonic_db_table.h"
#include "p4rt_app/sonic/redis_connections.h"
#include "p4rt_app/utils/ir_builder.h"

namespace p4rt_app {
namespace sonic {
namespace {

using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::testing::Contains;
using ::testing::HasSubstr;
using ::testing::Key;
using ::testing::Not;
using ::testing::Pair;
using ::testing::UnorderedElementsAreArray;

P4rtTable MakeP4rtTable(FakeSonicDbTable& fake_app_db_table) {
  return P4rtTable{
      .notification_producer =
          std::make_unique<FakeNotificationProducerAdapter>(&fake_app_db_table),
  };
}

TEST(InsertAclTableDefinition, InsertsAclTableDefinition) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table"
                         annotations: "@sai_acl(INGRESS)"
                         annotations: "@sai_acl_priority(5)")pb")
          .match_field(
              R"pb(id: 123
                   name: "mac_address"
                   bitwidth: 48
                   annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_SRC_MAC)")pb",
              pdpi::MAC)
          .match_field(
              R"pb(id: 124
                   name: "in_port"
                   annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_IN_PORT)")pb",
              pdpi::STRING)
          .match_field(
              R"pb(id: 125
                   name: "vrf_id"
                   annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_VRF_ID)")pb",
              pdpi::STRING)
          .match_field(
              R"pb(id: 126
                   name: "ipmc_table_hit"
                   bitwidth: 1
                   annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_IPMC_NPU_META_DST_HIT)")pb",
              pdpi::HEX_STRING)
          .entry_action(
              IrActionDefinitionBuilder()
                  .preamble(
                      R"pb(alias: "single_param_action"
                           annotations: "@sai_action(SAI_PACKET_ACTION_FORWARD)")pb")
                  .param(
                      R"pb(id: 11
                           name: "qos"
                           annotations: "@sai_action_param(QOS_QUEUE)")pb",
                      pdpi::STRING))
          .entry_action(
              IrActionDefinitionBuilder()
                  .preamble(
                      R"pb(alias: "double_param_action"
                           annotations: "@sai_action(SAI_PACKET_ACTION_FORWARD)")pb")
                  .param(
                      R"pb(id: 1
                           name: "qos"
                           annotations: "@sai_action_param(QOS_QUEUE)")pb",
                      pdpi::STRING)
                  .param(
                      R"pb(id: 2
                           name: "dec_ttl"
                           bitwidth: 1
                           annotations: "@sai_action_param(SAI_ACL_ENTRY_ATTR_ACTION_DECREMENT_TTL)"
                      )pb",
                      pdpi::HEX_STRING))
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "metered_action"
                   annotations: "@sai_action(SAI_PACKET_ACTION_DROP, SAI_PACKET_COLOR_GREEN)")pb"))
          .entry_action(
              IrActionDefinitionBuilder()
                  .preamble(
                      R"pb(alias: "metered_action_with_param"
                           annotations: "@sai_action(SAI_PACKET_ACTION_DROP, SAI_PACKET_COLOR_GREEN)")pb")
                  .param(
                      R"pb(id: 1
                           name: "qos"
                           annotations: "@sai_action_param(QOS_QUEUE)")pb",
                      pdpi::STRING))
          .entry_action(
              IrActionDefinitionBuilder()
                  .preamble(
                      R"pb(
                        alias: "complex_metered_action_with_param"
                        annotations: "@sai_action(SAI_PACKET_ACTION_LOG, SAI_PACKET_COLOR_GREEN)"
                        annotations: "@sai_action(SAI_PACKET_ACTION_FORWARD, SAI_PACKET_COLOR_YELLOW)"
                        annotations: "@sai_action(SAI_PACKET_ACTION_DROP, SAI_PACKET_COLOR_RED)"
                      )pb")
                  .param(
                      R"pb(
                        id: 1
                        name: "qos"
                        annotations: "@sai_action_param(QOS_QUEUE)"
                      )pb",
		      pdpi::STRING))
          .entry_action(
              IrActionDefinitionBuilder()
                  .preamble(
                      R"pb(
                        alias: "complex_metered_action_with_param_and_color"
                        annotations: "@sai_action(SAI_PACKET_ACTION_FORWARD, SAI_PACKET_COLOR_GREEN)"
                        annotations: "@sai_action(SAI_PACKET_ACTION_DENY, SAI_PACKET_COLOR_RED)"
                      )pb")
                  .param(
                      R"pb(
                        id: 1
                        name: "cpu_queue"
                        annotations: "@sai_action_param(QOS_QUEUE)"
                      )pb",
                      pdpi::STRING)
                  .param(
                      R"pb(
                        id: 2
                        name: "green_multicast_queue"
                        annotations: "@sai_action_param(SAI_POLICER_ATTR_COLORED_PACKET_SET_MCAST_COS_QUEUE_ACTION, SAI_PACKET_COLOR_GREEN)"
                      )pb",
                      pdpi::STRING)
                  .param(
                      R"pb(
                        id: 3
                        name: "red_multicast_queue"
                        annotations: "@sai_action_param(SAI_POLICER_ATTR_COLORED_PACKET_SET_MCAST_COS_QUEUE_ACTION, SAI_PACKET_COLOR_RED)"
                      )pb",
                      pdpi::STRING))
          .entry_action(
              IrActionDefinitionBuilder()
                  .preamble(
                      R"pb(
                        alias: "redirect_action_that_includes_ipmc_type"
                      )pb")
                  .param(
                      R"pb(
                        id: 1
                        name: "multicast_group_id"
                        bitwidth: 16
                        annotations: "@sai_action_param(SAI_ACL_ENTRY_ATTR_ACTION_REDIRECT)"
                        annotations: "@sai_action_param_object_type(SAI_OBJECT_TYPE_IPMC_GROUP)"
                      )pb",
                      pdpi::HEX_STRING))
          .entry_action(
              IrActionDefinitionBuilder()
                  .preamble(
                      R"pb(
                        alias: "redirect_action_that_includes_l2mc_type"
                      )pb")
                  .param(
                      R"pb(
                        id: 1
                        name: "multicast_group_id"
                        bitwidth: 16
                        annotations: "@sai_action_param(SAI_ACL_ENTRY_ATTR_ACTION_REDIRECT)"
                        annotations: "@sai_action_param_object_type(SAI_OBJECT_TYPE_L2MC_GROUP)"
                      )pb",
                      pdpi::HEX_STRING))
          .entry_action(
              IrActionDefinitionBuilder()
                  .preamble(
                      R"pb(
                        alias: "redirect_action_that_includes_next_hop_type"
                      )pb")
                  .param(
                      R"pb(
                        id: 1
                        name: "nexthop_id"
                        annotations: "@sai_action_param(SAI_ACL_ENTRY_ATTR_ACTION_REDIRECT)"
                        annotations: "@sai_action_param_object_type(SAI_OBJECT_TYPE_NEXT_HOP)"
                      )pb",
                      pdpi::STRING))
          .entry_action(
              IrActionDefinitionBuilder()
                  .preamble(
                      R"pb(
                        alias: "redirect_action_that_includes_port_type"
                      )pb")
                  .param(
                      R"pb(
                        id: 1
                        name: "port_id"
                        annotations: "@sai_action_param(SAI_ACL_ENTRY_ATTR_ACTION_REDIRECT)"
                        annotations: "@sai_action_param_object_type(SAI_OBJECT_TYPE_PORT)"
                      )pb",
                      pdpi::STRING))
          .size(512)
          .meter_unit(p4::config::v1::MeterSpec::BYTES)
          .counter_unit(p4::config::v1::CounterSpec::BOTH)();

  FakeSonicDbTable fake_table;
  FakeSonicDbTable fake_appdb_table("AppDb", &fake_table);
  P4rtTable fake_db = MakeP4rtTable(fake_appdb_table);

  ASSERT_OK(VerifyAclTableDefinition(table));
  ASSERT_OK(InsertAclTableDefinition(fake_db, table));
  std::vector<swss::FieldValueTuple> expected_values = {
      {"stage", "INGRESS"},
      {"match/mac_address", nlohmann::json::parse(R"JSON(
           {"kind": "sai_field",
            "bitwidth": 48,
            "format": "MAC",
            "sai_field": "SAI_ACL_TABLE_ATTR_FIELD_SRC_MAC"})JSON")
                                .dump()},
      {"match/in_port", nlohmann::json::parse(R"JSON(
           {"kind": "sai_field",
            "format": "STRING",
            "sai_field": "SAI_ACL_TABLE_ATTR_FIELD_IN_PORT"})JSON")
                            .dump()},
      {"match/vrf_id", nlohmann::json::parse(R"JSON(
           {"kind": "sai_field",
            "format": "STRING",
            "sai_field": "SAI_ACL_TABLE_ATTR_FIELD_VRF_ID"})JSON")
                           .dump()},
      {"match/ipmc_table_hit", nlohmann::json::parse(R"JSON(
           {"kind": "sai_field",
            "format": "HEX_STRING",
            "bitwidth": 1,
            "sai_field": "SAI_ACL_TABLE_ATTR_FIELD_IPMC_NPU_META_DST_HIT"})JSON")
                                   .dump()},
      {"action/single_param_action", nlohmann::json::parse(R"JSON(
           [{"action": "SAI_PACKET_ACTION_FORWARD"},
            {"action": "QOS_QUEUE", "param": "qos"}])JSON")
                                         .dump()},
      {"action/double_param_action", nlohmann::json::parse(R"JSON(
           [{"action": "SAI_PACKET_ACTION_FORWARD"},
            {"action": "QOS_QUEUE", "param": "qos"},
            {"action": "SAI_ACL_ENTRY_ATTR_ACTION_DECREMENT_TTL",
             "param": "dec_ttl"}])JSON")
                                         .dump()},
      {"action/metered_action", nlohmann::json::parse(R"JSON(
           [{"action": "SAI_PACKET_ACTION_DROP", "packet_color": "SAI_PACKET_COLOR_GREEN"}]
           )JSON")
                                    .dump()},
      {"action/metered_action_with_param", nlohmann::json::parse(R"JSON(
           [{"action": "SAI_PACKET_ACTION_DROP", "packet_color": "SAI_PACKET_COLOR_GREEN"},
            {"action": "QOS_QUEUE", "param": "qos"}])JSON")
                                               .dump()},
      {"action/complex_metered_action_with_param", nlohmann::json::parse(R"JSON(
           [{"action": "SAI_PACKET_ACTION_LOG", "packet_color": "SAI_PACKET_COLOR_GREEN"},
            {"action": "SAI_PACKET_ACTION_FORWARD", "packet_color": "SAI_PACKET_COLOR_YELLOW"},
            {"action": "SAI_PACKET_ACTION_DROP", "packet_color": "SAI_PACKET_COLOR_RED"},
            {"action": "QOS_QUEUE", "param": "qos"}])JSON")
                                                       .dump()},
      {"action/complex_metered_action_with_param_and_color",
       nlohmann::json::parse(R"JSON(
           [{"action": "SAI_PACKET_ACTION_FORWARD", "packet_color": "SAI_PACKET_COLOR_GREEN"},
            {"action": "SAI_PACKET_ACTION_DENY", "packet_color": "SAI_PACKET_COLOR_RED"},
            {"action": "QOS_QUEUE", "param": "cpu_queue"},
            {"action": "SAI_POLICER_ATTR_COLORED_PACKET_SET_MCAST_COS_QUEUE_ACTION",  "packet_color": "SAI_PACKET_COLOR_GREEN", "param": "green_multicast_queue"},
            {"action": "SAI_POLICER_ATTR_COLORED_PACKET_SET_MCAST_COS_QUEUE_ACTION", "packet_color": "SAI_PACKET_COLOR_RED", "param": "red_multicast_queue"}])JSON")
           .dump()},
      {"action/redirect_action_that_includes_ipmc_type",
       nlohmann::json::parse(R"JSON(
           [{"action": "SAI_ACL_ENTRY_ATTR_ACTION_REDIRECT",
             "param": "multicast_group_id",
             "object_type": "SAI_OBJECT_TYPE_IPMC_GROUP"}])JSON")
           .dump()},
      {"action/redirect_action_that_includes_l2mc_type",
       nlohmann::json::parse(R"JSON(
           [{"action": "SAI_ACL_ENTRY_ATTR_ACTION_REDIRECT",
             "param": "multicast_group_id",
             "object_type": "SAI_OBJECT_TYPE_L2MC_GROUP"}])JSON")
           .dump()},
      {"action/redirect_action_that_includes_next_hop_type",
       nlohmann::json::parse(R"JSON(
           [{"action": "SAI_ACL_ENTRY_ATTR_ACTION_REDIRECT",
             "param": "nexthop_id",
             "object_type": "SAI_OBJECT_TYPE_NEXT_HOP"}])JSON")
           .dump()},
      {"action/redirect_action_that_includes_port_type",
       nlohmann::json::parse(R"JSON(
           [{"action": "SAI_ACL_ENTRY_ATTR_ACTION_REDIRECT",
             "param": "port_id",
             "object_type": "SAI_OBJECT_TYPE_PORT"}])JSON")
           .dump()},
      {"size", "512"},
      {"meter/unit", "BYTES"},
      {"counter/unit", "BOTH"},
      {"priority", "5"},
  };
  EXPECT_THAT(fake_table.ReadTableEntry("ACL_TABLE_DEFINITION_TABLE:ACL_TABLE"),
              IsOkAndHolds(UnorderedElementsAreArray(expected_values)));
}

TEST(InsertAclTableDefinition, InsertsUdfMatchField) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table" annotations: "@sai_acl(INGRESS)")pb")
          .match_field(
              R"pb(
                id: 123
                name: "match_field_1"
                bitwidth: 16
                annotations: "@sai_udf(base=SAI_UDF_BASE_L3, offset=2, length=2)"
              )pb",
              pdpi::HEX_STRING)
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "action"
                   annotations: "@sai_action(SAI_PACKET_ACTION_DROP)")pb"))
          .size(512)();

  FakeSonicDbTable fake_table;
  FakeSonicDbTable fake_appdb_table("AppDb", &fake_table);
  P4rtTable fake_db = MakeP4rtTable(fake_appdb_table);
  ASSERT_OK(VerifyAclTableDefinition(table));
  ASSERT_OK(InsertAclTableDefinition(fake_db, table));
  std::vector<swss::FieldValueTuple> expected_values = {
      {"stage", "INGRESS"},
      {"match/match_field_1", nlohmann::json::parse(R"JSON(
           {"kind": "udf",
            "base": "SAI_UDF_BASE_L3",
            "offset": 2,
            "bitwidth": 16,
            "format": "HEX_STRING"})JSON")
                                  .dump()},
      {"action/action", nlohmann::json::parse(
                            R"JSON([{"action": "SAI_PACKET_ACTION_DROP"}])JSON")
                            .dump()},
      {"size", "512"}};
  EXPECT_THAT(fake_table.ReadTableEntry("ACL_TABLE_DEFINITION_TABLE:ACL_TABLE"),
              IsOkAndHolds(UnorderedElementsAreArray(expected_values)));
}

TEST(InsertAclTableDefinition, InsertsCompositeMatchField) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table" annotations: "@sai_acl(INGRESS)")pb")
          .match_field(
              R"pb(
                id: 123
                name: "match_field_1"
                bitwidth: 64
                annotations: "@composite_field(@sai_field(SAI_ACL_TABLE_ATTR_FIELD_DST_IPV6_WORD3), @sai_field(SAI_ACL_TABLE_ATTR_FIELD_DST_IPV6_WORD2))"
              )pb",
              pdpi::IPV6)
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "action"
                   annotations: "@sai_action(SAI_PACKET_ACTION_DROP)")pb"))
          .size(512)();

  FakeSonicDbTable fake_table;
  FakeSonicDbTable fake_appdb_table("AppDb", &fake_table);
  P4rtTable fake_db = MakeP4rtTable(fake_appdb_table);
  ASSERT_OK(VerifyAclTableDefinition(table));
  ASSERT_OK(InsertAclTableDefinition(fake_db, table));
  std::vector<swss::FieldValueTuple> expected_values = {
      {"stage", "INGRESS"},
      {"match/match_field_1", nlohmann::json::parse(R"JSON(
           {"kind": "composite",
            "format": "IPV6",
            "bitwidth": 64,
            "elements": [{
              "kind": "sai_field",
              "bitwidth": 32,
              "sai_field": "SAI_ACL_TABLE_ATTR_FIELD_DST_IPV6_WORD3"
            }, {
              "kind": "sai_field",
              "bitwidth": 32,
              "sai_field": "SAI_ACL_TABLE_ATTR_FIELD_DST_IPV6_WORD2"
            }]
            })JSON")
                                  .dump()},
      {"action/action", nlohmann::json::parse(
                            R"JSON([{"action": "SAI_PACKET_ACTION_DROP"}])JSON")
                            .dump()},
      {"size", "512"}};
  EXPECT_THAT(fake_table.ReadTableEntry("ACL_TABLE_DEFINITION_TABLE:ACL_TABLE"),
              IsOkAndHolds(UnorderedElementsAreArray(expected_values)));
}

TEST(InsertAclTableDefinition, InsertsCompositeUdfMatchField) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table" annotations: "@sai_acl(INGRESS)")pb")
          .match_field(
              R"pb(
                id: 123
                name: "match_field_1"
                bitwidth: 32
                annotations: "@composite_field(@sai_udf(base=SAI_UDF_BASE_L3, offset=2, length=2), @sai_udf(base=SAI_UDF_BASE_L3, offset=4, length=2))"
              )pb",
              pdpi::HEX_STRING)
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "action"
                   annotations: "@sai_action(SAI_PACKET_ACTION_DROP)")pb"))
          .size(512)();

  FakeSonicDbTable fake_table;
  FakeSonicDbTable fake_appdb_table("AppDb", &fake_table);
  P4rtTable fake_db = MakeP4rtTable(fake_appdb_table);
  ASSERT_OK(VerifyAclTableDefinition(table));
  ASSERT_OK(InsertAclTableDefinition(fake_db, table));
  std::vector<swss::FieldValueTuple> expected_values = {
      {"stage", "INGRESS"},
      {"match/match_field_1", nlohmann::json::parse(R"JSON(
           {"kind": "composite",
            "format": "HEX_STRING",
            "bitwidth": 32,
            "elements": [{
              "kind": "udf",
              "base": "SAI_UDF_BASE_L3",
              "offset": 2,
              "bitwidth": 16
            }, {
              "kind": "udf",
              "base": "SAI_UDF_BASE_L3",
              "offset": 4,
              "bitwidth": 16
            }]
            })JSON")
                                  .dump()},
      {"action/action", nlohmann::json::parse(R"JSON(
           [{"action": "SAI_PACKET_ACTION_DROP"}])JSON")
                            .dump()},
      {"size", "512"}};
  EXPECT_THAT(fake_table.ReadTableEntry("ACL_TABLE_DEFINITION_TABLE:ACL_TABLE"),
              IsOkAndHolds(UnorderedElementsAreArray(expected_values)));
}

TEST(InsertAclTableDefinition, OmitsPriorityIfNoPriorityAnnotation) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table" annotations: "@sai_acl(EGRESS)")pb")
          .match_field(
              R"pb(id: 123
                   name: "match"
                   annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_IN_PORT)")pb",
              pdpi::STRING)
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "action"
                   annotations: "@sai_action(SAI_PACKET_ACTION_DROP)")pb"))();

  FakeSonicDbTable fake_table;
  FakeSonicDbTable fake_appdb_table("AppDb", &fake_table);
  P4rtTable fake_db = MakeP4rtTable(fake_appdb_table);
  ASSERT_OK(VerifyAclTableDefinition(table));
  ASSERT_OK(InsertAclTableDefinition(fake_db, table));
  EXPECT_THAT(fake_table.ReadTableEntry("ACL_TABLE_DEFINITION_TABLE:ACL_TABLE"),
              IsOkAndHolds(Not(Contains(Key("priority")))));
}

TEST(InsertAclTableDefinition, FailsWithEmptyPriorityAnnotationBody) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table"
                         annotations: "@sai_acl(EGRESS)"
                         annotations: "@sai_acl_priority()")pb")
          .match_field(
              R"pb(id: 123
                   name: "match"
                   annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_IN_PORT)")pb",
              pdpi::STRING)
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "action"
                   annotations: "@sai_action(SAI_PACKET_ACTION_DROP)")pb"))();

  FakeSonicDbTable fake_table;
  FakeSonicDbTable fake_appdb_table("AppDb", &fake_table);
  P4rtTable fake_db = MakeP4rtTable(fake_appdb_table);
  EXPECT_THAT(
      VerifyAclTableDefinition(table),
      StatusIs(absl::StatusCode::kInvalidArgument, HasSubstr("priority")));
  EXPECT_THAT(
      InsertAclTableDefinition(fake_db, table),
      StatusIs(absl::StatusCode::kInvalidArgument, HasSubstr("priority")));
}

TEST(InsertAclTableDefinition, FailsWithNonIntegerPriority) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table"
                         annotations: "@sai_acl(EGRESS)"
                         annotations: "@sai_acl_priority(1.2)")pb")
          .match_field(
              R"pb(id: 123
                   name: "match"
                   annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_IN_PORT)")pb",
              pdpi::STRING)
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "action"
                   annotations: "@sai_action(SAI_PACKET_ACTION_DROP)")pb"))();

  FakeSonicDbTable fake_table;
  FakeSonicDbTable fake_appdb_table("AppDb", &fake_table);
  P4rtTable fake_db = MakeP4rtTable(fake_appdb_table);
  EXPECT_THAT(
      VerifyAclTableDefinition(table),
      StatusIs(absl::StatusCode::kInvalidArgument, HasSubstr("priority")));
  EXPECT_THAT(
      InsertAclTableDefinition(fake_db, table),
      StatusIs(absl::StatusCode::kInvalidArgument, HasSubstr("priority")));
}

// Simple table builder for meter/counter testing.
IrTableDefinitionBuilder IrTableDefinitionBuilderWithSingleMatchAction() {
  return IrTableDefinitionBuilder()
      .preamble(R"pb(alias: "Table" annotations: "@sai_acl(EGRESS)")pb")
      .match_field(
          R"pb(id: 123
               name: "match"
               annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_IN_PORT)")pb",
          pdpi::STRING)
      .entry_action(IrActionDefinitionBuilder().preamble(
          R"pb(alias: "action"
               annotations: "@sai_action(SAI_PACKET_ACTION_DROP)")pb"));
}

TEST(InsertAclTableDefinition, InsertsMeterUnitBytes) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilderWithSingleMatchAction().meter_unit(
          p4::config::v1::MeterSpec::BYTES)();
  FakeSonicDbTable fake_table;
  FakeSonicDbTable fake_appdb_table("AppDb", &fake_table);
  P4rtTable fake_db = MakeP4rtTable(fake_appdb_table);
  ASSERT_OK(VerifyAclTableDefinition(table));
  ASSERT_OK(InsertAclTableDefinition(fake_db, table));
  EXPECT_THAT(fake_table.ReadTableEntry("ACL_TABLE_DEFINITION_TABLE:ACL_TABLE"),
              IsOkAndHolds(Contains(Pair("meter/unit", "BYTES"))));
}

TEST(InsertAclTableDefinition, InsertsMeterUnitPackets) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilderWithSingleMatchAction().meter_unit(
          p4::config::v1::MeterSpec::PACKETS)();
  FakeSonicDbTable fake_table;
  FakeSonicDbTable fake_appdb_table("AppDb", &fake_table);
  P4rtTable fake_db = MakeP4rtTable(fake_appdb_table);
  ASSERT_OK(VerifyAclTableDefinition(table));
  ASSERT_OK(InsertAclTableDefinition(fake_db, table));
  EXPECT_THAT(fake_table.ReadTableEntry("ACL_TABLE_DEFINITION_TABLE:ACL_TABLE"),
              IsOkAndHolds(Contains(Pair("meter/unit", "PACKETS"))));
}

TEST(InsertAclTableDefinition, SkipsMeterUnitUnspecified) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilderWithSingleMatchAction().meter_unit(
          p4::config::v1::MeterSpec::UNSPECIFIED)();
  FakeSonicDbTable fake_table;
  FakeSonicDbTable fake_appdb_table("AppDb", &fake_table);
  P4rtTable fake_db = MakeP4rtTable(fake_appdb_table);
  ASSERT_OK(VerifyAclTableDefinition(table));
  ASSERT_OK(InsertAclTableDefinition(fake_db, table));
  EXPECT_THAT(fake_table.ReadTableEntry("ACL_TABLE_DEFINITION_TABLE:ACL_TABLE"),
              IsOkAndHolds(Not(Contains(Key("meter/unit")))));
}

TEST(InsertAclTableDefinition, SkipsMeterUnitWithNoMeter) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilderWithSingleMatchAction()();
  FakeSonicDbTable fake_table;
  FakeSonicDbTable fake_appdb_table("AppDb", &fake_table);
  P4rtTable fake_db = MakeP4rtTable(fake_appdb_table);
  ASSERT_OK(VerifyAclTableDefinition(table));
  ASSERT_OK(InsertAclTableDefinition(fake_db, table));
  EXPECT_THAT(fake_table.ReadTableEntry("ACL_TABLE_DEFINITION_TABLE:ACL_TABLE"),
              IsOkAndHolds(Not(Contains(Key("meter/unit")))));
}

TEST(InsertAclTableDefinition, InsertsCounterUnitBytes) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilderWithSingleMatchAction().counter_unit(
          p4::config::v1::CounterSpec::BYTES)();
  FakeSonicDbTable fake_table;
  FakeSonicDbTable fake_appdb_table("AppDb", &fake_table);
  P4rtTable fake_db = MakeP4rtTable(fake_appdb_table);
  ASSERT_OK(VerifyAclTableDefinition(table));
  ASSERT_OK(InsertAclTableDefinition(fake_db, table));
  EXPECT_THAT(fake_table.ReadTableEntry("ACL_TABLE_DEFINITION_TABLE:ACL_TABLE"),
              IsOkAndHolds(Contains(Pair("counter/unit", "BYTES"))));
}

TEST(InsertAclTableDefinition, InsertsCounterUnitPackets) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilderWithSingleMatchAction().counter_unit(
          p4::config::v1::CounterSpec::PACKETS)();
  FakeSonicDbTable fake_table;
  FakeSonicDbTable fake_appdb_table("AppDb", &fake_table);
  P4rtTable fake_db = MakeP4rtTable(fake_appdb_table);
  ASSERT_OK(VerifyAclTableDefinition(table));
  ASSERT_OK(InsertAclTableDefinition(fake_db, table));
  EXPECT_THAT(fake_table.ReadTableEntry("ACL_TABLE_DEFINITION_TABLE:ACL_TABLE"),
              IsOkAndHolds(Contains(Pair("counter/unit", "PACKETS"))));
}

TEST(InsertAclTableDefinition, InsertsCounterUnitBoth) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilderWithSingleMatchAction().counter_unit(
          p4::config::v1::CounterSpec::BOTH)();
  FakeSonicDbTable fake_table;
  FakeSonicDbTable fake_appdb_table("AppDb", &fake_table);
  P4rtTable fake_db = MakeP4rtTable(fake_appdb_table);
  ASSERT_OK(VerifyAclTableDefinition(table));
  ASSERT_OK(InsertAclTableDefinition(fake_db, table));
  EXPECT_THAT(fake_table.ReadTableEntry("ACL_TABLE_DEFINITION_TABLE:ACL_TABLE"),
              IsOkAndHolds(Contains(Pair("counter/unit", "BOTH"))));
}

TEST(InsertAclTableDefinition, SkipsCounterUnitUnspecified) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilderWithSingleMatchAction().counter_unit(
          p4::config::v1::CounterSpec::UNSPECIFIED)();
  FakeSonicDbTable fake_table;
  FakeSonicDbTable fake_appdb_table("AppDb", &fake_table);
  P4rtTable fake_db = MakeP4rtTable(fake_appdb_table);
  ASSERT_OK(VerifyAclTableDefinition(table));
  ASSERT_OK(InsertAclTableDefinition(fake_db, table));
  EXPECT_THAT(fake_table.ReadTableEntry("ACL_TABLE_DEFINITION_TABLE:ACL_TABLE"),
              IsOkAndHolds(Not(Contains(Key("counter/unit")))));
}

TEST(InsertAclTableDefinition, SkipsCounterUnitWithNoCounter) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilderWithSingleMatchAction()();
  FakeSonicDbTable fake_table;
  FakeSonicDbTable fake_appdb_table("AppDb", &fake_table);
  P4rtTable fake_db = MakeP4rtTable(fake_appdb_table);
  ASSERT_OK(VerifyAclTableDefinition(table));
  ASSERT_OK(InsertAclTableDefinition(fake_db, table));
  EXPECT_THAT(fake_table.ReadTableEntry("ACL_TABLE_DEFINITION_TABLE:ACL_TABLE"),
              IsOkAndHolds(Not(Contains(Key("counter/unit")))));
}

TEST(InsertAclTableDefinition, UdfComponentsAreUnordered) {
  pdpi::IrTableDefinition base_offset_length_table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table" annotations: "@sai_acl(INGRESS)")pb")
          .match_field(
              R"pb(
                id: 123
                name: "match_field_1"
                annotations: "@sai_udf(base=SAI_UDF_BASE_L3, offset=2, length=2)"
              )pb",
              pdpi::HEX_STRING)
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "action"
                   annotations: "@sai_action(SAI_PACKET_ACTION_DROP)")pb"))
          .size(512)();
  pdpi::IrTableDefinition length_offset_base_table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table" annotations: "@sai_acl(INGRESS)")pb")
          .match_field(
              R"pb(
                id: 123
                name: "match_field_1"
                annotations: "@sai_udf(length=2, offset=2, base=SAI_UDF_BASE_L3)"
              )pb",
              pdpi::HEX_STRING)
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "action"
                   annotations: "@sai_action(SAI_PACKET_ACTION_DROP)")pb"))
          .size(512)();

  FakeSonicDbTable fake_base_offset_length_table;
  FakeSonicDbTable fake_base_offset_length_appdb_table(
      "AppDb", &fake_base_offset_length_table);
  P4rtTable base_offset_length_db =
      MakeP4rtTable(fake_base_offset_length_appdb_table);
  ASSERT_OK(VerifyAclTableDefinition(base_offset_length_table));
  ASSERT_OK(InsertAclTableDefinition(base_offset_length_db,
                                     base_offset_length_table));

  FakeSonicDbTable fake_length_offset_base_table;
  FakeSonicDbTable fake_length_offset_base_appdb_table(
      "AppDb", &fake_length_offset_base_table);
  P4rtTable length_offset_base_db =
      MakeP4rtTable(fake_length_offset_base_appdb_table);
  ASSERT_OK(VerifyAclTableDefinition(length_offset_base_table));
  ASSERT_OK(InsertAclTableDefinition(length_offset_base_db,
                                     length_offset_base_table));

  const std::string entry_key = "ACL_TABLE_DEFINITION_TABLE:ACL_TABLE";
  ASSERT_OK_AND_ASSIGN(const auto base_offset_length_values,
                       fake_base_offset_length_table.ReadTableEntry(entry_key));
  ASSERT_OK_AND_ASSIGN(const auto length_offset_base_values,
                       fake_length_offset_base_table.ReadTableEntry(entry_key));
  EXPECT_THAT(length_offset_base_values,
              UnorderedElementsAreArray(base_offset_length_values));
}

enum class WhitespaceCase { kNone, kLeft, kRight, kBoth };
std::string PrintWhitespaceCase(WhitespaceCase ws_case) {
  switch (ws_case) {
    case WhitespaceCase::kNone:
      return "None";
    case WhitespaceCase::kLeft:
      return "Left";
    case WhitespaceCase::kRight:
      return "Right";
    case WhitespaceCase::kBoth:
      return "Both";
  }
  LOG(FATAL) << "Unhandled whitespace case";
  return "";
}

class WhitespaceTestBase : public ::testing::Test {
 public:
  void TestPadding(const std::string& table_template,
                   const std::string& raw_string,
                   const std::string& padded_string) {
    pdpi::IrTableDefinition raw, padded;
    google::protobuf::TextFormat::ParseFromString(
        absl::Substitute(table_template, raw_string), &raw);
    google::protobuf::TextFormat::ParseFromString(
        absl::Substitute(table_template, padded_string), &padded);

    FakeSonicDbTable raw_string_table;
    FakeSonicDbTable raw_string_appdb_table("AppDb", &raw_string_table);
    P4rtTable raw_string_db = MakeP4rtTable(raw_string_appdb_table);
    ASSERT_OK(VerifyAclTableDefinition(raw));
    ASSERT_OK(InsertAclTableDefinition(raw_string_db, raw));

    FakeSonicDbTable padded_string_table;
    FakeSonicDbTable padded_string_appdb_table("AppDb", &padded_string_table);
    P4rtTable padded_string_db = MakeP4rtTable(padded_string_appdb_table);
    ASSERT_OK(VerifyAclTableDefinition(padded));
    ASSERT_OK(InsertAclTableDefinition(padded_string_db, padded));

    const std::string entry_key = "ACL_TABLE_DEFINITION_TABLE:ACL_TABLE";
    ASSERT_OK_AND_ASSIGN(const auto raw_values,
                         raw_string_table.ReadTableEntry(entry_key));
    ASSERT_OK_AND_ASSIGN(const auto padded_values,
                         padded_string_table.ReadTableEntry(entry_key));
    EXPECT_THAT(padded_values, UnorderedElementsAreArray(raw_values));
  }
};

class WhitespaceTest : public WhitespaceTestBase,
                       public ::testing::WithParamInterface<WhitespaceCase> {};

TEST_P(WhitespaceTest, MatchField) {
  static const auto* const kTemplate = new std::string(
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table" annotations: "@sai_acl(EGRESS)")pb")
          .match_field(R"pb(id: 123
                            name: "match_field"
                            bitwidth: 32
                            annotations: "@sai_field($0)")pb",
                       pdpi::IPV4)
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "action"
                   annotations: "@sai_action(SAI_PACKET_ACTION_DROP)")pb"))
          .GetTableAsTextProto());

  switch (GetParam()) {
    case WhitespaceCase::kNone:
      return;  // Nothing to test here.
    case WhitespaceCase::kLeft:
      TestPadding(*kTemplate, "SAI_ACL_TABLE_ATTR_FIELD_SRC_IP",
                  " SAI_ACL_TABLE_ATTR_FIELD_SRC_IP");
      break;
    case WhitespaceCase::kRight:
      TestPadding(*kTemplate, "SAI_ACL_TABLE_ATTR_FIELD_SRC_IP",
                  "SAI_ACL_TABLE_ATTR_FIELD_SRC_IP  ");
      break;
    case WhitespaceCase::kBoth:
      TestPadding(*kTemplate, "SAI_ACL_TABLE_ATTR_FIELD_SRC_IP",
                  "  SAI_ACL_TABLE_ATTR_FIELD_SRC_IP ");
      break;
  }
}

TEST_P(WhitespaceTest, Stage) {
  static const auto* const kTemplate = new std::string(
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table" annotations: "@sai_acl($0)")pb")
          .match_field(
              R"pb(id: 123
                   name: "match_field"
                   bitwidth: 128
                   annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_SRC_IPV6)"
              )pb",
              pdpi::IPV6)
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "action"
                   annotations: "@sai_action(SAI_PACKET_ACTION_DROP)")pb"))
          .GetTableAsTextProto());

  switch (GetParam()) {
    case WhitespaceCase::kNone:
      return;  // Nothing to test here.
    case WhitespaceCase::kLeft:
      TestPadding(*kTemplate, "INGRESS", " INGRESS");
      break;
    case WhitespaceCase::kRight:
      TestPadding(*kTemplate, "INGRESS", "INGRESS  ");
      break;
    case WhitespaceCase::kBoth:
      TestPadding(*kTemplate, "INGRESS", "  INGRESS ");
      break;
  }
}

TEST_P(WhitespaceTest, UncoloredAction) {
  static const auto* const kTemplate = new std::string(
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table" annotations: "@sai_acl(EGRESS)")pb")
          .match_field(
              R"pb(id: 123
                   name: "match_field"
                   annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_IN_PORT)"
              )pb",
              pdpi::STRING)
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "action" annotations: "@sai_action($0)")pb"))
          .GetTableAsTextProto());

  switch (GetParam()) {
    case WhitespaceCase::kNone:
      return;  // Nothing to test here.
    case WhitespaceCase::kLeft:
      TestPadding(*kTemplate, "SAI_PACKET_ACTION_DROP",
                  " SAI_PACKET_ACTION_DROP");
      break;
    case WhitespaceCase::kRight:
      TestPadding(*kTemplate, "SAI_PACKET_ACTION_DROP",
                  "SAI_PACKET_ACTION_DROP  ");
      break;
    case WhitespaceCase::kBoth:
      TestPadding(*kTemplate, "SAI_PACKET_ACTION_DROP",
                  "  SAI_PACKET_ACTION_DROP ");
      break;
  }
}

TEST_P(WhitespaceTest, UdfBase) {
  static const auto* const kTemplate = new std::string(
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table" annotations: "@sai_acl(EGRESS)")pb")
          .match_field(
              R"pb(
                id: 123
                name: "match_field"
                annotations: "@sai_udf($0, offset=0, length=2)"
              )pb",
              pdpi::IPV4)
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "action"
                   annotations: "@sai_action(SAI_PACKET_ACTION_DROP)")pb"))
          .GetTableAsTextProto());

  switch (GetParam()) {
    case WhitespaceCase::kNone:
      return;  // Nothing to test here.
    case WhitespaceCase::kLeft:
      TestPadding(*kTemplate, "base=SAI_UDF_BASE_L3", " base= SAI_UDF_BASE_L3");
      break;
    case WhitespaceCase::kRight:
      TestPadding(*kTemplate, "base=SAI_UDF_BASE_L3",
                  "base= SAI_UDF_BASE_L3  ");
      break;
    case WhitespaceCase::kBoth:
      TestPadding(*kTemplate, "base=SAI_UDF_BASE_L3",
                  " base = SAI_UDF_BASE_L3 ");
      break;
  }
}

TEST_P(WhitespaceTest, UdfOffset) {
  static const auto* const kTemplate = new std::string(
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table" annotations: "@sai_acl(EGRESS)")pb")
          .match_field(
              R"pb(
                id: 123
                name: "match_field"
                annotations: "@sai_udf(base=SAI_UDF_BASE_L3, $0, length=2)"
              )pb",
              pdpi::IPV4)
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "action"
                   annotations: "@sai_action(SAI_PACKET_ACTION_DROP)")pb"))
          .GetTableAsTextProto());

  switch (GetParam()) {
    case WhitespaceCase::kNone:
      return;  // Nothing to test here.
    case WhitespaceCase::kLeft:
      TestPadding(*kTemplate, "offset=3", " offset= 3");
      break;
    case WhitespaceCase::kRight:
      TestPadding(*kTemplate, "offset=3", "offset= 3  ");
      break;
    case WhitespaceCase::kBoth:
      TestPadding(*kTemplate, "offset=3", " offset = 3 ");
      break;
  }
}

TEST_P(WhitespaceTest, UdfLength) {
  static const auto* const kTemplate = new std::string(
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table" annotations: "@sai_acl(EGRESS)")pb")
          .match_field(
              R"pb(
                id: 123
                name: "match_field"
                annotations: "@sai_udf(base=SAI_UDF_BASE_L3, offset=0, $0)"
              )pb",
              pdpi::IPV4)
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "action"
                   annotations: "@sai_action(SAI_PACKET_ACTION_DROP)")pb"))
          .GetTableAsTextProto());

  switch (GetParam()) {
    case WhitespaceCase::kNone:
      return;  // Nothing to test here.
    case WhitespaceCase::kLeft:
      TestPadding(*kTemplate, "length=2", " length= 2");
      break;
    case WhitespaceCase::kRight:
      TestPadding(*kTemplate, "length=2", "length =2  ");
      break;
    case WhitespaceCase::kBoth:
      TestPadding(*kTemplate, "length=2", " length = 2 ");
      break;
  }
}

INSTANTIATE_TEST_SUITE_P(
    AppDbAclMangerTest, WhitespaceTest,
    ::testing::Values(WhitespaceCase::kLeft, WhitespaceCase::kRight,
                      WhitespaceCase::kBoth),
    [](const ::testing::TestParamInfo<WhitespaceCase>& info) {
      return PrintWhitespaceCase(info.param);
    });

class ActionColorWhitespaceTest
    : public WhitespaceTestBase,
      public ::testing::WithParamInterface<
          std::tuple<WhitespaceCase, WhitespaceCase>> {};

TEST_P(ActionColorWhitespaceTest, Action) {
  static const auto* const kTemplate = new std::string(
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table" annotations: "@sai_acl(EGRESS)")pb")
          .match_field(
              R"pb(id: 123
                   name: "match_field"
                   annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_IN_PORT)")pb",
              pdpi::STRING)
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "action" annotations: "@sai_action($0)")pb"))
          .GetTableAsTextProto());

  WhitespaceCase inner_padding = std::get<0>(GetParam());
  WhitespaceCase outer_padding = std::get<1>(GetParam());

  std::string inner_action;
  switch (inner_padding) {
    case WhitespaceCase::kNone:
      inner_action = "SAI_PACKET_ACTION_DROP,SAI_PACKET_COLOR_GREEN";
      break;
    case WhitespaceCase::kLeft:
      inner_action = "SAI_PACKET_ACTION_DROP  ,SAI_PACKET_COLOR_GREEN";
      break;
    case WhitespaceCase::kRight:
      inner_action = "SAI_PACKET_ACTION_DROP, SAI_PACKET_COLOR_GREEN";
      break;
    case WhitespaceCase::kBoth:
      inner_action = "SAI_PACKET_ACTION_DROP ,  SAI_PACKET_COLOR_GREEN";
      break;
  }
  std::string action;
  switch (outer_padding) {
    case WhitespaceCase::kNone:
      action = inner_action;
      break;
    case WhitespaceCase::kLeft:
      action = absl::Substitute("  $0", inner_action);
      break;
    case WhitespaceCase::kRight:
      action = absl::Substitute("$0 ", inner_action);
      break;
    case WhitespaceCase::kBoth:
      action = absl::Substitute(" $0  ", inner_action);
      break;
  }
  TestPadding(*kTemplate, "SAI_PACKET_ACTION_DROP,SAI_PACKET_COLOR_GREEN",
              action);
}

constexpr WhitespaceCase kAllWhitespaceCases[] = {
    WhitespaceCase::kNone, WhitespaceCase::kLeft, WhitespaceCase::kRight,
    WhitespaceCase::kBoth};
INSTANTIATE_TEST_SUITE_P(
    AppDbAclMangerTest, ActionColorWhitespaceTest,
    ::testing::Combine(::testing::ValuesIn(kAllWhitespaceCases),
                       ::testing::ValuesIn(kAllWhitespaceCases)),
    [](const ::testing::TestParamInfo<ActionColorWhitespaceTest::ParamType>&
           info) {
      return std::string(absl::Substitute(
          "Inner$0_Outer$1", PrintWhitespaceCase(std::get<0>(info.param)),
          PrintWhitespaceCase(std::get<1>(info.param))));
    });

TEST(InsertAclTableDefinition, FailsWithoutAlias) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(annotations: "@sai_acl(INGRESS)")pb")
          .match_field(
              R"pb(id: 123
                   name: "match_field"
                   annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_IN_PORT)")pb",
              pdpi::STRING)
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "action_drop"
                   annotations: "@sai_action(SAI_PACKET_ACTION_DROP)")pb"))();

  FakeSonicDbTable fake_table;
  FakeSonicDbTable fake_appdb_table("AppDb", &fake_table);
  P4rtTable fake_db = MakeP4rtTable(fake_appdb_table);
  EXPECT_THAT(VerifyAclTableDefinition(table),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       HasSubstr("is missing an alias")));
  EXPECT_THAT(InsertAclTableDefinition(fake_db, table),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       HasSubstr("is missing an alias")));
}

TEST(InsertAclTableDefinition, FailsWithoutStage) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table")pb")
          .match_field(
              R"pb(id: 123
                   name: "match_field"
                   annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_IN_PORT)")pb",
              pdpi::STRING)
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "action"
                   annotations: "@sai_action(SAI_PACKET_ACTION_DROP)")pb"))();

  FakeSonicDbTable fake_table;
  FakeSonicDbTable fake_appdb_table("AppDb", &fake_table);
  P4rtTable fake_db = MakeP4rtTable(fake_appdb_table);
  EXPECT_THAT(VerifyAclTableDefinition(table),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       HasSubstr("is not an ACL table")));
  EXPECT_THAT(InsertAclTableDefinition(fake_db, table),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       HasSubstr("is not an ACL table")));
}

TEST(InsertAclTableDefinition, FailsWithoutMatchField) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table" annotations: "@sai_acl(INGRESS)")pb")
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "action"
                   annotations: "@sai_action(SAI_PACKET_ACTION_DROP)")pb"))();

  FakeSonicDbTable fake_table;
  FakeSonicDbTable fake_appdb_table("AppDb", &fake_table);
  P4rtTable fake_db = MakeP4rtTable(fake_appdb_table);
  EXPECT_THAT(
      VerifyAclTableDefinition(table),
      StatusIs(absl::StatusCode::kInvalidArgument,
               HasSubstr("ACL table requires at least one match field")));
  EXPECT_THAT(
      InsertAclTableDefinition(fake_db, table),
      StatusIs(absl::StatusCode::kInvalidArgument,
               HasSubstr("ACL table requires at least one match field")));
}

TEST(InsertAclTableDefinition, FailsWithoutAction) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table" annotations: "@sai_acl(INGRESS)")pb")
          .match_field(
              R"pb(id: 123
                   name: "match_field"
                   annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_IN_PORT)")pb",
              pdpi::STRING)();

  FakeSonicDbTable fake_table;
  FakeSonicDbTable fake_appdb_table("AppDb", &fake_table);
  P4rtTable fake_db = MakeP4rtTable(fake_appdb_table);
  EXPECT_THAT(VerifyAclTableDefinition(table),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       HasSubstr("ACL table requires at least one action")));
  EXPECT_THAT(InsertAclTableDefinition(fake_db, table),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       HasSubstr("ACL table requires at least one action")));
}

TEST(InsertAclTableDefinition, FailsWithoutSaiAction) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table" annotations: "@sai_acl(INGRESS)")pb")
          .match_field(
              R"pb(id: 123
                   name: "match_field"
                   annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_IN_PORT)")pb",
              pdpi::STRING)
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "skip_action" annotations: "@not_a_sai_action()")pb"))
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "add_action"
                   annotations: "@sai_action(SAI_PACKET_ACTION_DROP)")pb"))();

  FakeSonicDbTable fake_table;
  FakeSonicDbTable fake_appdb_table("AppDb", &fake_table);
  P4rtTable fake_db = MakeP4rtTable(fake_appdb_table);
  EXPECT_THAT(VerifyAclTableDefinition(table),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       HasSubstr("has no SAI mapping.")));
  EXPECT_THAT(InsertAclTableDefinition(fake_db, table),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       HasSubstr("has no SAI mapping.")));
}

TEST(InsertAclTableDefinition, DISABLED_FailsWithNonNoActionConstDefaultAction) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table" annotations: "@sai_acl(INGRESS)")pb")
          .match_field(
              R"pb(id: 123
                   name: "match_field"
                   annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_IN_PORT)")pb",
              pdpi::STRING)
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "entry_action"
                   annotations: "@sai_action(SAI_PACKET_ACTION_DROP)")pb"))
          .const_default_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "default_action"
                   annotations: "@sai_action(SAI_PACKET_ACTION_DROP)")pb"))();

  FakeSonicDbTable fake_table;
  FakeSonicDbTable fake_appdb_table("AppDb", &fake_table);
  P4rtTable fake_db = MakeP4rtTable(fake_appdb_table);
  EXPECT_THAT(
      VerifyAclTableDefinition(table),
      StatusIs(absl::StatusCode::kInvalidArgument,
               HasSubstr("const_default_action must refer to NoAction.")));
  EXPECT_THAT(
      InsertAclTableDefinition(fake_db, table),
      StatusIs(absl::StatusCode::kInvalidArgument,
               HasSubstr("const_default_action must refer to NoAction.")));
}

TEST(InsertAclTableDefinition, IgnoresNoActionConstDefaultAction) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table" annotations: "@sai_acl(INGRESS)")pb")
          .match_field(
              R"pb(id: 123
                   name: "match_field"
                   annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_IN_PORT)")pb",
              pdpi::STRING)
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "entry_action"
                   annotations: "@sai_action(SAI_PACKET_ACTION_DROP)")pb"))
          .const_default_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "NoAction")pb"))();

  auto control_table = table;
  control_table.clear_const_default_action();
  FakeSonicDbTable fake_expected_table;
  FakeSonicDbTable fake_expected_appdb_table("AppDb", &fake_expected_table);
  P4rtTable fake_expected_db = MakeP4rtTable(fake_expected_appdb_table);
  EXPECT_OK(VerifyAclTableDefinition(control_table));
  EXPECT_OK(InsertAclTableDefinition(fake_expected_db, control_table));
  ASSERT_OK_AND_ASSIGN(auto expected_values,
                       fake_expected_table.ReadTableEntry(
                           "ACL_TABLE_DEFINITION_TABLE:ACL_TABLE"));

  FakeSonicDbTable fake_table;
  FakeSonicDbTable fake_appdb_table("AppDb", &fake_table);
  P4rtTable fake_db = MakeP4rtTable(fake_appdb_table);
  EXPECT_OK(VerifyAclTableDefinition(table));
  EXPECT_OK(InsertAclTableDefinition(fake_db, table));
  ASSERT_OK_AND_ASSIGN(
      auto actual_values,
      fake_table.ReadTableEntry("ACL_TABLE_DEFINITION_TABLE:ACL_TABLE"));

  EXPECT_THAT(actual_values, UnorderedElementsAreArray(expected_values));
}

TEST(InsertAclTableDefinition, SkipsDefaultOnlyActions) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table" annotations: "@sai_acl(INGRESS)")pb")
          .match_field(
              R"pb(id: 123
                   name: "match_field"
                   annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_IN_PORT)")pb",
              pdpi::STRING)
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "entry_action"
                   annotations: "@sai_action(SAI_PACKET_ACTION_DROP)")pb"))
          .default_only_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "default_action"
                   annotations: "@sai_action(SAI_PACKET_ACTION_DROP)")pb"))();

  pdpi::IrTableDefinition control_table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table" annotations: "@sai_acl(INGRESS)")pb")
          .match_field(
              R"pb(id: 123
                   name: "match_field"
                   annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_IN_PORT)")pb",
              pdpi::STRING)
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "entry_action"
                   annotations: "@sai_action(SAI_PACKET_ACTION_DROP)")pb"))();

  FakeSonicDbTable fake_expected_table;
  FakeSonicDbTable fake_expected_appdb_table("AppDb", &fake_expected_table);
  P4rtTable fake_expected_db = MakeP4rtTable(fake_expected_appdb_table);
  EXPECT_OK(VerifyAclTableDefinition(control_table));
  EXPECT_OK(InsertAclTableDefinition(fake_expected_db, control_table));
  ASSERT_OK_AND_ASSIGN(auto expected_values,
                       fake_expected_table.ReadTableEntry(
                           "ACL_TABLE_DEFINITION_TABLE:ACL_TABLE"));

  FakeSonicDbTable fake_table;
  FakeSonicDbTable fake_appdb_table("AppDb", &fake_table);
  P4rtTable fake_db = MakeP4rtTable(fake_appdb_table);
  EXPECT_OK(VerifyAclTableDefinition(table));
  EXPECT_OK(InsertAclTableDefinition(fake_db, table));
  ASSERT_OK_AND_ASSIGN(
      auto actual_values,
      fake_table.ReadTableEntry("ACL_TABLE_DEFINITION_TABLE:ACL_TABLE"));

  EXPECT_THAT(actual_values, UnorderedElementsAreArray(expected_values));
}

class BadMatchFieldTest
    : public ::testing::TestWithParam<std::pair<std::string, std::string>> {
 public:
  // Set of TestCase name and match field string.
  static const std::vector<std::pair<std::string, std::string>>& TestCases() {
    static const auto* const kCases = new std::vector<
        std::pair<std::string, std::string>>({
        {"MissingName",
         R"pb(id: 123
              bitwidth: 8
              annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_TC)")pb"},
        {"MissingAnnotation", R"pb(id: 123 bitwidth: 8 name: "match_field")pb"},
        {"EmptyAnnotation", R"pb(id: 123
                                 bitwidth: 8
                                 name: "match_field"
                                 annotations: "@sai_field()")pb"},
#ifdef __EXCEPTIONS
        {"TooManyAnnotationArgs",
         R"pb(id: 123
              bitwidth: 8
              name: "match_field"
              annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_TC, SAI_ACL_TABLE_ATTR_FIELD_TTL)")pb"},
        {"UnsupportedSaiMatchField",
         R"pb(id: 123
              bitwidth: 8
              name: "match_field"
              annotations: "@sai_field(NOT_A_MATCH_FIELD)")pb"},
#endif
        {"BadFormat",
         R"pb(id: 123
              name: "match_field"
              annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_IN_PORT)")pb"},
        {"MissingBitwidth",
         R"pb(id: 123
              name: "match_field"
              annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_TC)")pb"},
        {"BitwidthTooLarge",
         R"pb(id: 123
              bitwidth: 9
              name: "match_field"
              annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_TC)")pb"},
        {"UdfMatchMissingBase",
         R"pb(
           id: 123
           name: "match_field"
           annotations: "@sai_udf(offset=2, length=6)"
         )pb"},
        {"UdfMatchMissingOffset",
         R"pb(
           id: 123
           name: "match_field"
           annotations: "@sai_udf(base=SAI_UDF_BASE_L3, length=6)"
         )pb"},
        {"UdfMatchMissingLength",
         R"pb(
           id: 123
           name: "match_field"
           annotations: "@sai_udf(base=SAI_UDF_BASE_L3, offset=6)"
         )pb"},
        {"UdfMatchLengthMismatch",
         R"pb(
           id: 123
           name: "match_field"
           bitwidth: 16
           annotations: "@sai_udf(base=SAI_UDF_BASE_L3, offset=0, length=6)"
         )pb"},
        {"UdfMatchHasUnknownArgument",
         R"pb(
           id: 123
           name: "match_field"
           annotations: "@sai_udf(base=SAI_UDF_BASE_L3, offset=6, length=6, a=2)"
         )pb"},
        {"UdfMatchHasDuplicateBase",
         R"pb(
           id: 123
           name: "match_field"
           annotations: "@sai_udf(base=SAI_UDF_BASE_L3, offset=6, length=6, base=SAI_UDF_BASE_L3)"
         )pb"},
        {"UdfMatchHasDuplicateOffset",
         R"pb(
           id: 123
           name: "match_field"
           annotations: "@sai_udf(base=SAI_UDF_BASE_L3, offset=6, length=6, offset=6)"
         )pb"},
        {"UdfMatchHasDuplicateLength",
         R"pb(
           id: 123
           name: "match_field"
           annotations: "@sai_udf(base=SAI_UDF_BASE_L3, offset=6, length=6, length=6)"
         )pb"},
        {"UdfMatchOffsetIsNegative",
         R"pb(
           id: 123
           name: "match_field"
           annotations: "@sai_udf(base=SAI_UDF_BASE_L3, offset=-6, length=6)"
         )pb"},
        {"UdfMatchLengthIsNegative",
         R"pb(
           id: 123
           name: "match_field"
           annotations: "@sai_udf(base=SAI_UDF_BASE_L3, offset=6, length=-6)"
         )pb"},
        {"CompositeFieldWithNoElement",
         R"pb(
           id: 123
           name: "match_field"
           bitwidth: 32
           annotations: "@composite_field()"
         )pb"},
        {"CompositeFieldWithUnknownElement",
         R"pb(
           id: 123
           name: "match_field"
           bitwidth: 10
           annotations: "@composite_field(@badfield(SAI_ACL_TABLE_ATTR_FIELD_ECN), @sai_field(SAI_ACL_TABLE_ATTR_FIELD_TC))"
         )pb"},
        {"CompositeFieldWithBadlyFormattedElement",
         R"pb(
           id: 123
           name: "match_field"
           bitwidth: 10
           annotations: "@composite_field(@sai_field(SAI_ACL_TABLE_ATTR_FIELD_TC), sai_field(SAI_ACL_TABLE_ATTR_FIELD_ECN))"
         )pb"},
        {"CompositeFieldWithBadTotalLength",
         R"pb(
           id: 123
           name: "match_field"
           bitwidth: 63
           annotations: "@composite_field(@sai_field(SAI_ACL_TABLE_ATTR_FIELD_DST_IPV6_WORD3), @sai_field(SAI_ACL_TABLE_ATTR_FIELD_DST_IPV6_WORD2))"
         )pb"},
        {"CompositeFieldUdfWithBadTotalLength",
         R"pb(
           id: 123
           name: "match_field"
           bitwidth: 31
           annotations: "@composite_field(@sai_udf(base=SAI_UDF_BASE_L3, offset=0, length=2), @sai_udf(base=SAI_UDF_BASE_L3, offset=2, length=2))"
         )pb"},
#ifdef __EXCEPTIONS
        {"CompositeFieldWithUnknownSaiField",
         R"pb(
           id: 123
           name: "match_field"
           bitwidth: 66
           annotations: "@composite_field(@sai_field(A), @sai_field(SAI_ACL_TABLE_ATTR_FIELD_DST_IPV6_WORD2))"
         )pb"},
#endif
        {"CompositeFieldWithEmptySaiField",
         R"pb(
           id: 123
           name: "match_field"
           bitwidth: 66
           annotations: "@composite_field(@sai_field(), @sai_field(SAI_ACL_TABLE_ATTR_FIELD_DST_IPV6_WORD2))"
         )pb"},
        {"CompositeFieldWithBadUdf",
         R"pb(
           id: 123
           name: "match_field"
           bitwidth: 66
           annotations: "@composite_field(@sai_udf(length=2), @sai_udf(base=SAI_UDF_BASE_L3, offset=2, length=2))"
         )pb"},
    });
    return *kCases;
  }
};

TEST_P(BadMatchFieldTest, DISABLED_ReturnsFailure) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table" annotations: "@sai_acl(INGRESS)")pb")
          .match_field(GetParam().second, pdpi::HEX_STRING)
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "action"
                   annotations: "@sai_action(SAI_ACL_ENTRY_ATTR_ACTION_REDIRECT)")pb"))();

  FakeSonicDbTable fake_table;
  FakeSonicDbTable fake_appdb_table("AppDb", &fake_table);
  P4rtTable fake_db = MakeP4rtTable(fake_appdb_table);
  EXPECT_THAT(
      VerifyAclTableDefinition(table),
      StatusIs(absl::StatusCode::kInvalidArgument, HasSubstr("match_field")));
  EXPECT_THAT(
      InsertAclTableDefinition(fake_db, table),
      StatusIs(absl::StatusCode::kInvalidArgument, HasSubstr("match_field")));
}

INSTANTIATE_TEST_SUITE_P(
    InsertAclTableDefinition, BadMatchFieldTest,
    ::testing::ValuesIn(BadMatchFieldTest::TestCases()),
    [](const ::testing::TestParamInfo<BadMatchFieldTest::ParamType>& info) {
      return info.param.first;
    });

class BadActionTest
    : public ::testing::TestWithParam<std::pair<std::string, std::string>> {
 public:
  // Set of TestCase name and action preamble string.
  static const std::vector<std::pair<std::string, std::string>>& TestCases() {
    static const auto* const kCases = new std::vector<
        std::pair<std::string, std::string>>({
        {"MissingAlias",
         R"pb(annotations: "@sai_action(SAI_PACKET_ACTION_DROP)")pb"},
        {"EmptyAnnotation",
         R"pb(alias: "action" annotations: "@sai_action()")pb"},
        {"InvalidColor",
         R"pb(
           alias: "action"
           annotations: "@sai_action(SAI_PACKET_ACTION_DROP, SAI_PACKET_ACTION_LOG)"
         )pb"},
        {"TooManyAnnotationArgs",
         R"pb(
           alias: "action"
           annotations: "@sai_action(SAI_PACKET_ACTION_DROP, SAI_PACKET_ACTION_LOG, SAI_PACKET_ACTION_TRAP)"
         )pb"},
        {"ParamOnlyAction", R"pb(alias: "action"
                                 annotations: "@sai_action(QOS_QUEUE)")pb"},
#ifdef __EXCEPTIONS
        {"UnsupportedSaiAction",
         R"pb(annotations: "@sai_action(NOT_AN_ACTION)")pb"},
#endif
    });
    return *kCases;
  }
};

TEST_P(BadActionTest, DISABLED_ReturnsFailure) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table" annotations: "@sai_acl(INGRESS)")pb")
          .match_field(
              R"pb(id: 123
                   name: "match"
                   annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_IN_PORT)")pb",
              pdpi::STRING)
          .entry_action(
              IrActionDefinitionBuilder().preamble(GetParam().second))();

  FakeSonicDbTable fake_table;
  FakeSonicDbTable fake_appdb_table("AppDb", &fake_table);
  P4rtTable fake_db = MakeP4rtTable(fake_appdb_table);
  EXPECT_THAT(
      VerifyAclTableDefinition(table),
      StatusIs(absl::StatusCode::kInvalidArgument, HasSubstr("action")));
  EXPECT_THAT(
      InsertAclTableDefinition(fake_db, table),
      StatusIs(absl::StatusCode::kInvalidArgument, HasSubstr("action")));
}

INSTANTIATE_TEST_SUITE_P(
    InsertAclTableDefinition, BadActionTest,
    ::testing::ValuesIn(BadActionTest::TestCases()),
    [](const ::testing::TestParamInfo<BadActionTest::ParamType>& info) {
      return info.param.first;
    });

class BadActionParamTest
    : public ::testing::TestWithParam<std::pair<std::string, std::string>> {
 public:
  // Set of test case name and action param string.
  static const std::vector<std::pair<std::string, std::string>>& TestCases() {
    static const auto* const kCases = new std::vector<
        std::pair<std::string, std::string>>({
        {"MissingName",
         R"pb(id: 1
              bitwidth: 6
              annotations: "@sai_action_param(SAI_ACL_ENTRY_ATTR_ACTION_SET_DSCP)")pb"},
        {"MissingAnnotation", R"pb(id: 1 bitwidth: 6 name: "param")pb"},
        {"MissingAnnotationArgs", R"pb(id: 1
                                       name: "param"
                                       bitwidth: 6
                                       annotations: "@sai_action_param()")pb"},
        {"TooManyAnnotationArgs",
         R"pb(id: 1
              name: "param"
              bitwidth: 6
              annotations: "@sai_action_param(SAI_ACL_ENTRY_ATTR_ACTION_SET_DSCP, QOS_QUEUE)")pb"},
        {"BadFormat", R"pb(id: 1
                           name: "param"
                           bitwidth: 6
                           annotations: "@sai_action_param(QOS_QUEUE)")pb"},
        {"MissingBitwidth",
         R"pb(id: 1
              name: "param"
              annotations: "@sai_action_param(SAI_ACL_ENTRY_ATTR_ACTION_SET_DSCP)")pb"},
        {"BitwidthTooLarge",
         R"pb(id: 1
              name: "param"
              bitwidth: 7
              annotations: "@sai_action_param(SAI_ACL_ENTRY_ATTR_ACTION_SET_DSCP)")pb"},
        {"NonParamAction",
         R"pb(id: 1
              name: "param"
              annotations: "@sai_action_param(SAI_PACKET_ACTION_DROP)")pb"},
        {"InvalidRedirectObjectType",
         R"pb(
           annotations: "@sai_action_param(SAI_ACL_ENTRY_ATTR_ACTION_REDIRECT)"
           annotations: "@sai_action_param_object_type(SAI_OBJECT_TYPE_INVALID)"
         )pb"},
        {"TooManySaiObjectTypeArguments",
         R"pb(
           annotations: "@sai_action_param(SAI_ACL_ENTRY_ATTR_ACTION_REDIRECT)"
           annotations: "@sai_action_param_object_type(SAI_OBJECT_TYPE_PORT, SAI_EXTRA)"
         )pb"},
        {"MissingSaiObjectTypeArgument",
         R"pb(
           annotations: "@sai_action_param(SAI_ACL_ENTRY_ATTR_ACTION_REDIRECT)"
           annotations: "@sai_action_param_object_type()"
         )pb"},
#ifdef __EXCEPTIONS
        {"UnknownSaiAction",
         R"pb(id: 1
              name: "param"
              bitwidth: 7
              annotations: "@sai_action_param(NOT_AN_ACTION)")pb"},
#endif
    });
    return *kCases;
  }
};

TEST_P(BadActionParamTest, DISABLED_ReturnsFailure) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table" annotations: "@sai_acl(INGRESS)")pb")
          .match_field(
              R"pb(id: 123
                   name: "match"
                   annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_IN_PORT)")pb",
              pdpi::STRING)
          .entry_action(IrActionDefinitionBuilder()
                            .preamble(R"pb(alias: "MyAction")pb")
                            .param(GetParam().second, pdpi::HEX_STRING))();

  FakeSonicDbTable fake_table;
  FakeSonicDbTable fake_appdb_table("AppDb", &fake_table);
  P4rtTable fake_db = MakeP4rtTable(fake_appdb_table);
  EXPECT_THAT(
      VerifyAclTableDefinition(table),
      StatusIs(absl::StatusCode::kInvalidArgument, HasSubstr("MyAction")));
  EXPECT_THAT(
      InsertAclTableDefinition(fake_db, table),
      StatusIs(absl::StatusCode::kInvalidArgument, HasSubstr("MyAction")));
}

INSTANTIATE_TEST_SUITE_P(
    InsertAclTableDefinition, BadActionParamTest,
    ::testing::ValuesIn(BadActionParamTest::TestCases()),
    [](const ::testing::TestParamInfo<BadActionParamTest::ParamType>& info) {
      return info.param.first;
    });

class BadStageTest
    : public ::testing::TestWithParam<std::pair<std::string, std::string>> {
 public:
  // Set of TestCase name and match field string.
  static const std::vector<std::pair<std::string, std::string>>& TestCases() {
    static const auto* const kCases =
        new std::vector<std::pair<std::string, std::string>>({
#ifdef __EXCEPTIONS
            {"UnknownStage", "I_DIGRESS"},
#endif
            {"EmptyStage", ""},
            {"MultipleStages", "INGRESS,EGRESS"},
        });
    return *kCases;
  }
};

TEST_P(BadStageTest, ReturnsMatchFieldFailure) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(absl::Substitute(R"pb(alias: "Table"
                                          annotations: "@sai_acl($0)")pb",
                                     GetParam().second))
          .match_field(
              R"pb(id: 123
                   name: "match"
                   bitwidth: 3
                   annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_IP_FLAGS)")pb",
              pdpi::HEX_STRING)
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "action"
                   annotations: "@sai_action(SAI_ACL_ENTRY_ATTR_ACTION_REDIRECT)")pb"))();

  FakeSonicDbTable fake_table;
  FakeSonicDbTable fake_appdb_table("AppDb", &fake_table);
  P4rtTable fake_db = MakeP4rtTable(fake_appdb_table);
  EXPECT_THAT(VerifyAclTableDefinition(table),
              StatusIs(absl::StatusCode::kInvalidArgument, HasSubstr("stage")));
  EXPECT_THAT(InsertAclTableDefinition(fake_db, table),
              StatusIs(absl::StatusCode::kInvalidArgument, HasSubstr("stage")));
}

INSTANTIATE_TEST_SUITE_P(
    InsertAclTableDefinition, BadStageTest,
    ::testing::ValuesIn(BadStageTest::TestCases()),
    [](const ::testing::TestParamInfo<BadStageTest::ParamType>& info) {
      return info.param.first;
    });

TEST(AppDbAclTableManagerTest, Insert_ConsistentActionOrder) {
  IrTableDefinitionBuilder table_template;
  table_template
      .preamble(R"pb(alias: "Table" annotations: "@sai_acl(INGRESS)")pb")
      .match_field(
          R"pb(id: 123
               name: "match_field"
               annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_IN_PORT)")pb",
          pdpi::STRING);

  p4::config::v1::Action::Param param1, param2;
  google::protobuf::TextFormat::ParseFromString(
      R"pb(id: 1 name: "a1" annotations: "@sai_action_param(QOS_QUEUE)")pb",
      &param1);
  google::protobuf::TextFormat::ParseFromString(
      R"pb(
        id: 2
        name: "a2"
        annotations: "@sai_action_param(SAI_ACL_ENTRY_ATTR_ACTION_MIRROR_INGRESS)"
      )pb",
      &param2);

  IrTableDefinitionBuilder incremental_table = table_template;
  incremental_table.entry_action(IrActionDefinitionBuilder()
                                     .preamble(R"pb(alias: "action")pb")
                                     .param(param1, pdpi::STRING)
                                     .param(param2, pdpi::STRING));

  IrTableDefinitionBuilder decremental_table = table_template;
  decremental_table.entry_action(IrActionDefinitionBuilder()
                                     .preamble(R"pb(alias: "action")pb")
                                     .param(param2, pdpi::STRING)
                                     .param(param1, pdpi::STRING));

  FakeSonicDbTable incremental_db_table;
  FakeSonicDbTable incremental_db_appdb_table("AppDb", &incremental_db_table);
  P4rtTable incremental_db = MakeP4rtTable(incremental_db_appdb_table);
  EXPECT_OK(VerifyAclTableDefinition(incremental_table()));
  EXPECT_OK(InsertAclTableDefinition(incremental_db, incremental_table()));

  FakeSonicDbTable decremental_db_table;
  FakeSonicDbTable decremental_db_appdb_table("AppDb", &decremental_db_table);
  P4rtTable decremental_db = MakeP4rtTable(decremental_db_appdb_table);
  EXPECT_OK(VerifyAclTableDefinition(decremental_table()));
  EXPECT_OK(InsertAclTableDefinition(decremental_db, decremental_table()));

  ASSERT_OK_AND_ASSIGN(auto incremental_result,
                       incremental_db_table.ReadTableEntry(
                           "ACL_TABLE_DEFINITION_TABLE:ACL_TABLE"));
  ASSERT_OK_AND_ASSIGN(auto decremental_result,
                       decremental_db_table.ReadTableEntry(
                           "ACL_TABLE_DEFINITION_TABLE:ACL_TABLE"));
  EXPECT_THAT(decremental_result,
              UnorderedElementsAreArray(incremental_result));
}

TEST(AppDbAclTableManagerTest, Remove) {
  pdpi::IrTableDefinition table = IrTableDefinitionBuilder().preamble(
      R"pb(alias: "Table" annotations: "@sai_acl(INGRESS)")pb")();

  FakeSonicDbTable fake_table;
  FakeSonicDbTable fake_appdb_table("AppDb", &fake_table);
  P4rtTable fake_db = MakeP4rtTable(fake_appdb_table);
  fake_table.InsertTableEntry("ACL_TABLE_DEFINITION_TABLE:ACL_TABLE",
                              {{"a", "a"}});
  ASSERT_OK(RemoveAclTableDefinition(fake_db, table));
  EXPECT_THAT(fake_table.ReadTableEntry("ACL_TABLE_DEFINITION_TABLE:ACL_TABLE"),
              StatusIs(absl::StatusCode::kNotFound));
}

}  // namespace
}  // namespace sonic
}  // namespace p4rt_app
