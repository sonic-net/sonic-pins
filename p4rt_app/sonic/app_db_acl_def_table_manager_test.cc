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

#include "absl/strings/substitute.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "google/protobuf/text_format.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "p4rt_app/utils/ir_builder.h"
#include "swss/fakes/fake_producer_state_table.h"
#include "swss/fakes/fake_sonic_db_table.h"
#include "swss/json.h"
#include "swss/json.hpp"

namespace p4rt_app {
namespace sonic {
namespace {

using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::testing::_;
using ::testing::Contains;
using ::testing::HasSubstr;
using ::testing::Key;
using ::testing::Not;
using ::testing::Pair;
using ::testing::UnorderedElementsAreArray;

TEST(InsertAclTableDefinition, InsertsAclTableDefinition) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table" annotations: "@sai_acl(INGRESS)")pb")
          .match_field(
              R"pb(id: 123
                   name: "match_field_uno"
                   bitwidth: 10
                   annotations: "@sai_field(SAI_MATCH_FIELD_1)")pb",
              pdpi::HEX_STRING)
          .match_field(
              R"pb(id: 124
                   name: "match_field_dos"
                   annotations: "@sai_field(SAI_MATCH_FIELD_2)")pb",
              pdpi::STRING)
          .entry_action(
              IrActionDefinitionBuilder()
                  .preamble(
                      R"pb(alias: "action_une"
                           annotations: "@sai_action(SAI_DEFAULT)")pb")
                  .param(
                      R"pb(id: 11
                           name: "a1_p1"
                           annotations: "@sai_action_param(SAI_ACTION_11)")pb"))
          .entry_action(
              IrActionDefinitionBuilder()
                  .preamble(
                      R"pb(alias: "action_deux"
                           annotations: "@sai_action(SAI_DEFAULT)")pb")
                  .param(
                      R"pb(id: 1
                           name: "a2_p1"
                           annotations: "@sai_action_param(SAI_ACTION_21)")pb")
                  .param(
                      R"pb(id: 2
                           name: "a2_p2"
                           annotations: "@sai_action_param(SAI_ACTION_22, RED)"
                      )pb"))
          .size(512)
          .meter_unit(p4::config::v1::MeterSpec::BYTES)
          .counter_unit(p4::config::v1::CounterSpec::BOTH)();

  swss::FakeSonicDbTable fake_table;
  swss::FakeProducerStateTable fake_db("P4RT", &fake_table);
  ASSERT_OK(InsertAclTableDefinition(fake_db, table));
  std::vector<swss::FieldValueTuple> expected_values = {
      {"stage", "INGRESS"},
      {"match/match_field_uno", nlohmann::json::parse(R"JSON(
           {"kind": "sai_field",
            "bitwidth": 10,
            "format": "HEX_STRING",
            "sai_field": "SAI_MATCH_FIELD_1"})JSON")
                                    .dump()},
      {"match/match_field_dos", nlohmann::json::parse(R"JSON(
           {"kind": "sai_field",
            "format": "STRING",
            "sai_field": "SAI_MATCH_FIELD_2"})JSON")
                                    .dump()},
      {"action/action_une", nlohmann::json::parse(R"JSON(
           [{"action": "SAI_DEFAULT"},
            {"action": "SAI_ACTION_11", "param": "a1_p1"}])JSON")
                                .dump()},
      {"action/action_deux", nlohmann::json::parse(R"JSON(
           [{"action": "SAI_DEFAULT"},
            {"action": "SAI_ACTION_21", "param": "a2_p1"},
            {"action": "SAI_ACTION_22", "param": "a2_p2", "color": "RED"}])JSON")
                                 .dump()},
      {"size", "512"},
      {"meter/unit", "BYTES"},
      {"counter/unit", "BOTH"}};
  EXPECT_THAT(fake_table.ReadTableEntry("DEFINITION:ACL_TABLE"),
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
              R"pb(alias: "action" annotations: "@sai_action(SAI_DEFAULT)")pb"))
          .size(512)();

  swss::FakeSonicDbTable fake_table;
  swss::FakeProducerStateTable fake_db("P4RT", &fake_table);
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
      {"action/action", nlohmann::json::parse(R"JSON(
           [{"action": "SAI_DEFAULT"}])JSON")
                            .dump()},
      {"size", "512"}};
  EXPECT_THAT(fake_table.ReadTableEntry("DEFINITION:ACL_TABLE"),
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
              R"pb(alias: "action" annotations: "@sai_action(SAI_DEFAULT)")pb"))
          .size(512)();

  swss::FakeSonicDbTable fake_table;
  swss::FakeProducerStateTable fake_db("P4RT", &fake_table);
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
      {"action/action", nlohmann::json::parse(R"JSON(
           [{"action": "SAI_DEFAULT"}])JSON")
                            .dump()},
      {"size", "512"}};
  EXPECT_THAT(fake_table.ReadTableEntry("DEFINITION:ACL_TABLE"),
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
              R"pb(alias: "action" annotations: "@sai_action(SAI_DEFAULT)")pb"))
          .size(512)();

  swss::FakeSonicDbTable fake_table;
  swss::FakeProducerStateTable fake_db("P4RT", &fake_table);
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
           [{"action": "SAI_DEFAULT"}])JSON")
                            .dump()},
      {"size", "512"}};
  EXPECT_THAT(fake_table.ReadTableEntry("DEFINITION:ACL_TABLE"),
              IsOkAndHolds(UnorderedElementsAreArray(expected_values)));
}

// Simple table builder for meter/counter testing.
IrTableDefinitionBuilder IrTableDefinitionBuilderWithSingleMatchAction() {
  return IrTableDefinitionBuilder()
      .preamble(R"pb(alias: "Table" annotations: "@sai_acl(EGRESS)")pb")
      .match_field(
          R"pb(id: 123 name: "match" annotations: "@sai_field(FIELD)")pb",
          pdpi::STRING)
      .entry_action(IrActionDefinitionBuilder().preamble(
          R"pb(alias: "action" annotations: "@sai_action(ACTION)")pb"));
}

TEST(InsertAclTableDefinition, InsertsMeterUnitBytes) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilderWithSingleMatchAction().meter_unit(
          p4::config::v1::MeterSpec::BYTES)();
  swss::FakeSonicDbTable fake_table;
  swss::FakeProducerStateTable fake_db("P4RT", &fake_table);
  ASSERT_OK(InsertAclTableDefinition(fake_db, table));
  EXPECT_THAT(fake_table.ReadTableEntry("DEFINITION:ACL_TABLE"),
              IsOkAndHolds(Contains(Pair("meter/unit", "BYTES"))));
}

TEST(InsertAclTableDefinition, InsertsMeterUnitPackets) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilderWithSingleMatchAction().meter_unit(
          p4::config::v1::MeterSpec::PACKETS)();
  swss::FakeSonicDbTable fake_table;
  swss::FakeProducerStateTable fake_db("P4RT", &fake_table);
  ASSERT_OK(InsertAclTableDefinition(fake_db, table));
  EXPECT_THAT(fake_table.ReadTableEntry("DEFINITION:ACL_TABLE"),
              IsOkAndHolds(Contains(Pair("meter/unit", "PACKETS"))));
}

TEST(InsertAclTableDefinition, SkipsMeterUnitUnspecified) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilderWithSingleMatchAction().meter_unit(
          p4::config::v1::MeterSpec::UNSPECIFIED)();
  swss::FakeSonicDbTable fake_table;
  swss::FakeProducerStateTable fake_db("P4RT", &fake_table);
  ASSERT_OK(InsertAclTableDefinition(fake_db, table));
  EXPECT_THAT(fake_table.ReadTableEntry("DEFINITION:ACL_TABLE"),
              IsOkAndHolds(Not(Contains(Key("meter/unit")))));
}

TEST(InsertAclTableDefinition, SkipsMeterUnitWithNoMeter) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilderWithSingleMatchAction()();
  swss::FakeSonicDbTable fake_table;
  swss::FakeProducerStateTable fake_db("P4RT", &fake_table);
  ASSERT_OK(InsertAclTableDefinition(fake_db, table));
  EXPECT_THAT(fake_table.ReadTableEntry("DEFINITION:ACL_TABLE"),
              IsOkAndHolds(Not(Contains(Key("meter/unit")))));
}

TEST(InsertAclTableDefinition, InsertsCounterUnitBytes) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilderWithSingleMatchAction().counter_unit(
          p4::config::v1::CounterSpec::BYTES)();
  swss::FakeSonicDbTable fake_table;
  swss::FakeProducerStateTable fake_db("P4RT", &fake_table);
  ASSERT_OK(InsertAclTableDefinition(fake_db, table));
  EXPECT_THAT(fake_table.ReadTableEntry("DEFINITION:ACL_TABLE"),
              IsOkAndHolds(Contains(Pair("counter/unit", "BYTES"))));
}

TEST(InsertAclTableDefinition, InsertsCounterUnitPackets) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilderWithSingleMatchAction().counter_unit(
          p4::config::v1::CounterSpec::PACKETS)();
  swss::FakeSonicDbTable fake_table;
  swss::FakeProducerStateTable fake_db("P4RT", &fake_table);
  ASSERT_OK(InsertAclTableDefinition(fake_db, table));
  EXPECT_THAT(fake_table.ReadTableEntry("DEFINITION:ACL_TABLE"),
              IsOkAndHolds(Contains(Pair("counter/unit", "PACKETS"))));
}

TEST(InsertAclTableDefinition, InsertsCounterUnitBoth) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilderWithSingleMatchAction().counter_unit(
          p4::config::v1::CounterSpec::BOTH)();
  swss::FakeSonicDbTable fake_table;
  swss::FakeProducerStateTable fake_db("P4RT", &fake_table);
  ASSERT_OK(InsertAclTableDefinition(fake_db, table));
  EXPECT_THAT(fake_table.ReadTableEntry("DEFINITION:ACL_TABLE"),
              IsOkAndHolds(Contains(Pair("counter/unit", "BOTH"))));
}

TEST(InsertAclTableDefinition, SkipsCounterUnitUnspecified) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilderWithSingleMatchAction().counter_unit(
          p4::config::v1::CounterSpec::UNSPECIFIED)();
  swss::FakeSonicDbTable fake_table;
  swss::FakeProducerStateTable fake_db("P4RT", &fake_table);
  ASSERT_OK(InsertAclTableDefinition(fake_db, table));
  EXPECT_THAT(fake_table.ReadTableEntry("DEFINITION:ACL_TABLE"),
              IsOkAndHolds(Not(Contains(Key("counter/unit")))));
}

TEST(InsertAclTableDefinition, SkipsCounterUnitWithNoCounter) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilderWithSingleMatchAction()();
  swss::FakeSonicDbTable fake_table;
  swss::FakeProducerStateTable fake_db("P4RT", &fake_table);
  ASSERT_OK(InsertAclTableDefinition(fake_db, table));
  EXPECT_THAT(fake_table.ReadTableEntry("DEFINITION:ACL_TABLE"),
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
              R"pb(alias: "action" annotations: "@sai_action(SAI_DEFAULT)")pb"))
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
              R"pb(alias: "action" annotations: "@sai_action(SAI_DEFAULT)")pb"))
          .size(512)();

  swss::FakeSonicDbTable fake_base_offset_length_table;
  swss::FakeProducerStateTable base_offset_length_db(
      "P4RT", &fake_base_offset_length_table);
  ASSERT_OK(InsertAclTableDefinition(base_offset_length_db,
                                     base_offset_length_table));

  swss::FakeSonicDbTable fake_length_offset_base_table;
  swss::FakeProducerStateTable length_offset_base_db(
      "P4RT", &fake_length_offset_base_table);
  ASSERT_OK(InsertAclTableDefinition(length_offset_base_db,
                                     length_offset_base_table));

  const std::string entry_key = "DEFINITION:ACL_TABLE";
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

    swss::FakeSonicDbTable raw_string_table;
    swss::FakeProducerStateTable raw_string_db("P4RT", &raw_string_table);
    ASSERT_OK(InsertAclTableDefinition(raw_string_db, raw));

    swss::FakeSonicDbTable padded_string_table;
    swss::FakeProducerStateTable padded_string_db("P4RT", &padded_string_table);
    ASSERT_OK(InsertAclTableDefinition(padded_string_db, padded));

    const std::string entry_key = "DEFINITION:ACL_TABLE";
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
  static const auto* const kTemplate =
      new std::string(IrTableDefinitionBuilder()
                          .preamble(R"pb(alias: "Table"
                                         annotations: "@sai_acl(EGRESS)")pb")
                          .match_field(
                              R"pb(id: 123
                                   name: "match_field"
                                   annotations: "@sai_field($0)")pb",
                              pdpi::IPV4)
                          .entry_action(IrActionDefinitionBuilder().preamble(
                              R"pb(alias: "action"
                                   annotations: "@sai_action(ACTION)")pb"))()
                          .DebugString());

  switch (GetParam()) {
    case WhitespaceCase::kNone:
      return;  // Nothing to test here.
    case WhitespaceCase::kLeft:
      TestPadding(*kTemplate, "MATCH_FIELD", " MATCH_FIELD");
      break;
    case WhitespaceCase::kRight:
      TestPadding(*kTemplate, "MATCH_FIELD", "MATCH_FIELD  ");
      break;
    case WhitespaceCase::kBoth:
      TestPadding(*kTemplate, "MATCH_FIELD", "  MATCH_FIELD ");
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
                   annotations: "@sai_field(SAI_MATCH_FIELD)")pb",
              pdpi::IPV6)
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "action" annotations: "@sai_action(ACTION)")pb"))()
          .DebugString());

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
                   annotations: "@sai_field(SAI_MATCH_FIELD)")pb",
              pdpi::STRING)
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "action" annotations: "@sai_action($0)")pb"))()
          .DebugString());

  switch (GetParam()) {
    case WhitespaceCase::kNone:
      return;  // Nothing to test here.
    case WhitespaceCase::kLeft:
      TestPadding(*kTemplate, "SAI_ACTION", " SAI_ACTION");
      break;
    case WhitespaceCase::kRight:
      TestPadding(*kTemplate, "SAI_ACTION", "SAI_ACTION  ");
      break;
    case WhitespaceCase::kBoth:
      TestPadding(*kTemplate, "SAI_ACTION", "  SAI_ACTION ");
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
              R"pb(alias: "action" annotations: "@sai_action(ACTION)")pb"))()
          .DebugString());

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
              R"pb(alias: "action" annotations: "@sai_action(ACTION)")pb"))()
          .DebugString());

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
              R"pb(alias: "action" annotations: "@sai_action(ACTION)")pb"))()
          .DebugString());

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
                   annotations: "@sai_field(SAI_MATCH_FIELD)")pb",
              pdpi::STRING)
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "action" annotations: "@sai_action($0)")pb"))()
          .DebugString());

  WhitespaceCase inner_padding = std::get<0>(GetParam());
  WhitespaceCase outer_padding = std::get<1>(GetParam());

  std::string inner_action;
  switch (inner_padding) {
    case WhitespaceCase::kNone:
      inner_action = "SAI_ACTION,GREEN";
      break;
    case WhitespaceCase::kLeft:
      inner_action = "SAI_ACTION  ,GREEN";
      break;
    case WhitespaceCase::kRight:
      inner_action = "SAI_ACTION, GREEN";
      break;
    case WhitespaceCase::kBoth:
      inner_action = "SAI_ACTION ,  GREEN";
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
  TestPadding(*kTemplate, "SAI_ACTION,GREEN", action);
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
                   annotations: "@sai_field(SAI_MATCH_FIELD)")pb",
              pdpi::STRING)
          .entry_action(
              IrActionDefinitionBuilder().preamble(
                  R"pb(alias: "action_une"
                       annotations: "@sai_action(SAI_DEFAULT)")pb"))();

  swss::FakeSonicDbTable fake_table;
  swss::FakeProducerStateTable fake_db("P4RT", &fake_table);
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
                   annotations: "@sai_field(SAI_MATCH_FIELD)")pb",
              pdpi::STRING)
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "action" annotations: "@sai_action(ACTION)")pb"))();

  swss::FakeSonicDbTable fake_table;
  swss::FakeProducerStateTable fake_db("P4RT", &fake_table);
  EXPECT_THAT(InsertAclTableDefinition(fake_db, table),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       HasSubstr("is not an ACL table")));
}

TEST(InsertAclTableDefinition, FailsWithoutMatchField) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table" annotations: "@sai_acl(INGRESS)")pb")
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "action" annotations: "@sai_action(ACTION)")pb"))();

  swss::FakeSonicDbTable fake_table;
  swss::FakeProducerStateTable fake_db("P4RT", &fake_table);
  EXPECT_THAT(
      InsertAclTableDefinition(fake_db, table),
      StatusIs(absl::StatusCode::kInvalidArgument,
               HasSubstr("ACL table requires at least one match field")));
}

TEST(InsertAclTableDefinition, FailsWithoutAction) {
  pdpi::IrTableDefinition
      table = IrTableDefinitionBuilder()
                  .preamble(
                      R"pb(alias: "Table" annotations: "@sai_acl(INGRESS)")pb")
                  .match_field(
                      R"pb(id: 123
                           name: "match_field"
                           annotations: "@sai_field(MATCH)")pb",
                      pdpi::STRING)();

  swss::FakeSonicDbTable fake_table;
  swss::FakeProducerStateTable fake_db("P4RT", &fake_table);
  EXPECT_THAT(InsertAclTableDefinition(fake_db, table),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       HasSubstr("ACL table requires at least one action")));
}

TEST(InsertAclTableDefinition, FailsWithoutSaiAction) {
  pdpi::IrTableDefinition
      table = IrTableDefinitionBuilder()
                  .preamble(
                      R"pb(alias: "Table" annotations: "@sai_acl(INGRESS)")pb")
                  .match_field(
                      R"pb(id: 123
                           name: "match_field"
                           annotations: "@sai_field(MATCH)")pb",
                      pdpi::STRING)
                  .entry_action(IrActionDefinitionBuilder().preamble(
                      R"pb(alias: "skip_action"
                           annotations: "@not_a_sai_action()")pb"))
                  .entry_action(IrActionDefinitionBuilder().preamble(
                      R"pb(alias: "add_action"
                           annotations: "@sai_action(ACTION)")pb"))();

  swss::FakeSonicDbTable fake_table;
  swss::FakeProducerStateTable fake_db("P4RT", &fake_table);
  EXPECT_THAT(InsertAclTableDefinition(fake_db, table),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       HasSubstr("has no SAI mapping.")));
}

TEST(InsertAclTableDefinition, FailsWithNonNoActionConstDefaultAction) {
  pdpi::IrTableDefinition
      table = IrTableDefinitionBuilder()
                  .preamble(
                      R"pb(alias: "Table" annotations: "@sai_acl(INGRESS)")pb")
                  .match_field(
                      R"pb(id: 123
                           name: "match_field"
                           annotations: "@sai_field(MATCH)")pb",
                      pdpi::STRING)
                  .entry_action(IrActionDefinitionBuilder().preamble(
                      R"pb(alias: "entry_action"
                           annotations: "@sai_action(ACTION)")pb"))
                  .const_default_action(IrActionDefinitionBuilder().preamble(
                      R"pb(alias: "default_action"
                           annotations: "@sai_action(ACTION)")pb"))();

  swss::FakeSonicDbTable fake_table;
  swss::FakeProducerStateTable fake_db("P4RT", &fake_table);
  EXPECT_THAT(
      InsertAclTableDefinition(fake_db, table),
      StatusIs(absl::StatusCode::kInvalidArgument,
               HasSubstr("const_default_action must refer to NoAction.")));
}

TEST(InsertAclTableDefinition, IgnoresNoActionConstDefaultAction) {
  pdpi::IrTableDefinition
      table = IrTableDefinitionBuilder()
                  .preamble(
                      R"pb(alias: "Table" annotations: "@sai_acl(INGRESS)")pb")
                  .match_field(
                      R"pb(id: 123
                           name: "match_field"
                           annotations: "@sai_field(MATCH)")pb",
                      pdpi::STRING)
                  .entry_action(IrActionDefinitionBuilder().preamble(
                      R"pb(alias: "entry_action"
                           annotations: "@sai_action(ACTION)")pb"))
                  .const_default_action(IrActionDefinitionBuilder().preamble(
                      R"pb(alias: "NoAction")pb"))();

  auto control_table = table;
  control_table.clear_const_default_action();
  swss::FakeSonicDbTable fake_expected_table;
  swss::FakeProducerStateTable fake_expected_db("P4RT", &fake_expected_table);
  EXPECT_OK(InsertAclTableDefinition(fake_expected_db, control_table));
  ASSERT_OK_AND_ASSIGN(auto expected_values, fake_expected_table.ReadTableEntry(
                                                 "DEFINITION:ACL_TABLE"));

  swss::FakeSonicDbTable fake_table;
  swss::FakeProducerStateTable fake_db("P4RT", &fake_table);
  EXPECT_OK(InsertAclTableDefinition(fake_db, table));
  ASSERT_OK_AND_ASSIGN(auto actual_values,
                       fake_table.ReadTableEntry("DEFINITION:ACL_TABLE"));

  EXPECT_THAT(actual_values, UnorderedElementsAreArray(expected_values));
}

TEST(InsertAclTableDefinition, SkipsDefaultOnlyActions) {
  pdpi::IrTableDefinition
      table = IrTableDefinitionBuilder()
                  .preamble(
                      R"pb(alias: "Table" annotations: "@sai_acl(INGRESS)")pb")
                  .match_field(
                      R"pb(id: 123
                           name: "match_field"
                           annotations: "@sai_field(MATCH)")pb",
                      pdpi::STRING)
                  .entry_action(IrActionDefinitionBuilder().preamble(
                      R"pb(alias: "entry_action"
                           annotations: "@sai_action(ACTION)")pb"))
                  .default_only_action(IrActionDefinitionBuilder().preamble(
                      R"pb(alias: "default_action"
                           annotations: "@sai_action(ACTION)")pb"))();

  pdpi::IrTableDefinition
      control_table = IrTableDefinitionBuilder()
                          .preamble(R"pb(alias: "Table"
                                         annotations: "@sai_acl(INGRESS)")pb")
                          .match_field(
                              R"pb(id: 123
                                   name: "match_field"
                                   annotations: "@sai_field(MATCH)")pb",
                              pdpi::STRING)
                          .entry_action(IrActionDefinitionBuilder().preamble(
                              R"pb(alias: "entry_action"
                                   annotations: "@sai_action(ACTION)")pb"))();

  swss::FakeSonicDbTable fake_expected_table;
  swss::FakeProducerStateTable fake_expected_db("P4RT", &fake_expected_table);
  EXPECT_OK(InsertAclTableDefinition(fake_expected_db, control_table));
  ASSERT_OK_AND_ASSIGN(auto expected_values, fake_expected_table.ReadTableEntry(
                                                 "DEFINITION:ACL_TABLE"));

  swss::FakeSonicDbTable fake_table;
  swss::FakeProducerStateTable fake_db("P4RT", &fake_table);
  EXPECT_OK(InsertAclTableDefinition(fake_db, table));
  ASSERT_OK_AND_ASSIGN(auto actual_values,
                       fake_table.ReadTableEntry("DEFINITION:ACL_TABLE"));

  EXPECT_THAT(actual_values, UnorderedElementsAreArray(expected_values));
}

class BadMatchFieldTest
    : public ::testing::TestWithParam<std::pair<std::string, std::string>> {
 public:
  // Set of TestCase name and match field string.
  static const std::vector<std::pair<std::string, std::string>>& TestCases() {
    static const auto* const kCases = new std::vector<
        std::pair<std::string, std::string>>({
        {"MissingName", R"pb(id: 123 annotations: "@sai_field(SAI_FIELD)")pb"},
        {"MissingAnnotation", R"pb(id: 123 name: "match_field")pb"},
        {"EmptyAnnotation", R"pb(id: 123 annotations: "@sai_field()")pb"},
        {"TooManyAnnotationArgs",
         R"pb(id: 123 annotations: "@sai_field(A, B)")pb"},
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
        {"CompositeFieldWithUnknownSaiField",
         R"pb(
           id: 123
           name: "match_field"
           bitwidth: 66
           annotations: "@composite_field(@sai_field(A), @sai_field(SAI_ACL_TABLE_ATTR_FIELD_DST_IPV6_WORD2))"
         )pb"},
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

// TODO: Fix.
TEST_P(BadMatchFieldTest, DISABLED_ReturnsFailure) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table" annotations: "@sai_acl(INGRESS)")pb")
          .match_field(GetParam().second, pdpi::STRING)
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(alias: "action" annotations: "@sai_action(ACTION)")pb"))();

  swss::FakeSonicDbTable fake_table;
  swss::FakeProducerStateTable fake_db("P4RT", &fake_table);
  EXPECT_THAT(InsertAclTableDefinition(fake_db, table),
              StatusIs(absl::StatusCode::kInvalidArgument, _));
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
    static const auto* const kCases =
        new std::vector<std::pair<std::string, std::string>>({
            {"MissingAlias", R"pb(annotations: "@sai_action(SAI_DEFAULT)")pb"},
            {"EmptyAnnotation", R"pb(alias: "action"
                                     annotations: "@sai_action()")pb"},
            {"TooManyAnnotationArgs",
             R"pb(alias: "action" annotations: "@sai_action(a, b, c)")pb"},
        });
    return *kCases;
  }
};

TEST_P(BadActionTest, ReturnsFailure) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table" annotations: "@sai_acl(INGRESS)")pb")
          .match_field(
              R"pb(id: 123 name: "match" annotations: "@sai_field(MATCH)")pb",
              pdpi::STRING)
          .entry_action(
              IrActionDefinitionBuilder().preamble(GetParam().second))();

  swss::FakeSonicDbTable fake_table;
  swss::FakeProducerStateTable fake_db("P4RT", &fake_table);
  EXPECT_THAT(InsertAclTableDefinition(fake_db, table),
              StatusIs(absl::StatusCode::kInvalidArgument, _));
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
    static const auto* const kCases =
        new std::vector<std::pair<std::string, std::string>>({
            {"MissingName",
             R"pb(id: 1 annotations: "@sai_action(SAI_ACTION_21)")pb"},
            {"MissingAnnotation", R"pb(id: 1 name: "a2_p1")pb"},
            {"MissingAnnotationArgs", R"pb(id: 1
                                           name: "a2_p1"
                                           annotations: "@sai_action()")pb"},
            {"TooManyAnnotationArgs",
             R"pb(id: 1 name: "a2_p1" annotations: "@sai_action(A, B, C)")pb"},
        });
    return *kCases;
  }
};

TEST_P(BadActionParamTest, ReturnsFailure) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(alias: "Table" annotations: "@sai_acl(INGRESS)")pb")
          .match_field(
              R"pb(id: 123 name: "match" annotations: "@sai_field(MATCH)")pb",
              pdpi::STRING)
          .entry_action(IrActionDefinitionBuilder()
                            .preamble(R"pb(alias: "Action")pb")
                            .param(GetParam().second))();

  swss::FakeSonicDbTable fake_table;
  swss::FakeProducerStateTable fake_db("P4RT", &fake_table);
  EXPECT_THAT(InsertAclTableDefinition(fake_db, table),
              StatusIs(absl::StatusCode::kInvalidArgument, _));
}

INSTANTIATE_TEST_SUITE_P(
    InsertAclTableDefinition, BadActionParamTest,
    ::testing::ValuesIn(BadActionParamTest::TestCases()),
    [](const ::testing::TestParamInfo<BadActionParamTest::ParamType>& info) {
      return info.param.first;
    });

TEST(AppDbAclTableManagerTest, Insert_ConsistentActionOrder) {
  IrTableDefinitionBuilder table_template;
  table_template
      .preamble(R"pb(alias: "Table" annotations: "@sai_acl(INGRESS)")pb")
      .match_field(
          R"pb(id: 123
               name: "match_field"
               annotations: "@sai_field(SAI_MATCH_FIELD)")pb",
          pdpi::STRING);

  p4::config::v1::Action::Param param1, param2;
  google::protobuf::TextFormat::ParseFromString(
      R"pb(id: 1 name: "a1" annotations: "@sai_action_param(SAI1)")pb",
      &param1);
  google::protobuf::TextFormat::ParseFromString(
      R"pb(id: 2 name: "a2" annotations: "@sai_action_param(SAI2)")pb",
      &param2);

  IrTableDefinitionBuilder incremental_table = table_template;
  incremental_table.entry_action(IrActionDefinitionBuilder()
                                     .preamble(R"pb(alias: "action")pb")
                                     .param(param1)
                                     .param(param2));

  IrTableDefinitionBuilder decremental_table = table_template;
  decremental_table.entry_action(IrActionDefinitionBuilder()
                                     .preamble(R"pb(alias: "action")pb")
                                     .param(param2)
                                     .param(param1));

  swss::FakeSonicDbTable incremental_db_table;
  swss::FakeProducerStateTable incremental_db("P4RT", &incremental_db_table);
  EXPECT_OK(InsertAclTableDefinition(incremental_db, incremental_table()));

  swss::FakeSonicDbTable decremental_db_table;
  swss::FakeProducerStateTable decremental_db("P4RT", &decremental_db_table);
  EXPECT_OK(InsertAclTableDefinition(decremental_db, decremental_table()));

  ASSERT_OK_AND_ASSIGN(
      auto incremental_result,
      incremental_db_table.ReadTableEntry("DEFINITION:ACL_TABLE"));
  ASSERT_OK_AND_ASSIGN(
      auto decremental_result,
      decremental_db_table.ReadTableEntry("DEFINITION:ACL_TABLE"));
  EXPECT_THAT(decremental_result,
              UnorderedElementsAreArray(incremental_result));
}

TEST(AppDbAclTableManagerTest, Remove) {
  pdpi::IrTableDefinition table = IrTableDefinitionBuilder().preamble(
      R"pb(alias: "Table" annotations: "@sai_acl(INGRESS)")pb")();

  swss::FakeSonicDbTable fake_table;
  swss::FakeProducerStateTable fake_db("P4RT", &fake_table);
  fake_table.InsertTableEntry("DEFINITION:ACL_TABLE", {{"a", "a"}});
  ASSERT_OK(RemoveAclTableDefinition(fake_db, table));
  EXPECT_THAT(fake_table.ReadTableEntry("DEFINITION:ACL_TABLE"),
              StatusIs(absl::StatusCode::kNotFound));
}

}  // namespace
}  // namespace sonic
}  // namespace p4rt_app
