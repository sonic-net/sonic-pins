// Copyright 2022 Google LLC
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
#include "p4rt_app/p4runtime/p4info_verification_schema.h"

#include <set>

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/substitute.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4rt_app/p4runtime/p4info_verification_schema.pb.h"
#include "p4rt_app/utils/ir_builder.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"

namespace p4rt_app {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::testing::AllOf;
using ::testing::Gt;
using ::testing::HasSubstr;
using ::testing::MatchesRegex;
using ::testing::Property;
using ::testing::ValuesIn;

// Returns a default, valid match field for testing.
p4::config::v1::MatchField DefaultMatchField() {
  p4::config::v1::MatchField match_field;
  google::protobuf::TextFormat::ParseFromString(
      R"pb(id: 1 name: "match" match_type: EXACT bitwidth: 10)pb",
      &match_field);
  return match_field;
}

// Returns a default, valid action for testing.
pdpi::IrActionDefinition DefaultAction() {
  return IrActionDefinitionBuilder().preamble(R"pb(id: 1 alias: "Action")pb")();
}

class FormatTest : public testing::TestWithParam<pdpi::Format> {};

// Tests that all action formats (except HEX_STRING) are converted correctly.
// HEX_STRING is tested in ConvertsEachMatchFieldFormat.
TEST_P(FormatTest, ConvertsEachActionFormat) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(id: 1 alias: "Table")pb")
          .match_field(
              R"pb(id: 1 name: "match" match_type: EXACT bitwidth: 10)pb",
              pdpi::Format::HEX_STRING)
          .entry_action(IrActionDefinitionBuilder()
                            .preamble(R"pb(alias: "Action")pb")
                            .param(R"pb(id: 1 name: "param")pb", GetParam()))();
  pdpi::IrP4Info irp4info;
  (*irp4info.mutable_tables_by_id())[1] = table;
  (*irp4info.mutable_tables_by_name())["Table"] = table;

  EXPECT_THAT(ConvertToSchema(irp4info),
              IsOkAndHolds(EqualsProto(absl::Substitute(
                  R"pb(
                    tables {
                      name: "Table"
                      match_fields {
                        name: "match"
                        format: HEX_STRING
                        bitwidth: 10
                        type: EXACT
                      }
                      actions {
                        name: "Action"
                        parameters { name: "param" format: $0 }
                      }
                    }
                  )pb",
                  pdpi::Format_Name(GetParam())))));
}

// Tests that all match field formats (except HEX_STRING) are converted
// correctly. HEX_STRING is tested in ConvertsEachActionFormat.
TEST_P(FormatTest, ConvertsEachMatchFieldFormat) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(id: 1 alias: "Table")pb")
          .match_field(R"pb(id: 1 name: "match" match_type: EXACT)pb",
                       GetParam())
          .entry_action(IrActionDefinitionBuilder()
                            .preamble(R"pb(alias: "Action")pb")
                            .param(R"pb(id: 1 name: "param" bitwidth: 10)pb",
                                   pdpi::Format::HEX_STRING))();
  pdpi::IrP4Info irp4info;
  (*irp4info.mutable_tables_by_id())[1] = table;
  (*irp4info.mutable_tables_by_name())["Table"] = table;

  EXPECT_THAT(
      ConvertToSchema(irp4info),
      IsOkAndHolds(EqualsProto(absl::Substitute(
          R"pb(
            tables {
              name: "Table"
              match_fields { name: "match" format: $0 type: EXACT }
              actions {
                name: "Action"
                parameters { name: "param" format: HEX_STRING bitwidth: 10 }
              }
            }
          )pb",
          pdpi::Format_Name(GetParam())))));
}

TEST_P(FormatTest, IgnoresBitwidthForNonHexStringActions) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(id: 1 alias: "Table")pb")
          .match_field(R"pb(id: 1 name: "match" match_type: EXACT)pb",
                       pdpi::Format::STRING)
          .entry_action(IrActionDefinitionBuilder()
                            .preamble(R"pb(alias: "Action")pb")
                            .param(R"pb(id: 1 name: "param" bitwidth: 10)pb",
                                   GetParam()))();
  pdpi::IrP4Info irp4info;
  (*irp4info.mutable_tables_by_id())[1] = table;
  (*irp4info.mutable_tables_by_name())["Table"] = table;

  EXPECT_THAT(ConvertToSchema(irp4info),
              IsOkAndHolds(EqualsProto(absl::Substitute(
                  R"pb(
                    tables {
                      name: "Table"
                      match_fields { name: "match" format: STRING type: EXACT }
                      actions {
                        name: "Action"
                        parameters { name: "param" format: $0 }
                      }
                    }
                  )pb",
                  pdpi::Format_Name(GetParam())))));
}

TEST_P(FormatTest, IgnoresBitwidthForNonHexStringMatchFields) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(id: 1 alias: "Table")pb")
          .match_field(
              R"pb(id: 1 name: "match" match_type: EXACT bitwidth: 1)pb",
              GetParam())
          .entry_action(
              IrActionDefinitionBuilder()
                  .preamble(R"pb(alias: "Action")pb")
                  .param(R"pb(id: 1 name: "param")pb", pdpi::Format::STRING))();
  pdpi::IrP4Info irp4info;
  (*irp4info.mutable_tables_by_id())[1] = table;
  (*irp4info.mutable_tables_by_name())["Table"] = table;

  EXPECT_THAT(ConvertToSchema(irp4info),
              IsOkAndHolds(EqualsProto(absl::Substitute(
                  R"pb(
                    tables {
                      name: "Table"
                      match_fields { name: "match" format: $0 type: EXACT }
                      actions {
                        name: "Action"
                        parameters { name: "param" format: STRING }
                      }
                    }
                  )pb",
                  pdpi::Format_Name(GetParam())))));
}

// Returns a list of all pdpi formats that do not require bitwidth.
const std::set<pdpi::Format>& NonBitwidthFormats() {
  static const auto* const kFormats =
      new std::set<pdpi::Format>({pdpi::Format::STRING, pdpi::Format::IPV4,
                                  pdpi::Format::IPV6, pdpi::Format::MAC});
  return *kFormats;
}

INSTANTIATE_TEST_SUITE_P(
    ConvertToSchemaTest, FormatTest, ValuesIn(NonBitwidthFormats()),
    [](const testing::TestParamInfo<FormatTest::ParamType>& info) {
      return pdpi::Format_Name(info.param);
    });

TEST(ConvertToSchemaTest, ConvertsTableWithNoParamAction) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(id: 1 alias: "Table")pb")
          .match_field(R"pb(id: 1 name: "match" match_type: OPTIONAL)pb",
                       pdpi::Format::STRING)
          .entry_action(IrActionDefinitionBuilder().preamble(
              R"pb(id: 1 alias: "Action")pb"))();
  pdpi::IrP4Info irp4info;
  (*irp4info.mutable_tables_by_id())[1] = table;
  (*irp4info.mutable_tables_by_name())["Table"] = table;

  EXPECT_THAT(ConvertToSchema(irp4info), IsOkAndHolds(EqualsProto(R"pb(
                tables {
                  name: "Table"
                  match_fields { name: "match" type: EXACT format: STRING }
                  actions { name: "Action" }
                }
              )pb")));
}

TEST(ConvertToSchemaTest, ConvertsTableWithMultipleMatchFields) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(id: 1 alias: "Table")pb")
          .match_field(R"pb(id: 1
                            name: "hex_string_match"
                            match_type: EXACT
                            bitwidth: 10)pb",
                       pdpi::Format::HEX_STRING)
          .match_field(R"pb(id: 2 name: "string_match" match_type: OPTIONAL)pb",
                       pdpi::Format::STRING)
          .match_field(R"pb(id: 3 name: "ipv4_match" match_type: LPM)pb",
                       pdpi::Format::IPV4)
          .match_field(R"pb(id: 4 name: "ipv6_match" match_type: LPM)pb",
                       pdpi::Format::IPV6)
          .match_field(R"pb(id: 5 name: "mac_match" match_type: TERNARY)pb",
                       pdpi::Format::MAC)
          .entry_action(
              IrActionDefinitionBuilder()
                  .preamble(R"pb(alias: "Action")pb")
                  .param(R"pb(id: 1 name: "param")pb", pdpi::Format::STRING))();
  pdpi::IrP4Info irp4info;
  (*irp4info.mutable_tables_by_id())[1] = table;
  (*irp4info.mutable_tables_by_name())["Table"] = table;

  EXPECT_THAT(
      ConvertToSchema(irp4info),
      IsOkAndHolds(EqualsProto(
          R"pb(
            tables {
              name: "Table"
              match_fields {
                name: "hex_string_match"
                format: HEX_STRING
                bitwidth: 10
                type: EXACT
              }
              match_fields { name: "string_match" format: STRING type: EXACT }
              match_fields { name: "ipv4_match" format: IPV4 type: LPM }
              match_fields { name: "ipv6_match" format: IPV6 type: LPM }
              match_fields { name: "mac_match" format: MAC type: TERNARY }
              actions {
                name: "Action"
                parameters { name: "param" format: STRING }
              }
            }
          )pb")));
}

TEST(ConvertToSchemaTest, ConvertsTableWithMultipleActionParameters) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(id: 1 alias: "Table")pb")
          .match_field(R"pb(id: 1 name: "string_match" match_type: OPTIONAL)pb",
                       pdpi::Format::STRING)
          .entry_action(
              IrActionDefinitionBuilder()
                  .preamble(R"pb(id: 1 alias: "Action")pb")
                  .param(R"pb(id: 1 name: "hex_string_param" bitwidth: 10)pb",
                         pdpi::Format::HEX_STRING)
                  .param(R"pb(id: 2 name: "string_param")pb",
                         pdpi::Format::STRING)
                  .param(R"pb(id: 3 name: "ipv4_param")pb", pdpi::Format::IPV4)
                  .param(R"pb(id: 4 name: "ipv6_param")pb", pdpi::Format::IPV6)
                  .param(R"pb(id: 5 name: "mac_param")pb",
                         pdpi::Format::MAC))();
  pdpi::IrP4Info irp4info;
  (*irp4info.mutable_tables_by_id())[1] = table;
  (*irp4info.mutable_tables_by_name())["Table"] = table;

  EXPECT_THAT(
      ConvertToSchema(irp4info),
      IsOkAndHolds(EqualsProto(
          R"pb(
            tables {
              name: "Table"
              match_fields { name: "string_match" format: STRING type: EXACT }
              actions {
                name: "Action"
                parameters {
                  name: "hex_string_param"
                  bitwidth: 10
                  format: HEX_STRING
                }
                parameters { name: "string_param" format: STRING }
                parameters { name: "ipv4_param" format: IPV4 }
                parameters { name: "ipv6_param" format: IPV6 }
                parameters { name: "mac_param" format: MAC }
              }
            }
          )pb")));
}

TEST(ConvertToSchemaTest, ConvertsTableWithMultipleActions) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(id: 1 alias: "Table")pb")
          .match_field(R"pb(id: 1 name: "string_match" match_type: OPTIONAL)pb",
                       pdpi::Format::STRING)
          .entry_action(
              IrActionDefinitionBuilder()
                  .preamble(R"pb(id: 1 alias: "String_Action")pb")
                  .param(R"pb(id: 1 name: "param")pb", pdpi::Format::STRING))
          .entry_action(
              IrActionDefinitionBuilder()
                  .preamble(R"pb(id: 2 alias: "IPV4_Action")pb")
                  .param(R"pb(id: 1 name: "param")pb", pdpi::Format::IPV4))
          .entry_action(
              IrActionDefinitionBuilder()
                  .preamble(R"pb(id: 3 alias: "IPV6_MAC_Action")pb")
                  .param(R"pb(id: 1 name: "ip_param")pb", pdpi::Format::IPV6)
                  .param(R"pb(id: 2 name: "mac_param")pb",
                         pdpi::Format::MAC))();
  pdpi::IrP4Info irp4info;
  (*irp4info.mutable_tables_by_id())[1] = table;
  (*irp4info.mutable_tables_by_name())["Table"] = table;

  EXPECT_THAT(
      ConvertToSchema(irp4info),
      IsOkAndHolds(EqualsProto(
          R"pb(
            tables {
              name: "Table"
              match_fields { name: "string_match" format: STRING type: EXACT }
              actions {
                name: "String_Action"
                parameters { name: "param" format: STRING }
              }
              actions {
                name: "IPV4_Action"
                parameters { name: "param" format: IPV4 }
              }
              actions {
                name: "IPV6_MAC_Action"
                parameters { name: "ip_param" format: IPV6 }
                parameters { name: "mac_param" format: MAC }
              }
            }
          )pb")));
}

TEST(ConvertToSchemaTest, ConvertsMultipleTables) {
  pdpi::IrTableDefinition table1 =
      IrTableDefinitionBuilder()
          .preamble(R"pb(id: 1 alias: "Table1")pb")
          .match_field(R"pb(id: 1 name: "string_match" match_type: OPTIONAL)pb",
                       pdpi::Format::STRING)
          .match_field(R"pb(id: 2 name: "ipv6_match" match_type: OPTIONAL)pb",
                       pdpi::Format::IPV6)
          .entry_action(
              IrActionDefinitionBuilder()
                  .preamble(R"pb(id: 1 alias: "Action1")pb")
                  .param(R"pb(id: 1 name: "param")pb", pdpi::Format::IPV6))
          .entry_action(
              IrActionDefinitionBuilder()
                  .preamble(R"pb(id: 2 alias: "Action2")pb")
                  .param(R"pb(id: 1 name: "param")pb", pdpi::Format::IPV6))();

  pdpi::IrTableDefinition table2 =
      IrTableDefinitionBuilder()
          .preamble(R"pb(id: 2 alias: "Table2")pb")
          .match_field(R"pb(id: 1 name: "ipv4_match" match_type: OPTIONAL)pb",
                       pdpi::Format::IPV4)
          .match_field(R"pb(id: 2 name: "ipv6_match" match_type: OPTIONAL)pb",
                       pdpi::Format::IPV6)
          .entry_action(
              IrActionDefinitionBuilder()
                  .preamble(R"pb(id: 1 alias: "Complex_action")pb")
                  .param(R"pb(id: 1 name: "param1")pb", pdpi::Format::STRING)
                  .param(R"pb(id: 2 name: "param2")pb", pdpi::Format::STRING)
                  .param(R"pb(id: 3 name: "param3")pb", pdpi::Format::IPV4))();

  pdpi::IrP4Info irp4info;
  (*irp4info.mutable_tables_by_id())[1] = table1;
  (*irp4info.mutable_tables_by_name())["Table1"] = table1;
  (*irp4info.mutable_tables_by_id())[2] = table2;
  (*irp4info.mutable_tables_by_name())["Table2"] = table2;

  EXPECT_THAT(
      ConvertToSchema(irp4info),
      IsOkAndHolds(EqualsProto(
          R"pb(
            tables {
              name: "Table1"
              match_fields { name: "string_match" format: STRING type: EXACT }
              match_fields { name: "ipv6_match" format: IPV6 type: EXACT }
              actions {
                name: "Action1"
                parameters { name: "param" format: IPV6 }
              }
              actions {
                name: "Action2"
                parameters { name: "param" format: IPV6 }
              }
            }
            tables {
              name: "Table2"
              match_fields { name: "ipv4_match" format: IPV4 type: EXACT }
              match_fields { name: "ipv6_match" format: IPV6 type: EXACT }
              actions {
                name: "Complex_action"
                parameters { name: "param1" format: STRING }
                parameters { name: "param2" format: STRING }
                parameters { name: "param3" format: IPV4 }
              }
            }
          )pb")));
}

TEST(ConvertToSchemaTest, FailsForTableWithNoMatchFields) {
  pdpi::IrTableDefinition table = IrTableDefinitionBuilder()
                                      .preamble(R"pb(id: 1 alias: "Table")pb")
                                      .entry_action(DefaultAction())();
  pdpi::IrP4Info irp4info;
  (*irp4info.mutable_tables_by_id())[1] = table;
  (*irp4info.mutable_tables_by_name())["Table"] = table;

  EXPECT_THAT(ConvertToSchema(irp4info).status(),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       HasSubstr("must contain at least one match field")));
}

TEST(ConvertToSchemaTest, FailsToConvertRangeMatch) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(id: 1 alias: "Table")pb")
          .match_field(R"pb(id: 1 name: "match" match_type: RANGE)pb",
                       pdpi::Format::IPV4)
          .entry_action(DefaultAction())();
  pdpi::IrP4Info irp4info;
  (*irp4info.mutable_tables_by_id())[1] = table;
  (*irp4info.mutable_tables_by_name())["Table"] = table;

  EXPECT_THAT(ConvertToSchema(irp4info).status(),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       MatchesRegex(".*Match type.*RANGE.*is unsupported.*")));
}

TEST(ConvertToSchemaTest, FailsToConvertUnspecifiedMatch) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(id: 1 alias: "Table")pb")
          .match_field(R"pb(id: 1 name: "match" match_type: UNSPECIFIED)pb",
                       pdpi::Format::IPV4)
          .entry_action(DefaultAction())();
  pdpi::IrP4Info irp4info;
  (*irp4info.mutable_tables_by_id())[1] = table;
  (*irp4info.mutable_tables_by_name())["Table"] = table;

  EXPECT_THAT(
      ConvertToSchema(irp4info).status(),
      StatusIs(absl::StatusCode::kInvalidArgument,
               MatchesRegex(".*Match type.*UNSPECIFIED.*is unsupported.*")));
}

TEST(ConvertToSchemaTest, FailsToConvertHexStringMatchWithoutBitwidth) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(id: 1 alias: "Table")pb")
          .match_field(R"pb(id: 1 name: "match" match_type: EXACT)pb",
                       pdpi::Format::HEX_STRING)
          .entry_action(DefaultAction())();
  pdpi::IrP4Info irp4info;
  (*irp4info.mutable_tables_by_id())[1] = table;
  (*irp4info.mutable_tables_by_name())["Table"] = table;

  EXPECT_THAT(ConvertToSchema(irp4info).status(),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       MatchesRegex(".*HEX_STRING.*match field.*bitwidth.*")));
}

TEST(ConvertToSchemaTest, FailsToConvertHexStringActionWithoutBitwidth) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(id: 1 alias: "Table")pb")
          .match_field(DefaultMatchField(), pdpi::Format::STRING)
          .entry_action(IrActionDefinitionBuilder()
                            .preamble(R"pb(id: 1 alias: "Action")pb")
                            .param(R"pb(id: 1 name: "param")pb",
                                   pdpi::Format::HEX_STRING))();
  pdpi::IrP4Info irp4info;
  (*irp4info.mutable_tables_by_id())[1] = table;
  (*irp4info.mutable_tables_by_name())["Table"] = table;

  EXPECT_THAT(ConvertToSchema(irp4info).status(),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       MatchesRegex(".*HEX_STRING.*parameters.*bitwidth.*")));
}

TEST(ConvertToSchemaTest, FailsToConvertFixedTableWithCounter) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(id: 1 alias: "Table")pb")
          .match_field(DefaultMatchField(), pdpi::Format::STRING)
          .entry_action(DefaultAction())();
  table.mutable_counter()->set_unit(p4::config::v1::CounterSpec::PACKETS);
  pdpi::IrP4Info irp4info;
  (*irp4info.mutable_tables_by_id())[1] = table;
  (*irp4info.mutable_tables_by_name())["Table"] = table;

  EXPECT_THAT(ConvertToSchema(irp4info).status(),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       HasSubstr("may not contain counters")));
}

TEST(ConvertToSchemaTest, FailsToConvertFixedTableWithMeter) {
  pdpi::IrTableDefinition table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(id: 1 alias: "Table")pb")
          .match_field(DefaultMatchField(), pdpi::Format::STRING)
          .entry_action(DefaultAction())();
  table.mutable_meter()->set_unit(p4::config::v1::MeterSpec::PACKETS);
  pdpi::IrP4Info irp4info;
  (*irp4info.mutable_tables_by_id())[1] = table;
  (*irp4info.mutable_tables_by_name())["Table"] = table;

  EXPECT_THAT(ConvertToSchema(irp4info).status(),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       HasSubstr("may not contain meters")));
}

TEST(SupportedSchemaTest, ReturnsASchema) {
  EXPECT_THAT(
      SupportedSchema(),
      IsOkAndHolds(Property(&P4InfoVerificationSchema::ByteSizeLong, Gt(0))));
}

pdpi::IrP4Info IrP4InfoFromSchema(const P4InfoVerificationSchema& schema) {
  IrP4InfoBuilder ir_p4info_builder;
  for (const auto& table : schema.tables()) {
    IrTableDefinitionBuilder table_builder;
    table_builder.name(table.name());
    for (const auto& match_field : table.match_fields()) {
      table_builder.match_field(
          absl::Substitute(R"pb(name: "$0" match_type: $1 bitwidth: $2)pb",
                           match_field.name(),
                           MatchSchema::MatchType_Name(match_field.type()),
                           match_field.bitwidth()),
          match_field.format());
    }
    for (const auto& action : table.actions()) {
      IrActionDefinitionBuilder action_builder;
      action_builder.name(action.name());
      for (const auto& param : action.parameters()) {
        action_builder.param(absl::Substitute(R"pb(name: "$0" bitwidth: $1)pb",
                                              param.name(), param.bitwidth()),
                             param.format());
      }
      table_builder.entry_action(action_builder);
    }
    ir_p4info_builder.table(table_builder);
  }
  return ir_p4info_builder();
}

TEST(IsSupportedBySchemaTest, ReturnsOkWithTableSubset) {
  const P4InfoVerificationSchema kSupportedSchema =
      gutil::ParseProtoOrDie<P4InfoVerificationSchema>(R"pb(
        tables {
          name: "Table1"
          match_fields { name: "match1" format: STRING type: EXACT }
        }
        tables {
          name: "Table2"
          match_fields { name: "match2" format: STRING type: EXACT }
        }
        tables {
          name: "Table3"
          match_fields { name: "match3" format: STRING type: EXACT }
        }
      )pb");
  auto schema = kSupportedSchema;
  schema.mutable_tables()->erase(schema.mutable_tables()->begin());
  pdpi::IrP4Info schema_p4info = IrP4InfoFromSchema(schema);
  EXPECT_OK(IsSupportedBySchema(schema_p4info, kSupportedSchema));
}

TEST(IsSupportedBySchemaTest, ReturnsOkWithMatchFieldSubset) {
  const P4InfoVerificationSchema kSupportedSchema =
      gutil::ParseProtoOrDie<P4InfoVerificationSchema>(R"pb(
        tables {
          name: "Table"
          match_fields { name: "match1" format: STRING type: EXACT }
          match_fields { name: "match2" format: STRING type: EXACT }
        }
      )pb");
  auto schema = kSupportedSchema;
  auto& match_fields = *schema.mutable_tables(0)->mutable_match_fields();
  match_fields.erase(match_fields.begin());
  pdpi::IrP4Info schema_p4info = IrP4InfoFromSchema(schema);
  EXPECT_OK(IsSupportedBySchema(schema_p4info, kSupportedSchema));
}

TEST(IsSupportedBySchemaTest, ReturnsOkWithActionSubset) {
  const P4InfoVerificationSchema kSupportedSchema =
      gutil::ParseProtoOrDie<P4InfoVerificationSchema>(R"pb(
        tables {
          name: "Table"
          match_fields { name: "match1" format: STRING type: EXACT }
          match_fields { name: "match2" format: STRING type: EXACT }
          actions { name: "action1" }
          actions { name: "action2" }
        }
      )pb");
  auto schema = kSupportedSchema;
  auto& actions = *schema.mutable_tables(0)->mutable_actions();
  actions.erase(actions.begin());
  pdpi::IrP4Info schema_p4info = IrP4InfoFromSchema(schema);
  EXPECT_OK(IsSupportedBySchema(schema_p4info, kSupportedSchema));
}

TEST(IsSupportedBySchemaTest, ReturnsErrorForUnknownTable) {
  const P4InfoVerificationSchema kSupportedSchema =
      gutil::ParseProtoOrDie<P4InfoVerificationSchema>(R"pb(
        tables {
          name: "Table1"
          match_fields { name: "match1" format: STRING type: EXACT }
          actions { name: "action1" }
        }
        tables {
          name: "Table2"
          match_fields { name: "match1" format: STRING type: EXACT }
          actions { name: "action2" }
        }
      )pb");
  auto schema = kSupportedSchema;
  schema.mutable_tables(1)->set_name("not_a_table");

  pdpi::IrP4Info schema_p4info = IrP4InfoFromSchema(schema);
  EXPECT_THAT(IsSupportedBySchema(schema_p4info, kSupportedSchema),
              StatusIs(absl::StatusCode::kNotFound, HasSubstr("not_a_table")));
}

TEST(IsSupportedBySchemaTest, ReturnsErrorForUnknownMatchField) {
  const P4InfoVerificationSchema kSupportedSchema =
      gutil::ParseProtoOrDie<P4InfoVerificationSchema>(R"pb(
        tables {
          name: "Table1"
          match_fields { name: "match1" format: STRING type: EXACT }
          actions { name: "action1" }
        }
      )pb");
  auto schema = kSupportedSchema;
  schema.mutable_tables(0)->mutable_match_fields(0)->set_name("not_a_field");
  pdpi::IrP4Info schema_p4info = IrP4InfoFromSchema(schema);
  EXPECT_THAT(IsSupportedBySchema(schema_p4info, kSupportedSchema),
              StatusIs(absl::StatusCode::kNotFound,
                       AllOf(HasSubstr("Table1"), HasSubstr("not_a_field"))));
}

TEST(IsSupportedBySchemaTest, ReturnsErrorForUnknownAction) {
  const P4InfoVerificationSchema kSupportedSchema =
      gutil::ParseProtoOrDie<P4InfoVerificationSchema>(R"pb(
        tables {
          name: "Table1"
          match_fields { name: "match1" format: STRING type: EXACT }
          actions { name: "action1" }
        }
      )pb");
  auto schema = kSupportedSchema;
  schema.mutable_tables(0)->mutable_actions(0)->set_name("not_an_action");
  pdpi::IrP4Info schema_p4info = IrP4InfoFromSchema(schema);
  EXPECT_THAT(IsSupportedBySchema(schema_p4info, kSupportedSchema),
              StatusIs(absl::StatusCode::kNotFound,
                       AllOf(HasSubstr("Table1"), HasSubstr("not_an_action"))));
}

TEST(IsSupportedBySchemaTest, ReturnsErrorForMatchFieldMatchTypeMismatch) {
  const P4InfoVerificationSchema kSupportedSchema =
      gutil::ParseProtoOrDie<P4InfoVerificationSchema>(R"pb(
        tables {
          name: "Table1"
          match_fields { name: "match1" format: STRING type: EXACT }
        }
      )pb");
  auto schema = kSupportedSchema;
  schema.mutable_tables(0)->mutable_match_fields(0)->set_type(MatchSchema::LPM);

  pdpi::IrP4Info schema_p4info = IrP4InfoFromSchema(schema);
  EXPECT_THAT(IsSupportedBySchema(schema_p4info, kSupportedSchema),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       AllOf(HasSubstr("Table1"), HasSubstr("match1"),
                             HasSubstr("match type"))));
}

TEST(IsSupportedBySchemaTest, ReturnsErrorForMatchFieldFormatMismatch) {
  const P4InfoVerificationSchema kSupportedSchema =
      gutil::ParseProtoOrDie<P4InfoVerificationSchema>(R"pb(
        tables {
          name: "Table1"
          match_fields { name: "match1" format: STRING type: EXACT }
        }
      )pb");
  auto schema = kSupportedSchema;
  schema.mutable_tables(0)->mutable_match_fields(0)->set_format(
      pdpi::Format::IPV4);

  pdpi::IrP4Info schema_p4info = IrP4InfoFromSchema(schema);
  EXPECT_THAT(IsSupportedBySchema(schema_p4info, kSupportedSchema),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       AllOf(HasSubstr("Table1"), HasSubstr("match1"),
                             HasSubstr("format"))));
}

TEST(IsSupportedBySchemaTest, ReturnsErrorForMatchFieldBitwidthMismatch) {
  pdpi::IrP4Info ir_p4info =
      IrP4InfoBuilder().table(IrTableDefinitionBuilder()
                                  .name("TableName")
                                  .match_field(R"pb(id: 1
                                                    name: "MatchName"
                                                    match_type: EXACT
                                                    bitwidth: 10)pb",
                                               pdpi::Format::HEX_STRING)
                                  .entry_action(DefaultAction()))();
  ASSERT_OK_AND_ASSIGN(P4InfoVerificationSchema schema,
                       ConvertToSchema(ir_p4info));
  schema.mutable_tables(0)->mutable_match_fields(0)->set_bitwidth(9);

  EXPECT_THAT(IsSupportedBySchema(ir_p4info, schema),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       AllOf(HasSubstr("TableName"), HasSubstr("MatchName"),
                             HasSubstr("bitwidth"))));
}

TEST(IsSupportedBySchemaTest, ReturnsErrorForUnknownActionParameter) {
  pdpi::IrP4Info ir_p4info = IrP4InfoBuilder().table(
      IrTableDefinitionBuilder()
          .name("TableName")
          .match_field(DefaultMatchField(), pdpi::Format::STRING)
          .entry_action(IrActionDefinitionBuilder()
                            .name("ActionName")
                            .param(R"pb(id: 1 name: "ParamName")pb",
                                   pdpi::Format::STRING)))();
  ASSERT_OK_AND_ASSIGN(P4InfoVerificationSchema schema,
                       ConvertToSchema(ir_p4info));
  schema.mutable_tables(0)->mutable_actions(0)->mutable_parameters(0)->set_name(
      "SchemaName");
  EXPECT_THAT(IsSupportedBySchema(ir_p4info, schema),
              StatusIs(absl::StatusCode::kNotFound,
                       AllOf(HasSubstr("TableName"), HasSubstr("ActionName"),
                             HasSubstr("ParamName"))));
}

TEST(IsSupportedBySchemaTest, ReturnsErrorForUnexpectedActionParameter) {
  pdpi::IrP4Info ir_p4info = IrP4InfoBuilder().table(
      IrTableDefinitionBuilder()
          .name("TableName")
          .match_field(DefaultMatchField(), pdpi::Format::STRING)
          .entry_action(IrActionDefinitionBuilder()
                            .name("ActionName")
                            .param(R"pb(id: 1 name: "ParamName")pb",
                                   pdpi::Format::IPV4)))();
  ASSERT_OK_AND_ASSIGN(P4InfoVerificationSchema schema,
                       ConvertToSchema(ir_p4info));
  schema.mutable_tables(0)->mutable_actions(0)->clear_parameters();
  EXPECT_THAT(IsSupportedBySchema(ir_p4info, schema),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       AllOf(HasSubstr("TableName"), HasSubstr("ActionName"),
                             HasSubstr("parameter"))));
}

TEST(IsSupportedBySchemaTest, ReturnsErrorForExtraActionParameter) {
  pdpi::IrP4Info ir_p4info = IrP4InfoBuilder().table(
      IrTableDefinitionBuilder()
          .name("TableName")
          .match_field(DefaultMatchField(), pdpi::Format::STRING)
          .entry_action(
              IrActionDefinitionBuilder()
                  .name("ActionName")
                  .param(R"pb(id: 1 name: "ParamName")pb", pdpi::Format::IPV4)
                  .param(R"pb(id: 2 name: "SecondParamName")pb",
                         pdpi::Format::IPV4)))();
  ASSERT_OK_AND_ASSIGN(P4InfoVerificationSchema schema,
                       ConvertToSchema(ir_p4info));
  auto& parameters =
      *schema.mutable_tables(0)->mutable_actions(0)->mutable_parameters();
  parameters.erase(parameters.begin());
  EXPECT_THAT(IsSupportedBySchema(ir_p4info, schema),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       AllOf(HasSubstr("TableName"), HasSubstr("ActionName"),
                             HasSubstr("parameter"))));
}

TEST(IsSupportedBySchemaTest, ReturnsErrorForActionParameterFormatMismatch) {
  pdpi::IrP4Info ir_p4info = IrP4InfoBuilder().table(
      IrTableDefinitionBuilder()
          .name("TableName")
          .match_field(DefaultMatchField(), pdpi::Format::STRING)
          .entry_action(IrActionDefinitionBuilder()
                            .name("ActionName")
                            .param(R"pb(id: 1 name: "ParamName")pb",
                                   pdpi::Format::IPV4)))();
  ASSERT_OK_AND_ASSIGN(P4InfoVerificationSchema schema,
                       ConvertToSchema(ir_p4info));
  schema.mutable_tables(0)
      ->mutable_actions(0)
      ->mutable_parameters(0)
      ->set_format(pdpi::Format::IPV6);
  EXPECT_THAT(IsSupportedBySchema(ir_p4info, schema),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       AllOf(HasSubstr("TableName"), HasSubstr("ActionName"),
                             HasSubstr("ParamName"), HasSubstr("format"))));
}

TEST(IsSupportedBySchemaTest, ReturnsErrorForActionParameterBitwidthMismatch) {
  pdpi::IrP4Info ir_p4info = IrP4InfoBuilder().table(
      IrTableDefinitionBuilder()
          .name("TableName")
          .match_field(DefaultMatchField(), pdpi::Format::STRING)
          .entry_action(IrActionDefinitionBuilder()
                            .name("ActionName")
                            .param(R"pb(id: 1 name: "ParamName" bitwidth: 9)pb",
                                   pdpi::Format::HEX_STRING)))();
  ASSERT_OK_AND_ASSIGN(P4InfoVerificationSchema schema,
                       ConvertToSchema(ir_p4info));
  schema.mutable_tables(0)
      ->mutable_actions(0)
      ->mutable_parameters(0)
      ->set_bitwidth(8);
  EXPECT_THAT(IsSupportedBySchema(ir_p4info, schema),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       AllOf(HasSubstr("TableName"), HasSubstr("ActionName"),
                             HasSubstr("ParamName"), HasSubstr("bitwidth"))));
}

TEST(IsSupportedBySchemaTest, AcceptsSmallerActionParameterBitwidth) {
  pdpi::IrP4Info ir_p4info = IrP4InfoBuilder().table(
      IrTableDefinitionBuilder()
          .name("TableName")
          .match_field(DefaultMatchField(), pdpi::Format::STRING)
          .entry_action(IrActionDefinitionBuilder()
                            .name("ActionName")
                            .param(R"pb(id: 1 name: "ParamName" bitwidth: 7)pb",
                                   pdpi::Format::HEX_STRING)))();
  ASSERT_OK_AND_ASSIGN(P4InfoVerificationSchema schema,
                       ConvertToSchema(ir_p4info));
  schema.mutable_tables(0)
      ->mutable_actions(0)
      ->mutable_parameters(0)
      ->set_bitwidth(8);
  EXPECT_OK(IsSupportedBySchema(ir_p4info, schema));
}

TEST(IsSupportedBySchemaTest, AcceptsSmallerMatchFieldBitwidth) {
  pdpi::IrP4Info ir_p4info = IrP4InfoBuilder().table(
      IrTableDefinitionBuilder()
          .name("TableName")
          .match_field(R"pb(id: 1 name: "Match" bitwidth: 7 match_type: LPM)pb",
                       pdpi::Format::HEX_STRING)
          .entry_action(DefaultAction()))();
  ASSERT_OK_AND_ASSIGN(P4InfoVerificationSchema schema,
                       ConvertToSchema(ir_p4info));
  schema.mutable_tables(0)->mutable_match_fields(0)->set_bitwidth(8);
  EXPECT_OK(IsSupportedBySchema(ir_p4info, schema));
}

class GoogleInstantiationTest
    : public ::testing::TestWithParam<sai::Instantiation> {};

// Tests that P4RT app is always "ahead of" our SAI P4 programs, so we don't
// accidentally expose features in the program that are not yet supported by
// P4RT app/PINS.
TEST_P(GoogleInstantiationTest, SchemaSupportsInstantiation) {
  sai::Instantiation instantiation = GetParam();
  pdpi::IrP4Info p4info = sai::GetIrP4Info(instantiation);
  ASSERT_OK_AND_ASSIGN(P4InfoVerificationSchema schema, SupportedSchema());
  // Not supporting entities that are explicitly marked as `@unsupported` is ok.
  pdpi::RemoveUnsupportedEntities(p4info);
  EXPECT_OK(IsSupportedBySchema(p4info, schema));
}

INSTANTIATE_TEST_SUITE_P(
    IsSupportedBySchemaTest, GoogleInstantiationTest,
    ValuesIn(sai::AllSaiInstantiations()),
    [](const testing::TestParamInfo<sai::Instantiation>& info) {
      return sai::InstantiationToString(info.param);
    });

}  // namespace
}  // namespace p4rt_app
