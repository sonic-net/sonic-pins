// Copyright 2021 Google LLC
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
#include "p4rt_app/utils/table_utility.h"

#include <string>
#include <vector>

#include "absl/status/status.h"
#include "gmock/gmock.h"
#include "google/protobuf/map.h"
#include "google/protobuf/text_format.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status_matchers.h"  // NOLINT
#include "p4_pdpi/ir.pb.h"
#include "sai_p4/instantiations/google/sai_p4info.h"

namespace p4rt_app {
namespace {

using ::gutil::EqualsProto;
using ::testing::Contains;
using ::testing::ElementsAre;
using ::testing::HasSubstr;
using ::testing::Matches;
using ::testing::TestWithParam;
using ::testing::ValuesIn;

TEST(GetTableType, ReturnsAclForSaiAclAnnotation) {
  pdpi::IrTableDefinition ir_table;
  google::protobuf::TextFormat::ParseFromString(
      R"pb(preamble { annotations: "@sai_acl(INGRESS)" })pb", &ir_table);

  auto get_table_type_result = GetTableType(ir_table);
  ASSERT_TRUE(get_table_type_result.ok())
      << "Actual status is " << get_table_type_result.status();
  EXPECT_EQ(get_table_type_result.value(), table::Type::kAcl);
}

TEST(GetTableType, ReturnsFixedForNoAnnotation) {
  pdpi::IrTableDefinition ir_table;
  google::protobuf::TextFormat::ParseFromString(
        R"pb(preamble { alias: "router_interface_table"})pb", &ir_table);
  auto get_table_type_result = GetTableType(ir_table);

  ASSERT_TRUE(get_table_type_result.ok())
      << "Actual status is " << get_table_type_result.status();
  EXPECT_EQ(get_table_type_result.value(), table::Type::kFixed);
}

TEST(GetTableType, ReturnsFixedForNoSpecialAnnotation) {
  pdpi::IrTableDefinition ir_table;
  google::protobuf::TextFormat::ParseFromString(
      R"pb(preamble { alias: "router_interface_table" annotations: "@random()" })pb", &ir_table);

  auto get_table_type_result = GetTableType(ir_table);
  ASSERT_TRUE(get_table_type_result.ok())
      << "Actual status is " << get_table_type_result.status();
  EXPECT_EQ(get_table_type_result.value(), table::Type::kFixed);
}

TEST(GetTableType, ReturnsExtForNoAnnotation) {
  pdpi::IrTableDefinition ir_table;
  google::protobuf::TextFormat::ParseFromString(
      R"pb(preamble { id: 0x03000001 })pb", &ir_table);

  auto get_table_type_result = GetTableType(ir_table);

  ASSERT_TRUE(get_table_type_result.ok())
      << "Actual status is " << get_table_type_result.status();
  EXPECT_EQ(get_table_type_result.value(), table::Type::kExt);
}

TEST(GetTableType, ReturnsErrorForAnnotationParseFailure) {
  pdpi::IrTableDefinition ir_table;
  google::protobuf::TextFormat::ParseFromString(
      R"pb(preamble { annotations: "@sai_acl()" annotations: "@sai_acl()" })pb",
      &ir_table);

  auto get_table_type_result = GetTableType(ir_table);
  EXPECT_EQ(get_table_type_result.status().code(),
            absl::StatusCode::kInvalidArgument)
      << "Actual status is " << get_table_type_result.status();
}

TEST(TableParse, ReturnsErrorForUnknownString) {
  auto parse_result = table::TypeParse("random_string");
  EXPECT_EQ(parse_result.status().code(), absl::StatusCode::kInvalidArgument)
      << "Actual status: " << parse_result.status();
}

class TypeTest : public TestWithParam<table::Type> {};

TEST_P(TypeTest, TypeNameMatchesTypeParse) {
  std::string type_name = table::TypeName(GetParam());
  auto parse_result = table::TypeParse(type_name);
  ASSERT_TRUE(parse_result.ok()) << "Actual status: " << parse_result.status();
  EXPECT_EQ(parse_result.value(), GetParam());
}

INSTANTIATE_TEST_SUITE_P(
    Type, TypeTest,
    testing::Values(table::Type::kAcl, table::Type::kFixed,
                    table::Type::kAclDefinition),
    [](const testing::TestParamInfo<TypeTest::ParamType>& info) {
      return table::TypeName(info.param);
    });

TEST(OrderTablesBySize, OrdersTablesBySize) {
  google::protobuf::Map<std::string, pdpi::IrTableDefinition> tables_by_name;
  ASSERT_OK_AND_ASSIGN(tables_by_name["table_size_5"],
                       gutil::ParseTextProto<pdpi::IrTableDefinition>(R"pb(
                         match_fields_by_name {
                           key: "a"
                           value { match_field { bitwidth: 5 } }
                         }
                       )pb"));
  ASSERT_OK_AND_ASSIGN(tables_by_name["table_size_10"],
                       gutil::ParseTextProto<pdpi::IrTableDefinition>(R"pb(
                         match_fields_by_name {
                           key: "b"
                           value { match_field { bitwidth: 3 } }
                         }
                         match_fields_by_name {
                           key: "c"
                           value { match_field { bitwidth: 7 } }
                         }
                       )pb"));
  ASSERT_OK_AND_ASSIGN(tables_by_name["table_size_15"],
                       gutil::ParseTextProto<pdpi::IrTableDefinition>(R"pb(
                         match_fields_by_name {
                           key: "d"
                           value { match_field { bitwidth: 15 } }
                         }
                       )pb"));

  EXPECT_THAT(OrderTablesBySize(tables_by_name),
              ElementsAre(&tables_by_name["table_size_15"],
                          &tables_by_name["table_size_10"],
                          &tables_by_name["table_size_5"]));
}

TEST(OrderTablesBySize, OrdersTablesByNameToBreakTies) {
  google::protobuf::Map<std::string, pdpi::IrTableDefinition> tables_by_name;
  ASSERT_OK_AND_ASSIGN(tables_by_name["a"],
                       gutil::ParseTextProto<pdpi::IrTableDefinition>(R"pb(
                         preamble { alias: "a" }
                         match_fields_by_name {
                           key: "a"
                           value { match_field { bitwidth: 5 } }
                         }
                       )pb"));
  ASSERT_OK_AND_ASSIGN(tables_by_name["b"],
                       gutil::ParseTextProto<pdpi::IrTableDefinition>(R"pb(
                         preamble { alias: "b" }
                         match_fields_by_name {
                           key: "b"
                           value { match_field { bitwidth: 5 } }
                         }
                       )pb"));
  ASSERT_OK_AND_ASSIGN(tables_by_name["c"],
                       gutil::ParseTextProto<pdpi::IrTableDefinition>(R"pb(
                         preamble { alias: "d" }
                         match_fields_by_name {
                           key: "d"
                           value { match_field { bitwidth: 6 } }
                         }
                       )pb"));

  // Note that table `c` has a larger size so it will be first. Then table `b`
  // because its name is larger than table `a`.
  EXPECT_THAT(OrderTablesBySize(tables_by_name),
              ElementsAre(&tables_by_name["c"], &tables_by_name["b"],
                          &tables_by_name["a"]));
}

std::vector<std::string> AllTableNames() {
  std::vector<std::string> table_names;
  table_names.reserve(sai::GetUnionedIrP4Info().tables_by_name().size());
  for (const auto& [table_name, _] :
       sai::GetUnionedIrP4Info().tables_by_name()) {
    table_names.push_back(table_name);
  }
  return table_names;
}

class PerTableTest : public TestWithParam<std::string /*table_name*/> {};

TEST_P(PerTableTest, CreatesANewTable) {
  const pdpi::IrP4Info& kBaseP4Info = sai::GetUnionedIrP4Info();
  std::string table_name = GetParam();
  const pdpi::IrTableDefinition& table_def =
      kBaseP4Info.tables_by_name().at(table_name);

  pdpi::IrP4Info ir_p4info = kBaseP4Info;
  ASSERT_OK_AND_ASSIGN(std::string dup_table_name,
                       DuplicateTable(ir_p4info, table_name));
  ASSERT_THAT(dup_table_name, HasSubstr(table_name));
  ASSERT_NE(dup_table_name, table_name);
  ASSERT_FALSE(kBaseP4Info.tables_by_name().contains(dup_table_name));
  ASSERT_TRUE(ir_p4info.tables_by_name().contains(dup_table_name));
  auto dup_table_def = ir_p4info.tables_by_name().at(dup_table_name);

  int dup_table_id = dup_table_def.preamble().id();
  ASSERT_NE(dup_table_id, table_def.preamble().id());
  ASSERT_TRUE(ir_p4info.tables_by_id().contains(dup_table_id));
  ASSERT_FALSE(kBaseP4Info.tables_by_id().contains(dup_table_id));

  ASSERT_THAT(ir_p4info.tables_by_id().at(dup_table_id),
              EqualsProto(ir_p4info.tables_by_name().at(dup_table_name)));
}

TEST_P(PerTableTest, NewTableEqualsOriginalTable) {
  const pdpi::IrP4Info& kBaseP4Info = sai::GetUnionedIrP4Info();
  std::string table_name = GetParam();

  pdpi::IrP4Info ir_p4info = kBaseP4Info;
  ASSERT_OK_AND_ASSIGN(std::string dup_table_name,
                       DuplicateTable(ir_p4info, table_name));
  pdpi::IrTableDefinition table = ir_p4info.tables_by_name().at(table_name);
  pdpi::IrTableDefinition dup_table =
      ir_p4info.tables_by_name().at(dup_table_name);

  EXPECT_THAT(dup_table.preamble().alias(),
              HasSubstr(table.preamble().alias()));
  EXPECT_THAT(dup_table.preamble().name(), HasSubstr(table.preamble().name()));
  EXPECT_NE(dup_table.preamble().id(), table.preamble().id());

  table.mutable_preamble()->set_alias(dup_table.preamble().alias());
  table.mutable_preamble()->set_name(dup_table.preamble().name());
  table.mutable_preamble()->set_id(dup_table.preamble().id());

  EXPECT_THAT(dup_table, EqualsProto(table));
}

TEST_P(PerTableTest, UpdatesActionTableReferences) {
  const pdpi::IrP4Info& kBaseP4Info = sai::GetUnionedIrP4Info();
  std::string table_name = GetParam();
  const pdpi::IrTableDefinition& table_def =
      kBaseP4Info.tables_by_name().at(table_name);

  pdpi::IrP4Info ir_p4info = kBaseP4Info;
  ASSERT_OK_AND_ASSIGN(std::string dup_table_name,
                       DuplicateTable(ir_p4info, table_name));
  int table_id = table_def.preamble().id();
  int dup_table_id =
      ir_p4info.tables_by_name().at(dup_table_name).preamble().id();

  for (const auto& [action_name, action_profile] :
       ir_p4info.action_profiles_by_name()) {
    EXPECT_EQ(Matches(Contains(table_id))(
                  action_profile.action_profile().table_ids()),
              Matches(Contains(dup_table_id))(
                  action_profile.action_profile().table_ids()));
  }

  for (const auto& [action_id, action_profile] :
       ir_p4info.action_profiles_by_id()) {
    EXPECT_EQ(Matches(Contains(table_id))(
                  action_profile.action_profile().table_ids()),
              Matches(Contains(dup_table_id))(
                  action_profile.action_profile().table_ids()));
  }
}

TEST_P(PerTableTest, DoesNotTouchTheRestOfTheIrP4Info) {
  const pdpi::IrP4Info& kBaseP4Info = sai::GetUnionedIrP4Info();
  std::string table_name = GetParam();

  pdpi::IrP4Info ir_p4info = kBaseP4Info;
  ASSERT_OK_AND_ASSIGN(std::string dup_table_name,
                       DuplicateTable(ir_p4info, table_name));
  int dup_table_id =
      ir_p4info.tables_by_name().at(dup_table_name).preamble().id();
  ir_p4info.mutable_tables_by_name()->erase(dup_table_name);
  ir_p4info.mutable_tables_by_id()->erase(dup_table_id);

  for (auto& [_, action_profile] :
       *ir_p4info.mutable_action_profiles_by_name()) {
    auto& table_ids =
        *action_profile.mutable_action_profile()->mutable_table_ids();
    for (auto iter = table_ids.begin(); iter != table_ids.end(); ++iter) {
      if (*iter == dup_table_id) {
        table_ids.erase(iter);
        break;
      }
    }
  }

  for (auto& [_, action_profile] : *ir_p4info.mutable_action_profiles_by_id()) {
    auto& table_ids =
        *action_profile.mutable_action_profile()->mutable_table_ids();
    for (auto iter = table_ids.begin(); iter != table_ids.end(); ++iter) {
      if (*iter == dup_table_id) {
        table_ids.erase(iter);
        break;
      }
    }
  }

  EXPECT_THAT(ir_p4info, EqualsProto(kBaseP4Info));
}

INSTANTIATE_TEST_SUITE_P(DuplicateTable, PerTableTest,
                         ValuesIn(AllTableNames()),
                         [](const testing::TestParamInfo<std::string>& info) {
                           return info.param;
                         });

}  // namespace
}  // namespace p4rt_app
