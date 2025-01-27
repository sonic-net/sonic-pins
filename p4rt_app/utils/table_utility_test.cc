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

#include "absl/status/status.h"
#include "gmock/gmock.h"
#include "google/protobuf/map.h"
#include "google/protobuf/text_format.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status_matchers.h"
#include "p4_infra/p4_pdpi/ir.pb.h"

namespace p4rt_app {
namespace {

using ::gutil::EqualsProto;
using ::testing::ElementsAre;

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

class TypeTest : public testing::TestWithParam<table::Type> {};

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
  ASSERT_OK_AND_ASSIGN(pdpi::IrTableDefinition table_size_5,
                       gutil::ParseTextProto<pdpi::IrTableDefinition>(R"pb(
                         match_fields_by_name {
                           key: "a"
                           value { match_field { bitwidth: 5 } }
                         }
                       )pb"));
  ASSERT_OK_AND_ASSIGN(pdpi::IrTableDefinition table_size_10,
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
  ASSERT_OK_AND_ASSIGN(pdpi::IrTableDefinition table_size_15,
                       gutil::ParseTextProto<pdpi::IrTableDefinition>(R"pb(
                         match_fields_by_name {
                           key: "d"
                           value { match_field { bitwidth: 15 } }
                         }
                       )pb"));

  google::protobuf::Map<std::string, pdpi::IrTableDefinition> tables_by_name;
  tables_by_name["table_size_10"] = table_size_10;
  tables_by_name["table_size_5"] = table_size_5;
  tables_by_name["table_size_15"] = table_size_15;

  EXPECT_THAT(
      OrderTablesBySize(tables_by_name),
      ElementsAre(EqualsProto(table_size_15), EqualsProto(table_size_10),
                  EqualsProto(table_size_5)));
}

TEST(OrderTablesBySize, OrdersTablesByNameToBreakTies) {
  ASSERT_OK_AND_ASSIGN(pdpi::IrTableDefinition table0,
                       gutil::ParseTextProto<pdpi::IrTableDefinition>(R"pb(
                         match_fields_by_name {
                           key: "a"
                           value { match_field { bitwidth: 5 } }
                         }
                       )pb"));
  ASSERT_OK_AND_ASSIGN(pdpi::IrTableDefinition table1,
                       gutil::ParseTextProto<pdpi::IrTableDefinition>(R"pb(
                         match_fields_by_name {
                           key: "b"
                           value { match_field { bitwidth: 5 } }
                         }
                       )pb"));
  ASSERT_OK_AND_ASSIGN(pdpi::IrTableDefinition table2,
                       gutil::ParseTextProto<pdpi::IrTableDefinition>(R"pb(
                         match_fields_by_name {
                           key: "d"
                           value { match_field { bitwidth: 6 } }
                         }
                       )pb"));

  google::protobuf::Map<std::string, pdpi::IrTableDefinition> tables_by_name;
  tables_by_name["a"] = table0;
  tables_by_name["b"] = table1;
  tables_by_name["c"] = table2;

  // Note that `table2` has a larger size so it will be first. Then table 1
  // because its name is larger than table0.
  EXPECT_THAT(OrderTablesBySize(tables_by_name),
              ElementsAre(EqualsProto(table2), EqualsProto(table1),
                          EqualsProto(table0)));
}

}  // namespace
}  // namespace p4rt_app
