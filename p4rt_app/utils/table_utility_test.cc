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

#include "glog/logging.h"
#include "gmock/gmock.h"
#include "google/protobuf/text_format.h"
#include "gtest/gtest.h"
#include "p4_pdpi/ir.pb.h"

namespace p4rt_app {
namespace {

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

}  // namespace
}  // namespace p4rt_app
