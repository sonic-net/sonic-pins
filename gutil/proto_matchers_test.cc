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
#include "proto_matchers.h"

#include <utility>
#include <vector>

#include "absl/strings/str_replace.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/proto_test.pb.h"
#include "gutil/testing.h"
#include "p4_pdpi/ir.pb.h"

namespace gutil {
namespace {

using ::testing::Not;

TEST(ProtoMatcher, EqualsProto) {
  pdpi::IrTableEntry table_entry;
  table_entry.set_table_name("router_interface_table");
  table_entry.set_priority(123);

  EXPECT_THAT(table_entry, EqualsProto(table_entry));
}

TEST(ProtoMatcher, EqualsProtoFromText) {
  pdpi::IrTableEntry table_entry;
  table_entry.set_table_name("router_interface_table");
  table_entry.set_priority(123);

  EXPECT_THAT(table_entry, EqualsProto(R"pb(
                table_name: "router_interface_table"
                priority: 123)pb"));
}

TEST(ProtoMatcher, DescribeEqualsProto) {
  auto matcher = EqualsProto(gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
    table_name: "router_interface_table"
    priority: 123
  )pb"));

  EXPECT_EQ(testing::DescribeMatcher<pdpi::IrTableEntry>(matcher),
            R"(is equal to pdpi.IrTableEntry <
table_name: "router_interface_table"
priority: 123
>)");
  EXPECT_EQ(testing::DescribeMatcher<pdpi::IrTableEntry>(Not(matcher)),
            R"(is not equal to pdpi.IrTableEntry <
table_name: "router_interface_table"
priority: 123
>)");
}

TEST(ProtoMatcher, DescribeEqualsProtoFromText) {
  std::string text =
      R"pb(table_name: "router_interface_table" priority: 123)pb";
  auto matcher = EqualsProto(text);

  EXPECT_EQ(testing::DescribeMatcher<pdpi::IrTableEntry>(matcher),
            R"(is equal to <
table_name: "router_interface_table" priority: 123>)");
  EXPECT_EQ(testing::DescribeMatcher<pdpi::IrTableEntry>(Not(matcher)),
            R"(is not equal to <
table_name: "router_interface_table" priority: 123>)");
}

TEST(BinaryEqualsProtoTest, EqualPairWorks) {
  auto arbitrary_proto_1 = ParseProtoOrDie<TestMessage>("int_field: 24");
  EXPECT_THAT(std::make_pair(arbitrary_proto_1, arbitrary_proto_1),
              EqualsProto());

  auto arbitrary_proto_2 = ParseProtoOrDie<TestMessage>("string_field: \"hi\"");
  EXPECT_THAT(std::make_pair(arbitrary_proto_2, arbitrary_proto_2),
              EqualsProto());
}

TEST(BinaryEqualsProtoTest, UnequalPairWorks) {
  auto arbitrary_proto_1 = ParseProtoOrDie<TestMessage>("int_field: 24");
  auto arbitrary_proto_2 = ParseProtoOrDie<TestMessage>("string_field: \"hi\"");
  EXPECT_THAT(std::make_pair(arbitrary_proto_1, arbitrary_proto_2),
              Not(EqualsProto()));
  EXPECT_THAT(std::make_pair(arbitrary_proto_2, arbitrary_proto_1),
              Not(EqualsProto()));
}

TEST(BinaryEqualsProtoTest, WorksWithPointwiseMatcher) {
  std::vector<TestMessage> protos = {
      ParseProtoOrDie<TestMessage>("int_field: 24"),
      ParseProtoOrDie<TestMessage>("string_field: \"hi\""),
  };
  EXPECT_THAT(protos, testing::Pointwise(EqualsProto(), protos));
}

TEST(BinaryEqualsProtoTest, DescribeBinaryEqualsProto) {
  auto matcher = EqualsProto();
  EXPECT_EQ(
      (testing::DescribeMatcher<std::pair<TestMessage, TestMessage>>(matcher)),
      "is a pair of equal protobufs");
}

TEST(EqualsProtoSequenceTest, EqualSequencesWork) {
  std::vector<TestMessage> protos = {
      ParseProtoOrDie<TestMessage>("int_field: 24"),
      ParseProtoOrDie<TestMessage>("string_field: \"hi\""),
  };
  EXPECT_THAT(protos, EqualsProtoSequence(protos));
}

TEST(EqualsProtoSequenceTest, UnequalSequencesWork) {
  std::vector<TestMessage> protos1 = {
      ParseProtoOrDie<TestMessage>("int_field: 24"),
      ParseProtoOrDie<TestMessage>("string_field: \"hi\""),
  };
  std::vector<TestMessage> protos2 = {
      ParseProtoOrDie<TestMessage>("int_field: 42"),
  };
  EXPECT_THAT(protos1, Not(EqualsProtoSequence(protos2)));
}

TEST(PartiallyMatcherTest, IdenticalProtosAreAlsoPartiallyEqual) {
  pdpi::IrTableEntry table_entry;
  table_entry.set_table_name("router_interface_table");
  table_entry.set_priority(123);

  EXPECT_THAT(table_entry, Partially(EqualsProto(table_entry)));
}

TEST(PartiallyMatcherTest, PartiallyEqualsProtoOnlyComparePresentFields) {
  pdpi::IrTableEntry table_entry;
  table_entry.set_table_name("router_interface_table");
  table_entry.set_priority(123);

  EXPECT_THAT(table_entry, Partially(EqualsProto(R"pb(
                table_name: "router_interface_table"
                priority: 123)pb")));
}

TEST(PartiallyMatcherTest, DifferentlProtosDoNotMatch) {
  pdpi::IrTableEntry table_entry;
  table_entry.set_table_name("router_interface_table");
  table_entry.set_priority(123);

  // Proto differs in one field and remains the same for another field does not
  // match.
  EXPECT_THAT(table_entry, Not(Partially(EqualsProto(R"pb(
                table_name: "big_table"
                priority: 123)pb"))));
  // Proto differs in both fields should not match.
  EXPECT_THAT(table_entry, Not(Partially(EqualsProto(R"pb(
                table_name: "big_table"
                priority: 1234)pb"))));
}

TEST(HasOneofCaseTest, NotHasOneofCase) {
  EXPECT_THAT(gutil::ParseProtoOrDie<TestMessageWithOneof>(R"pb()pb"),
              Not(HasOneofCase<TestMessageWithOneof>(
                  "foo", TestMessageWithOneof::kStringFoo)));
  EXPECT_THAT(gutil::ParseProtoOrDie<TestMessageWithOneof>(R"pb(
                int_foo: 42
              )pb"),
              Not(HasOneofCase<TestMessageWithOneof>(
                  "foo", TestMessageWithOneof::kStringFoo)));
  EXPECT_THAT(gutil::ParseProtoOrDie<TestMessageWithOneof>(R"pb(
                int_foo: 42
              )pb"),
              Not(HasOneofCase<TestMessageWithOneof>(
                  "foo", TestMessageWithOneof::kBoolFoo)));
}

TEST(HasOneofCaseTest, DoesHaveOneofCase) {
  EXPECT_THAT(gutil::ParseProtoOrDie<TestMessageWithOneof>(R"pb(
                string_foo: "hi"
              )pb"),
              HasOneofCase<TestMessageWithOneof>(
                  "foo", TestMessageWithOneof::kStringFoo));
  EXPECT_THAT(
      gutil::ParseProtoOrDie<TestMessageWithOneof>(R"pb(
        int_foo: 42
      )pb"),
      HasOneofCase<TestMessageWithOneof>("foo", TestMessageWithOneof::kIntFoo));
  EXPECT_THAT(gutil::ParseProtoOrDie<TestMessageWithOneof>(R"pb(
                bool_foo: false
              )pb"),
              HasOneofCase<TestMessageWithOneof>(
                  "foo", TestMessageWithOneof::kBoolFoo));
}

TEST(HasOneofCaseTest, Description) {
  auto matcher = HasOneofCase<TestMessageWithOneof>(
      "foo", TestMessageWithOneof::kStringFoo);
  EXPECT_EQ(testing::DescribeMatcher<TestMessageWithOneof>(matcher),
            "is a `gutil.TestMessageWithOneof` protobuf message whose oneof "
            "field `foo` has case `string_foo`");
  EXPECT_EQ(testing::DescribeMatcher<TestMessageWithOneof>(Not(matcher)),
            "is a `gutil.TestMessageWithOneof` protobuf message whose oneof "
            "field `foo` does not have case `string_foo`");
}

}  // namespace
}  // namespace gutil
