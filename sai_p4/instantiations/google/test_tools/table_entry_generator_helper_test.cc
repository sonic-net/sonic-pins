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

#include "sai_p4/instantiations/google/test_tools/table_entry_generator_helper.h"

#include <tuple>

#include "absl/strings/numbers.h"
#include "absl/strings/substitute.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/testing.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_pdpi/ir.pb.h"

namespace sai {
namespace {
using ::gutil::EqualsProto;
using ::gutil::ParseProtoOrDie;
using ::p4::config::v1::MatchField;
using ::testing::Combine;
using ::testing::TestWithParam;
using ::testing::Values;

MATCHER_P2(EqualsProtoWithPriority, proto, priority, "") {
  auto priority_proto = proto;
  priority_proto.set_priority(priority);
  return testing::ExplainMatchResult(EqualsProto(priority_proto), arg,
                                     result_listener);
}

class MatchTypeTest : public TestWithParam<MatchField::MatchType> {};

pdpi::IrValue& TypedValue(pdpi::IrMatch& match, MatchField::MatchType type) {
  switch (type) {
    case MatchField::EXACT:
      return *match.mutable_exact();
    case MatchField::OPTIONAL:
      return *match.mutable_optional()->mutable_value();
    case MatchField::LPM:
      return *match.mutable_lpm()->mutable_value();
    case MatchField::TERNARY:
      return *match.mutable_ternary()->mutable_value();
    default:
      break;
  }
  LOG(FATAL) << "Cannot return match value without valid type.";
  return *match.mutable_exact();  // Unreachable.
}

TEST_P(MatchTypeTest, GenerateIpv4Entries) {
  auto table_definition = ParseProtoOrDie<pdpi::IrTableDefinition>(
      absl::Substitute(R"pb(
                         preamble { alias: "table" }
                         match_fields_by_name {
                           key: "match"
                           value {
                             match_field { id: 1 name: "match" match_type: $0 }
                             format: IPV4
                           }
                         })pb",
                       MatchField::MatchType_Name(GetParam())));
  auto base_entry = ParseProtoOrDie<pdpi::IrTableEntry>(
      R"pb(table_name: "table"
           matches {
             name: "static_match"
             exact { str: " aString " }
           }
           action { name: "action" })pb");
  auto generator = IrMatchFieldGenerator(table_definition, base_entry, "match");

  auto table_entry = base_entry;
  table_entry.add_matches()->set_name("match");
  auto& match = *table_entry.mutable_matches()->rbegin();
  if (GetParam() == MatchField::LPM) {
    match.mutable_lpm()->set_prefix_length(32);
  } else if (GetParam() == MatchField::TERNARY) {
    match.mutable_ternary()->mutable_mask()->set_ipv4("255.255.255.255");
  }
  std::string& ipv4_address = *TypedValue(match, GetParam()).mutable_ipv4();

  ipv4_address = "16.0.0.0";
  EXPECT_THAT(generator(0), EqualsProto(table_entry));

  ipv4_address = "16.0.0.1";
  EXPECT_THAT(generator(1), EqualsProto(table_entry));

  ipv4_address = "16.0.1.1";
  EXPECT_THAT(generator(257), EqualsProto(table_entry));

  ipv4_address = "143.255.255.255";
  EXPECT_THAT(generator(0x7fffffff), EqualsProto(table_entry));
}

TEST_P(MatchTypeTest, GenerateIpv6Entries) {
  auto table_definition = ParseProtoOrDie<pdpi::IrTableDefinition>(
      absl::Substitute(R"pb(
                         preamble { alias: "table" }
                         match_fields_by_name {
                           key: "match"
                           value {
                             match_field { id: 1 name: "match" match_type: $0 }
                             format: IPV6
                           }
                         })pb",
                       MatchField::MatchType_Name(GetParam())));
  auto base_entry =
      ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(table_name: "table"
                                               matches {
                                                 name: "static_match"
                                                 exact { str: " aString " }
                                               }
                                               action { name: "action" })pb");
  auto generator = IrMatchFieldGenerator(table_definition, base_entry, "match");

  auto table_entry = base_entry;
  table_entry.add_matches()->set_name("match");
  auto& match = *table_entry.mutable_matches()->rbegin();
  if (GetParam() == MatchField::LPM) {
    match.mutable_lpm()->set_prefix_length(64);
  } else if (GetParam() == MatchField::TERNARY) {
    match.mutable_ternary()->mutable_mask()->set_ipv6("ffff:ffff:ffff:ffff::");
  }
  std::string& ipv6_address = *TypedValue(match, GetParam()).mutable_ipv6();

  ipv6_address = "1234::";
  EXPECT_THAT(generator(0), EqualsProto(table_entry));

  ipv6_address = "1234:0:0:1::";
  EXPECT_THAT(generator(1), EqualsProto(table_entry));

  ipv6_address = "1234:0:f:ffff::";
  EXPECT_THAT(generator(0xfffff), EqualsProto(table_entry));

  ipv6_address = "1234:0:7fff:ffff::";
  EXPECT_THAT(generator(0x7fffffff), EqualsProto(table_entry));
}

TEST_P(MatchTypeTest, GenerateMacEntries) {
  auto table_definition = ParseProtoOrDie<pdpi::IrTableDefinition>(
      absl::Substitute(R"pb(
                         preamble { alias: "table" }
                         match_fields_by_name {
                           key: "match"
                           value {
                             match_field { id: 1 name: "match" match_type: $0 }
                             format: MAC
                           }
                         })pb",
                       MatchField::MatchType_Name(GetParam())));
  auto base_entry =
      ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(table_name: "table"
                                               matches {
                                                 name: "static_match"
                                                 exact { str: " aString " }
                                               }
                                               action { name: "action" })pb");
  auto generator = IrMatchFieldGenerator(table_definition, base_entry, "match");

  auto table_entry = base_entry;
  table_entry.add_matches()->set_name("match");
  auto& match = *table_entry.mutable_matches()->rbegin();
  if (GetParam() == MatchField::LPM) {
    match.mutable_lpm()->set_prefix_length(48);
  } else if (GetParam() == MatchField::TERNARY) {
    match.mutable_ternary()->mutable_mask()->set_mac("ff:ff:ff:ff:ff:ff");
  }
  std::string& mac_address = *TypedValue(match, GetParam()).mutable_mac();

  mac_address = "aa:00:00:00:00:00";
  EXPECT_THAT(generator(0), EqualsProto(table_entry));

  mac_address = "aa:00:00:00:00:01";
  EXPECT_THAT(generator(1), EqualsProto(table_entry));

  mac_address = "aa:00:00:0f:ff:ff";
  EXPECT_THAT(generator(0xfffff), EqualsProto(table_entry));

  mac_address = "aa:00:7f:ff:ff:ff";
  EXPECT_THAT(generator(0x7fffffff), EqualsProto(table_entry));
}

TEST_P(MatchTypeTest, GenerateHexStringEntries) {
  auto table_definition =
      ParseProtoOrDie<pdpi::IrTableDefinition>(absl::Substitute(
          R"pb(
            preamble { alias: "table" }
            match_fields_by_name {
              key: "match"
              value {
                match_field { id: 1 name: "match" bitwidth: 32 match_type: $0 }
                format: HEX_STRING
              }
            })pb",
          MatchField::MatchType_Name(GetParam())));
  auto base_entry =
      ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(table_name: "table"
                                               matches {
                                                 name: "static_match"
                                                 exact { str: " aString " }
                                               }
                                               action { name: "action" })pb");
  auto generator = IrMatchFieldGenerator(table_definition, base_entry, "match");

  auto table_entry = base_entry;
  table_entry.add_matches()->set_name("match");
  auto& match = *table_entry.mutable_matches()->rbegin();
  if (GetParam() == MatchField::LPM) {
    match.mutable_lpm()->set_prefix_length(32);
  } else if (GetParam() == MatchField::TERNARY) {
    match.mutable_ternary()->mutable_mask()->set_hex_str("0xffffffff");
  }
  std::string& hex_string = *TypedValue(match, GetParam()).mutable_hex_str();

  hex_string = "0x00000001";
  EXPECT_THAT(generator(0), EqualsProto(table_entry));

  hex_string = "0x00000002";
  EXPECT_THAT(generator(1), EqualsProto(table_entry));

  hex_string = "0x00100000";
  EXPECT_THAT(generator(0xfffff), EqualsProto(table_entry));

  hex_string = "0x80000000";
  EXPECT_THAT(generator(0x7fffffff), EqualsProto(table_entry));
}

// Test large strings with >64-bit masks.
TEST_P(MatchTypeTest, GenerateLargeHexStringEntries) {
  auto table_definition =
      ParseProtoOrDie<pdpi::IrTableDefinition>(absl::Substitute(
          R"pb(
            preamble { alias: "table" }
            match_fields_by_name {
              key: "match"
              value {
                match_field { id: 1 name: "match" bitwidth: 96 match_type: $0 }
                format: HEX_STRING
              }
            })pb",
          MatchField::MatchType_Name(GetParam())));
  auto base_entry =
      ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(table_name: "table"
                                               matches {
                                                 name: "static_match"
                                                 exact { str: " aString " }
                                               }
                                               action { name: "action" })pb");
  auto generator = IrMatchFieldGenerator(table_definition, base_entry, "match");

  auto table_entry = base_entry;
  table_entry.add_matches()->set_name("match");
  auto& match = *table_entry.mutable_matches()->rbegin();
  if (GetParam() == MatchField::LPM) {
    match.mutable_lpm()->set_prefix_length(96);
  } else if (GetParam() == MatchField::TERNARY) {
    match.mutable_ternary()->mutable_mask()->set_hex_str(
        "0xffffffffffffffffffffffff");
  }
  std::string& hex_string = *TypedValue(match, GetParam()).mutable_hex_str();

  hex_string = "0x000000000000000000000001";
  EXPECT_THAT(generator(0), EqualsProto(table_entry));

  hex_string = "0x000000000000000000000002";
  EXPECT_THAT(generator(1), EqualsProto(table_entry));

  hex_string = "0x000000000000000000100000";
  EXPECT_THAT(generator(0xfffff), EqualsProto(table_entry));

  hex_string = "0x000000000000000080000000";
  EXPECT_THAT(generator(0x7fffffff), EqualsProto(table_entry));
}

// Small strings have a modulus to repeat over the number set.
TEST_P(MatchTypeTest, GenerateSmallHexStringEntries) {
  auto table_definition =
      ParseProtoOrDie<pdpi::IrTableDefinition>(absl::Substitute(
          R"pb(
            preamble { alias: "table" }
            match_fields_by_name {
              key: "match"
              value {
                match_field { id: 1 name: "match" bitwidth: 15 match_type: $0 }
                format: HEX_STRING
              }
            })pb",
          MatchField::MatchType_Name(GetParam())));
  auto base_entry =
      ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(table_name: "table"
                                               matches {
                                                 name: "static_match"
                                                 exact { str: " aString " }
                                               }
                                               action { name: "action" })pb");
  auto generator = IrMatchFieldGenerator(table_definition, base_entry, "match");

  auto table_entry = base_entry;
  table_entry.add_matches()->set_name("match");
  auto& match = *table_entry.mutable_matches()->rbegin();
  if (GetParam() == MatchField::LPM) {
    match.mutable_lpm()->set_prefix_length(15);
  } else if (GetParam() == MatchField::TERNARY) {
    match.mutable_ternary()->mutable_mask()->set_hex_str("0x7fff");
  }
  std::string& hex_string = *TypedValue(match, GetParam()).mutable_hex_str();

  hex_string = "0x0001";
  EXPECT_THAT(generator(0), EqualsProto(table_entry));

  hex_string = "0x0002";
  EXPECT_THAT(generator(1), EqualsProto(table_entry));

  hex_string = "0x7fff";
  EXPECT_THAT(generator((1 << 15) - 2), EqualsProto(table_entry));

  hex_string = "0x0001";
  EXPECT_THAT(generator((1 << 15) - 1), EqualsProto(table_entry));

  hex_string = "0x0020";
  EXPECT_THAT(generator(0xfffff), EqualsProto(table_entry));

  hex_string = "0x0002";
  EXPECT_THAT(generator(0x7fffffff), EqualsProto(table_entry));
}

INSTANTIATE_TEST_SUITE_P(
    IrMatchFieldAndPriorityGenerator, MatchTypeTest,
    Values(MatchField::EXACT, MatchField::LPM, MatchField::OPTIONAL,
           MatchField::TERNARY),
    [](const testing::TestParamInfo<MatchField::MatchType>& info) {
      return MatchField::MatchType_Name(info.param);
    });

TEST(IrMatchFieldGenerator, HexStringsAreNeverZero) {
  auto table_definition = ParseProtoOrDie<pdpi::IrTableDefinition>(R"pb(
    preamble { alias: "table" }
    match_fields_by_name {
      key: "match"
      value {
        match_field { id: 1 name: "match" bitwidth: 5 match_type: EXACT }
        format: HEX_STRING
      }
    })pb");
  auto base_entry =
      ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(table_name: "table"
                                               action { name: "action" })pb");
  auto generator = IrMatchFieldGenerator(table_definition, base_entry, "match");

  auto table_entry = base_entry;
  table_entry.add_matches()->set_name("match");

  // Test for two full cycles of size <bitwidth>.
  for (int i = 0; i <= 2 << 5; ++i) {
    int hex_value;
    ASSERT_TRUE(absl::SimpleHexAtoi(generator(i).matches(0).exact().hex_str(),
                                    &hex_value));
    EXPECT_GT(hex_value, 0);
  }
}

TEST(IrMatchFieldGenerator, IsKilledByStringMatch) {
  auto table_definition = ParseProtoOrDie<pdpi::IrTableDefinition>(R"pb(
    preamble { alias: "table" }
    match_fields_by_name {
      key: "match"
      value {
        match_field { id: 1 name: "match" bitwidth: 5 match_type: EXACT }
        format: STRING
      }
    })pb");
  auto base_entry =
      ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(table_name: "table"
                                               action { name: "action" })pb");

  ASSERT_DEATH(
      { IrMatchFieldGenerator(table_definition, base_entry, "match"); },
      "Unable to generate match field with format type STRING");
}

TEST(IrMatchFieldGenerator, IsKilledByHexStringBitwidth0Match) {
  auto table_definition = ParseProtoOrDie<pdpi::IrTableDefinition>(R"pb(
    preamble { alias: "table" }
    match_fields_by_name {
      key: "match"
      value {
        match_field { id: 1 name: "match" bitwidth: 0 match_type: EXACT }
        format: HEX_STRING
      }
    })pb");
  auto base_entry =
      ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(table_name: "table"
                                               action { name: "action" })pb");

  ASSERT_DEATH(
      { IrMatchFieldGenerator(table_definition, base_entry, "match"); },
      "Unable to generate HEX_STRING match field of bitwidth 0");
}

TEST(IrMatchFieldGenerator, IsKilledByDuplicateMatch) {
  auto table_definition = ParseProtoOrDie<pdpi::IrTableDefinition>(R"pb(
    preamble { alias: "table" }
    match_fields_by_name {
      key: "match"
      value {
        match_field { id: 1 name: "match" bitwidth: 5 match_type: EXACT }
        format: HEX_STRING
      }
    })pb");
  auto base_entry =
      ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(table_name: "table"
                                               matches {
                                                 name: "match"
                                                 exact { hex_str: "0x01" }
                                               }
                                               action { name: "action" })pb");

  ASSERT_DEATH(
      { IrMatchFieldGenerator(table_definition, base_entry, "match"); },
      "Match field 'match' is already defined in the base entry.");
}

TEST(PriorityGenerator, IncrementsPriority) {
  auto base_entry = ParseProtoOrDie<pdpi::IrTableEntry>(
      R"pb(table_name: "table"
           matches {
             name: "match"
             exact { str: "Astring" }
           }
           action { name: "action" })pb");
  auto generator = PriorityGenerator(base_entry);

  pdpi::IrTableEntry expected_entry = base_entry;

  expected_entry.set_priority(1);
  EXPECT_THAT(generator(0), EqualsProto(expected_entry));

  expected_entry.set_priority(2);
  EXPECT_THAT(generator(1), EqualsProto(expected_entry));

  expected_entry.set_priority(0x10000);
  EXPECT_THAT(generator(0xffff), EqualsProto(expected_entry));

  expected_entry.set_priority(0x7fffffff);
  EXPECT_THAT(generator(0x7ffffffe), EqualsProto(expected_entry));
}

class MatchTypeAndFormatTest
    : public TestWithParam<std::tuple<MatchField::MatchType, pdpi::Format>> {};

TEST_P(MatchTypeAndFormatTest, ResultMatchesIrMatchFieldGeneratorWithPriority) {
  MatchField::MatchType match_type = std::get<0>(GetParam());
  pdpi::Format format = std::get<1>(GetParam());
  auto table_definition =
      ParseProtoOrDie<pdpi::IrTableDefinition>(absl::Substitute(
          R"pb(
            preamble { alias: "table" }
            match_fields_by_name {
              key: "match"
              value {
                match_field { id: 1 name: "match" match_type: $0 bitwidth: 32 }
                format: $1
              }
            })pb",
          MatchField::MatchType_Name(match_type), pdpi::Format_Name(format)));

  auto base_entry =
      ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(table_name: "table"
                                               action { name: "action" })pb");
  auto priority_and_match_field_generator =
      IrMatchFieldAndPriorityGenerator(table_definition, base_entry, "match");
  auto match_field_generator =
      IrMatchFieldGenerator(table_definition, base_entry, "match");

  EXPECT_THAT(priority_and_match_field_generator(0),
              EqualsProtoWithPriority(match_field_generator(0), 1));
  EXPECT_THAT(priority_and_match_field_generator(1),
              EqualsProtoWithPriority(match_field_generator(1), 2));
  EXPECT_THAT(
      priority_and_match_field_generator(0xfffff),
      EqualsProtoWithPriority(match_field_generator(0xfffff), 0x100000));
  EXPECT_THAT(
      priority_and_match_field_generator(0x7ffffffe),
      EqualsProtoWithPriority(match_field_generator(0x7ffffffe), 0x7fffffff));
}

INSTANTIATE_TEST_SUITE_P(
    IrMatchFieldAndPriorityGenerator, MatchTypeAndFormatTest,
    Combine(Values(MatchField::EXACT, MatchField::LPM, MatchField::OPTIONAL,
                   MatchField::TERNARY),
            Values(pdpi::Format::HEX_STRING, pdpi::Format::IPV4,
                   pdpi::Format::IPV6, pdpi::Format::MAC)),
    [](const testing::TestParamInfo<MatchTypeAndFormatTest::ParamType>& info) {
      return absl::StrCat(MatchField::MatchType_Name(std::get<0>(info.param)),
                          gutil::SnakeCaseToCamelCase(
                              pdpi::Format_Name(std::get<1>(info.param))));
    });

}  // namespace
}  // namespace sai
