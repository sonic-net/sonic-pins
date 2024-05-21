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

#include "p4rt_app/sonic/hashing.h"

#include <memory>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/substitute.h"
#include "gmock/gmock.h"
#include "google/protobuf/text_format.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4rt_app/sonic/adapters/mock_consumer_notifier_adapter.h"
#include "p4rt_app/sonic/adapters/mock_notification_producer_adapter.h"
#include "p4rt_app/sonic/adapters/mock_producer_state_table_adapter.h"
#include "p4rt_app/sonic/adapters/mock_table_adapter.h"

namespace p4rt_app {
namespace sonic {
namespace {

using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::testing::HasSubstr;
using ::testing::IsEmpty;
using ::testing::Pointwise;
using ::testing::Test;
using ::testing::UnorderedPointwise;

MATCHER(FieldPairsAre, "") {
  return std::get<0>(arg).first == std::get<1>(arg).first &&
         std::get<0>(arg).second == std::get<1>(arg).second;
}

MATCHER(HashFieldsAreEqual, "") {
  const EcmpHashEntry& a = std::get<0>(arg);
  const EcmpHashEntry& b = std::get<1>(arg);
  return ExplainMatchResult(a.hash_key, b.hash_key, result_listener) &&
         ExplainMatchResult(Pointwise(FieldPairsAre(), a.hash_value),
                            b.hash_value, result_listener);
}

MATCHER_P(HashValuesAreEqual, check_field_value, "") {
  const swss::FieldValueTuple& a = std::get<0>(arg);
  const swss::FieldValueTuple& b = std::get<1>(arg);
  if (check_field_value) {
    return a.first == b.first && a.second == b.second;
  } else {
    return a.first == b.first;
  }
}

p4::config::v1::Action GetHashAlgorithmAction(const std::string& alias) {
  p4::config::v1::Action action =
      gutil::ParseProtoOrDie<p4::config::v1::Action>(absl::Substitute(
          R"pb(
            preamble {
              id: 1
              name: "$0"
              alias: "$1"
              annotations: "@sai_hash_algorithm(SAI_HASH_ALGORITHM_CRC_32LO)"
              annotations: "@sai_hash_seed(0)"
              annotations: "@sai_hash_offset(0)"
            }
          )pb",
          absl::StrCat("ingress.hashing_config.", alias), alias));
  return action;
}

p4::config::v1::Action GetHashIpv4Action(const std::string& alias) {
  p4::config::v1::Action action = gutil::ParseProtoOrDie<
      p4::config::v1::Action>(absl::Substitute(
      R"pb(
        preamble {
          id: 4
          name: "$0"
          alias: "$1"
          annotations: "@sai_lag_hash(SAI_SWITCH_ATTR_LAG_HASH_IPV4)"
          annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_SRC_IPV4)"
          annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_DST_IPV4)"
          annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_L4_SRC_PORT)"
          annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_L4_DST_PORT)"
        }
      )pb",
      absl::StrCat("ingress.hashing_config.", alias), alias));
  return action;
}

p4::config::v1::Action GetHashIpv6Action(const std::string& alias) {
  p4::config::v1::Action action = gutil::ParseProtoOrDie<
      p4::config::v1::Action>(absl::Substitute(
      R"pb(
        preamble {
          id: 6
          name: "$0"
          alias: "$1"
          annotations: "@sai_lag_hash(SAI_SWITCH_ATTR_LAG_HASH_IPV6)"
          annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_SRC_IPV6)"
          annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_DST_IPV6)"
          annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_L4_SRC_PORT)"
          annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_L4_DST_PORT)"
          annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_IPV6_FLOW_LABEL)"
        }
      )pb",
      absl::StrCat("ingress.hashing_config.", alias), alias));
  return action;
}

absl::StatusOr<pdpi::IrP4Info> GetSampleHashConfig(const std::string& name) {
  p4::config::v1::P4Info p4_info;

  *p4_info.add_actions() =
      GetHashAlgorithmAction(absl::StrCat("select_", name, "_hash_algorithm"));
  *p4_info.add_actions() =
      GetHashIpv4Action(absl::StrCat("compute_", name, "_hash_ipv4"));
  *p4_info.add_actions() =
      GetHashIpv6Action(absl::StrCat("compute_", name, "_hash_ipv6"));

  return pdpi::CreateIrP4Info(p4_info);
}

TEST(HashingTest, SupportEcmpHashConfig) {
  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info ir_p4_info, GetSampleHashConfig("ecmp"));

  std::vector<EcmpHashEntry> expected_hash_fields = {
      {"compute_ecmp_hash_ipv6",
       {{"hash_field_list",
         R"(["src_ip","dst_ip","l4_src_port","l4_dst_port","ipv6_flow_label"])"}}},
      {"compute_ecmp_hash_ipv4",
       {{"hash_field_list",
         R"(["src_ip","dst_ip","l4_src_port","l4_dst_port"])"}}}};

  EXPECT_THAT(GenerateAppDbHashFieldEntries(ir_p4_info),
              IsOkAndHolds(UnorderedPointwise(HashFieldsAreEqual(),
                                              expected_hash_fields)));
}

TEST(HashingTest, SupportLagHashConfig) {
  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info ir_p4_info, GetSampleHashConfig("lag"));

  std::vector<EcmpHashEntry> expected_hash_fields = {
      {"compute_lag_hash_ipv6",
       {{"hash_field_list",
         R"(["src_ip","dst_ip","l4_src_port","l4_dst_port","ipv6_flow_label"])"}}},
      {"compute_lag_hash_ipv4",
       {{"hash_field_list",
         R"(["src_ip","dst_ip","l4_src_port","l4_dst_port"])"}}}};

  EXPECT_THAT(GenerateAppDbHashFieldEntries(ir_p4_info),
              IsOkAndHolds(UnorderedPointwise(HashFieldsAreEqual(),
                                              expected_hash_fields)));
}

TEST(HashingTest, GenerateAppDbHashValueEntries) {
  pdpi::IrP4Info ir_p4_info;
  EXPECT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(actions_by_name {
             key: "select_ecmp_hash_algorithm"
             value {
               preamble {
                 id: 17825802
                 name: "ingress.hashing.select_ecmp_hash_algorithm"
                 alias: "select_ecmp_hash_algorithm"
                 annotations: "@sai_hash_algorithm(SAI_HASH_ALGORITHM_CRC_32LO)"
                 annotations: "@sai_hash_seed(1)"
                 annotations: "@sai_hash_offset(2)"
               }
             }
           }
           actions_by_name {
             key: "select_lag_hash_algorithm"
             value {
               preamble {
                 id: 17825802
                 name: "ingress.hashing.select_lag_hash_algorithm"
                 alias: "select_lag_hash_algorithm"
                 annotations: "@sai_hash_algorithm(SAI_HASH_ALGORITHM_CRC)"
                 annotations: "@sai_hash_seed(10)"
                 annotations: "@sai_hash_offset(20)"
               }
             }
           })pb",
      &ir_p4_info));
  EXPECT_THAT(
      GenerateAppDbHashValueEntries(ir_p4_info),
      IsOkAndHolds(UnorderedPointwise(HashValuesAreEqual(true),
                                      std::vector<swss::FieldValueTuple>{
                                          {"ecmp_hash_algorithm", "crc_32lo"},
                                          {"ecmp_hash_seed", "1"},
                                          {"ecmp_hash_offset", "2"},
                                          {"lag_hash_algorithm", "crc"},
                                          {"lag_hash_seed", "10"},
                                          {"lag_hash_offset", "20"},
                                      })));
}

TEST(HashingTest, GenerateAppDbHashValueEntriesPartial) {
  pdpi::IrP4Info ir_p4_info;
  EXPECT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(actions_by_name {
             key: "select_ecmp_hash_algorithm"
             value {
               preamble {
                 id: 17825802
                 name: "ingress.hashing.select_ecmp_hash_algorithm"
                 alias: "select_ecmp_hash_algorithm"
                 annotations: "@sai_hash_algorithm(SAI_HASH_ALGORITHM_CRC_32LO)"
                 annotations: "@sai_hash_offset(2)"
               }
             }
           })pb",
      &ir_p4_info));
  EXPECT_THAT(
      GenerateAppDbHashValueEntries(ir_p4_info),
      IsOkAndHolds(UnorderedPointwise(HashValuesAreEqual(true),
                                      std::vector<swss::FieldValueTuple>{
                                          {"ecmp_hash_algorithm", "crc_32lo"},
                                          {"ecmp_hash_offset", "2"},
                                      })));
}

TEST(HashingTest, GenerateAppDbHashValueEntriesIgnoresNonSaiHashAnnotations) {
  pdpi::IrP4Info ir_p4_info;
  EXPECT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(actions_by_name {
             key: "select_ecmp_hash_algorithm"
             value {
               preamble {
                 id: 17825802
                 name: "ingress.hashing.select_ecmp_hash_algorithm"
                 alias: "select_ecmp_hash_algorithm"
                 annotations: "@sai_hash_algorithm(SAI_HASH_ALGORITHM_CRC_32LO)"
                 annotations: "@sai_hash_offset(2)"
                 annotations: "@sai_hashnonotreally(3)"
               }
             }
           })pb",
      &ir_p4_info));
  EXPECT_THAT(
      GenerateAppDbHashValueEntries(ir_p4_info),
      IsOkAndHolds(UnorderedPointwise(HashValuesAreEqual(true),
                                      std::vector<swss::FieldValueTuple>{
                                          {"ecmp_hash_algorithm", "crc_32lo"},
                                          {"ecmp_hash_offset", "2"},
                                      })));
}

TEST(HashingTest, GenerateAppDbEntryWithNoSaiHashFieldsReturnsEmpty) {
  pdpi::IrP4Info ir_p4_info;
  EXPECT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(actions_by_name {
             key: "NoAction"
             value {
               preamble {
                 id: 21257015
                 name: "NoAction"
                 alias: "NoAction"
                 annotations: "@noWarn(\"unused\")"
               }
             }
           })pb",
      &ir_p4_info));
  EXPECT_THAT(GenerateAppDbHashFieldEntries(ir_p4_info),
              IsOkAndHolds(IsEmpty()));
}

TEST(HashingTest, DoesNotProgramAppDbWithoutSaiHashFields) {
  pdpi::IrP4Info ir_p4_info;
  EXPECT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(actions_by_name {
             key: "NoAction"
             value {
               preamble {
                 id: 21257015
                 name: "NoAction"
                 alias: "NoAction"
                 annotations: "@noWarn(\"unused\")"
               }
             }
           })pb",
      &ir_p4_info));
  SwitchTable switch_table;
  switch_table.producer_state =
      std::make_unique<testing::StrictMock<MockProducerStateTableAdapter>>();
  EXPECT_OK(ProgramSwitchTable(switch_table, ir_p4_info, {}));

  HashTable hash_table;
  hash_table.producer_state =
      std::make_unique<testing::StrictMock<MockProducerStateTableAdapter>>();
  hash_table.notification_consumer =
      std::make_unique<testing::StrictMock<MockConsumerNotifierAdapter>>();
  hash_table.app_state_db =
      std::make_unique<testing::StrictMock<MockTableAdapter>>();
  EXPECT_OK(ProgramHashFieldTable(hash_table, ir_p4_info));
}

TEST(HashingTest, HashFieldAnnotationsMustHaveOneValue) {
  pdpi::IrP4Info ir_p4_info;
  EXPECT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(actions_by_name {
             key: "compute_ecmp_hash_ipv4"
             value {
               preamble {
                 id: 16777227
                 name: "ingress.hashing.compute_ecmp_hash_ipv4"
                 alias: "compute_ecmp_hash_ipv4"
                 annotations: "@sai_ecmp_hash(SAI_SWITCH_ATTR_ECMP_HASH_IP4)"
                 annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_SRC_IPV4, SAI_NATIVE_HASH_FIELD_DST_IPV4)"
                 annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_L4_SRC_PORT)"
                 annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_L4_DST_PORT)"
               }
             }
           })pb",
      &ir_p4_info));
  EXPECT_THAT(
      GenerateAppDbHashFieldEntries(ir_p4_info),
      StatusIs(absl::StatusCode::kInvalidArgument,
               HasSubstr("Unexpected number of native hash field specified")));
}

TEST(HashingTest, CannotGenerateAppDbEntryWithUnknownHashField) {
  pdpi::IrP4Info ir_p4_info;
  EXPECT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(actions_by_name {
             key: "compute_ecmp_hash_ipv4"
             value {
               preamble {
                 id: 16777227
                 name: "ingress.hashing.compute_ecmp_hash_ipv4"
                 alias: "compute_ecmp_hash_ipv4"
                 annotations: "@sai_ecmp_hash(SAI_SWITCH_ATTR_ECMP_HASH_IP4)"
                 annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_WRONG_SRC_IP_IDENTIFIER)"
                 annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_DST_IPV4)"
                 annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_L4_SRC_PORT)"
                 annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_L4_DST_PORT)"
               }
             }
           })pb",
      &ir_p4_info));
  EXPECT_THAT(GenerateAppDbHashFieldEntries(ir_p4_info),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       HasSubstr("Unable to find hash field string")));
}

TEST(HashingTest, CannotGenerateAppDbEntryWithUnsupportedHashAlgorithm) {
  pdpi::IrP4Info ir_p4_info;
  EXPECT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(actions_by_name {
             key: "select_ecmp_hash_algorithm"
             value {
               preamble {
                 id: 17825802
                 name: "ingress.hashing.select_ecmp_hash_algorithm"
                 alias: "select_ecmp_hash_algorithm"
                 annotations: "@sai_hash_algorithm(UNSUPPORTED)"
                 annotations: "@sai_hash_seed(1)"
                 annotations: "@sai_hash_offset(2)"
               }
             }
           })pb",
      &ir_p4_info));
  EXPECT_THAT(GenerateAppDbHashValueEntries(ir_p4_info),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(HashingTest, CannotGenerateAppDbEntryWthDuplicateHashAlgorithm) {
  pdpi::IrP4Info ir_p4_info;
  EXPECT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(actions_by_name {
             key: "select_ecmp_hash_algorithm"
             value {
               preamble {
                 id: 17825802
                 name: "ingress.hashing.select_ecmp_hash_algorithm"
                 alias: "select_ecmp_hash_algorithm"
                 annotations: "@sai_hash_algorithm(SAI_HASH_ALGORITHM_CRC_32LO)"
                 annotations: "@sai_hash_algorithm(SAI_HASH_ALGORITHM_CRC_32LO)"
                 annotations: "@sai_hash_seed(1)"
                 annotations: "@sai_hash_offset(2)"
               }
             }
           })pb",
      &ir_p4_info));
  EXPECT_THAT(GenerateAppDbHashValueEntries(ir_p4_info),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(HashingTest, CannotGenerateAppDbEntryWithDuplicateSeed) {
  pdpi::IrP4Info ir_p4_info;
  EXPECT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(actions_by_name {
             key: "select_ecmp_hash_algorithm"
             value {
               preamble {
                 id: 17825802
                 name: "ingress.hashing.select_ecmp_hash_algorithm"
                 alias: "select_ecmp_hash_algorithm"
                 annotations: "@sai_hash_algorithm(SAI_HASH_ALGORITHM_CRC_32LO)"
                 annotations: "@sai_hash_seed(0)"
                 annotations: "@sai_hash_seed(1)"
                 annotations: "@sai_hash_offset(2)"
               }
             }
           })pb",
      &ir_p4_info));
  EXPECT_THAT(GenerateAppDbHashValueEntries(ir_p4_info),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(HashingTest, CannotGenerateAppDbEntryWithDuplicateOffset) {
  pdpi::IrP4Info ir_p4_info;
  EXPECT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(actions_by_name {
             key: "select_ecmp_hash_algorithm"
             value {
               preamble {
                 id: 17825802
                 name: "ingress.hashing.select_ecmp_hash_algorithm"
                 alias: "select_ecmp_hash_algorithm"
                 annotations: "@sai_hash_algorithm(SAI_HASH_ALGORITHM_CRC_32LO)"
                 annotations: "@sai_hash_seed(1)"
                 annotations: "@sai_hash_offset(0)"
                 annotations: "@sai_hash_offset(1)"
               }
             }
           })pb",
      &ir_p4_info));
  EXPECT_THAT(GenerateAppDbHashValueEntries(ir_p4_info),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(HashingTest, CannotGenerateAppDbEntryWithInvalidAnnotation) {
  pdpi::IrP4Info ir_p4_info;
  EXPECT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(actions_by_name {
             key: "select_ecmp_hash_algorithm"
             value {
               preamble {
                 id: 17825802
                 name: "ingress.hashing.select_ecmp_hash_algorithm"
                 alias: "select_ecmp_hash_algorithm"
                 annotations: "@sai_hash_algorithm(SAI_HASH_ALGORITHM_CRC_32LO)"
                 annotations: "@sai_hash_seed(1)"
                 annotations: "@sai_hash_ohno(0)"
               }
             }
           })pb",
      &ir_p4_info));
  EXPECT_THAT(GenerateAppDbHashValueEntries(ir_p4_info),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

}  // namespace
}  // namespace sonic
}  // namespace p4rt_app
