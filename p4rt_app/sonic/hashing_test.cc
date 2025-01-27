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
#include <string>
#include <vector>

#include "absl/container/btree_set.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/substitute.h"
#include "gmock/gmock.h"
#include "google/protobuf/text_format.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "include/nlohmann/json.hpp"
#include "p4/config/v1/p4info.pb.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4rt_app/sonic/adapters/fake_consumer_notifier_adapter.h"
#include "p4rt_app/sonic/adapters/fake_producer_state_table_adapter.h"
#include "p4rt_app/sonic/adapters/fake_sonic_db_table.h"
#include "p4rt_app/sonic/adapters/fake_table_adapter.h"
#include "p4rt_app/sonic/adapters/mock_producer_state_table_adapter.h"
#include "p4rt_app/sonic/redis_connections.h"

namespace p4rt_app {
namespace sonic {
namespace {

using ::gutil::IsOk;
using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::testing::ElementsAre;
using ::testing::ExplainMatchResult;
using ::testing::HasSubstr;
using ::testing::IsEmpty;
using ::testing::Pair;
using ::testing::SizeIs;
using ::testing::Test;
using ::testing::UnorderedElementsAre;
using ::testing::UnorderedElementsAreArray;

MATCHER_P(IsUnorderedJsonListOf, hash_fields_list,
          absl::StrCat(negation ? "isn't" : "is",
                       " a json list containing the expected fields: {",
                       absl::StrJoin(hash_fields_list, ", "), "}")) {
  nlohmann::json json = nlohmann::json::parse(arg);
  if (!json.is_array()) {
    *result_listener << "Expected a JSON array.";
  }
  absl::btree_set<std::string> arg_values;
  for (const auto& field : json) {
    arg_values.insert(field.get<std::string>());
  }
  return ExplainMatchResult(UnorderedElementsAreArray(hash_fields_list),
                            arg_values, result_listener);
}

// This class generates tables with fake adapters backing it. Operations will
// succeed by default and the fake DBs can be accessed for verification and
// setup. Only one table generation function should be called per FakeTable
// instance since all generated tables use the same DB objects.
class FakeTable {
 public:
  FakeTable() : db_table_(), state_db_table_() {}

  // Table generation functions.
  HashTable GenerateHashTable() { return Table<HashTable>(); }
  SwitchTable GenerateSwitchTable() { return Table<SwitchTable>(); }

  FakeSonicDbTable& db_table() { return db_table_; }
  FakeSonicDbTable& state_db_table() { return state_db_table_; }

 private:
  template <typename T>
  T Table() {
    return T{
        .producer_state =
            std::make_unique<FakeProducerStateTableAdapter>(&db_table_),
        .notification_consumer =
            std::make_unique<FakeConsumerNotifierAdapter>(&db_table_),
        .app_db = std::make_unique<FakeTableAdapter>(&db_table_, "HASH_TABLE"),
        .app_state_db = std::make_unique<sonic::FakeTableAdapter>(
            &state_db_table_, "HASH_TABLE"),
    };
  }

  FakeSonicDbTable db_table_;
  FakeSonicDbTable state_db_table_;
};

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

TEST(HashingTest, TestHashPacketFieldConfigEqualsSelf) {
  HashPacketFieldConfig config{
      .key = "Hi, I'm a key",
      .fields = {"field_a", "field_b", "field_c"},
      .switch_table_key = "Hi, Switch key here",
  };
  EXPECT_TRUE(config == config);
  EXPECT_FALSE(config != config);
}

TEST(HashingTest, TestHashPacketFieldConfigComparisonWithKeyDiff) {
  HashPacketFieldConfig config{
      .key = "Hi, I'm a key",
      .fields = {"field_a", "field_b", "field_c"},
      .switch_table_key = "Hi, Switch key here",
  };
  auto diff_config = config;
  diff_config.key = "Hi, I'm another key";
  EXPECT_TRUE(config != diff_config);
  EXPECT_FALSE(config == diff_config);
}

TEST(HashingTest, TestHashPacketFieldConfigComparisonWithSwitchTableKeyDiff) {
  HashPacketFieldConfig config{
      .key = "Hi, I'm a key",
      .fields = {"field_a", "field_b", "field_c"},
      .switch_table_key = "Hi, Switch key here",
  };
  auto diff_config = config;
  diff_config.switch_table_key = "Hi, another Switch key here";
  EXPECT_TRUE(config != diff_config);
  EXPECT_FALSE(config == diff_config);
}

TEST(HashingTest, TestHashPacketFieldConfigComparisonWithFieldCountDiff) {
  HashPacketFieldConfig config{
      .key = "Hi, I'm a key",
      .fields = {"field_a", "field_b", "field_c"},
      .switch_table_key = "Hi, Switch key here",
  };
  auto diff_config = config;
  diff_config.fields = {"field_a", "field_b"};
  EXPECT_TRUE(config != diff_config);
  EXPECT_FALSE(config == diff_config);
}

TEST(HashingTest, TestHashPacketFieldConfigComparisonWithFieldDiff) {
  HashPacketFieldConfig config{
      .key = "Hi, I'm a key",
      .fields = {"field_a", "field_b", "field_c"},
      .switch_table_key = "Hi, Switch key here",
  };
  auto diff_config = config;
  diff_config.fields = {"field_a", "field_b", "field_d"};
  EXPECT_TRUE(config != diff_config);
  EXPECT_FALSE(config == diff_config);
}

TEST(HashingTest, GeneratesHashPacketFieldConfigs) {
  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info ir_p4_info, GetSampleHashConfig("ecmp"));
  ASSERT_OK_AND_ASSIGN(auto configs, ExtractHashPacketFieldConfigs(ir_p4_info));
  EXPECT_THAT(
      configs,
      UnorderedElementsAre(
          HashPacketFieldConfig({
              .key = "compute_ecmp_hash_ipv6",
              .fields = {"src_ip", "dst_ip", "l4_src_port", "l4_dst_port",
                         "ipv6_flow_label"},
              .switch_table_key = "ecmp_hash_ipv6",
          }),
          HashPacketFieldConfig({
              .key = "compute_ecmp_hash_ipv4",
              .fields = {"src_ip", "dst_ip", "l4_src_port", "l4_dst_port"},
              .switch_table_key = "ecmp_hash_ipv4",
          })));
}

TEST(HashingTest, ProgramHashFieldTableSucceeds) {
  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info ir_p4_info, GetSampleHashConfig("ecmp"));
  ASSERT_OK_AND_ASSIGN(auto configs, ExtractHashPacketFieldConfigs(ir_p4_info));
  FakeTable fake_table;
  HashTable hash_table = fake_table.GenerateHashTable();
  EXPECT_THAT(ProgramHashFieldTable(hash_table, configs), IsOk());

  ASSERT_THAT(
      fake_table.db_table().GetAllKeys(),
      UnorderedElementsAre("compute_ecmp_hash_ipv4", "compute_ecmp_hash_ipv6"));
  EXPECT_THAT(fake_table.db_table().ReadTableEntry("compute_ecmp_hash_ipv4"),
              IsOkAndHolds(ElementsAre(Pair(
                  "hash_field_list",
                  IsUnorderedJsonListOf(std::vector<std::string>(
                      {"src_ip", "dst_ip", "l4_src_port", "l4_dst_port"}))))));

  ASSERT_THAT(
      fake_table.db_table().ReadTableEntry("compute_ecmp_hash_ipv6"),
      IsOkAndHolds(ElementsAre(Pair(
          "hash_field_list", IsUnorderedJsonListOf(std::vector<std::string>(
                                 {"src_ip", "dst_ip", "l4_src_port",
                                  "l4_dst_port", "ipv6_flow_label"}))))));
}

TEST(HashingTest, SupportLagHashConfig) {
  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info ir_p4_info, GetSampleHashConfig("lag"));
  ASSERT_OK_AND_ASSIGN(auto configs, ExtractHashPacketFieldConfigs(ir_p4_info));
  EXPECT_THAT(
      configs,
      UnorderedElementsAre(
          HashPacketFieldConfig({
              .key = "compute_lag_hash_ipv6",
              .fields = {"src_ip", "dst_ip", "l4_src_port", "l4_dst_port",
                         "ipv6_flow_label"},
              .switch_table_key = "lag_hash_ipv6",
          }),
          HashPacketFieldConfig({
              .key = "compute_lag_hash_ipv4",
              .fields = {"src_ip", "dst_ip", "l4_src_port", "l4_dst_port"},
              .switch_table_key = "lag_hash_ipv4",
          })));
}

TEST(HashingTest, ExtractHashParamConfigsSucceeds) {
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
      ExtractHashParamConfigs(ir_p4_info),
      IsOkAndHolds(UnorderedElementsAre(
          Pair("ecmp_hash_algorithm", "crc_32lo"), Pair("ecmp_hash_seed", "1"),
          Pair("ecmp_hash_offset", "2"), Pair("lag_hash_algorithm", "crc"),
          Pair("lag_hash_seed", "10"), Pair("lag_hash_offset", "20"))));
}

TEST(HashingTest, ExtractHashParamConfigsSuccedsWithPartialSettings) {
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
      ExtractHashParamConfigs(ir_p4_info),
      IsOkAndHolds(UnorderedElementsAre(Pair("ecmp_hash_algorithm", "crc_32lo"),
                                        Pair("ecmp_hash_offset", "2"))));
}

TEST(HashingTest, ExtractHashParamConfigsIgnoresNonSaiHashAnnotations) {
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
      ExtractHashParamConfigs(ir_p4_info),
      IsOkAndHolds(UnorderedElementsAre(Pair("ecmp_hash_algorithm", "crc_32lo"),
                                        Pair("ecmp_hash_offset", "2"))));
}

TEST(HashingTest, ExtractHashParamConfigsReturnsErrorForNonEcmpOrLagAction) {
  pdpi::IrP4Info ir_p4_info;
  EXPECT_TRUE(google::protobuf::TextFormat::ParseFromString(
      R"pb(actions_by_name {
             key: "select_hash_algorithm"
             value {
               preamble {
                 id: 17825802
                 name: "ingress.hashing.select_hash_algorithm"
                 alias: "select_hash_algorithm"
                 annotations: "@sai_hash_algorithm(SAI_HASH_ALGORITHM_CRC_32LO)"
                 annotations: "@sai_hash_offset(2)"
                 annotations: "@sai_hashnonotreally(3)"
               }
             }
           })pb",
      &ir_p4_info));
  EXPECT_THAT(ExtractHashParamConfigs(ir_p4_info),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       HasSubstr("select_hash_algorithm")));
}

TEST(HashingTest,
     ExtractHashPacketFieldConfigsWithNoSaiHashFieldsReturnsEmpty) {
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
  EXPECT_THAT(ExtractHashPacketFieldConfigs(ir_p4_info),
              IsOkAndHolds(IsEmpty()));
}

TEST(HashingTest, DoesNotProgramHashTableWithoutHashFields) {
  FakeTable fake_table;
  HashTable hash_table = fake_table.GenerateHashTable();
  EXPECT_OK(ProgramHashFieldTable(hash_table, {}));
  EXPECT_THAT(fake_table.db_table().GetAllKeys(), IsEmpty());
}

TEST(HashingTest, DoesNotProgramSwitchTableWithoutHashFields) {
  SwitchTable switch_table;
  switch_table.producer_state =
      std::make_unique<testing::StrictMock<MockProducerStateTableAdapter>>();
  EXPECT_OK(ProgramSwitchTable(switch_table, {}, {}));
}

TEST(HashingTest, ExtractHashPacketFieldConfigsFailsForMultiArgAnnotations) {
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
  EXPECT_THAT(ExtractHashPacketFieldConfigs(ir_p4_info),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       HasSubstr("SAI_NATIVE_HASH_FIELD_SRC_IPV4")));
}

TEST(HashingTest, CannotExtractHashPacketFieldConfigWithUnknownHashField) {
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
  EXPECT_THAT(
      ExtractHashPacketFieldConfigs(ir_p4_info),
      StatusIs(absl::StatusCode::kInvalidArgument,
               HasSubstr("SAI_NATIVE_HASH_FIELD_WRONG_SRC_IP_IDENTIFIER")));
}

TEST(HashingTest, CannotExtractHashParamConfigsWithUnsupportedHashAlgorithm) {
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
  EXPECT_THAT(ExtractHashParamConfigs(ir_p4_info),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       HasSubstr("@sai_hash_algorithm(UNSUPPORTED)")));
}

TEST(HashingTest, CannotExtractHashParamConfigWthDuplicateHashAlgorithm) {
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
  EXPECT_THAT(ExtractHashParamConfigs(ir_p4_info),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       HasSubstr("@sai_hash_algorithm")));
}

TEST(HashingTest, CannotExtractHashParamConfigWithDuplicateSeed) {
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
  EXPECT_THAT(ExtractHashParamConfigs(ir_p4_info),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       HasSubstr("@sai_hash_seed")));
}

TEST(HashingTest, CannotExtractHashParamConfigWithDuplicateOffset) {
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
  EXPECT_THAT(ExtractHashParamConfigs(ir_p4_info),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       HasSubstr("@sai_hash_offset")));
}

TEST(HashingTest, CannotExtractHashParamConfigWithInvalidAnnotation) {
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
  EXPECT_THAT(ExtractHashParamConfigs(ir_p4_info),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       HasSubstr("@sai_hash_ohno")));
}

pdpi::IrP4Info FullHashIrP4Info() {
  pdpi::IrP4Info ir_p4info;
  if (!google::protobuf::TextFormat::ParseFromString(
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
               }
               actions_by_name {
                 key: "compute_ecmp_hash_ipv4"
                 value {
                   preamble {
                     id: 17825802
                     name: "ingress.hashing.compute_ecmp_hash_ipv4"
                     alias: "compute_ecmp_hash_ipv4"
                     annotations: "@sai_ecmp_hash(SAI_SWITCH_ATTR_ECMP_HASH_IPV4)"
                     annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_SRC_IPV4)"
                     annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_DST_IPV4)"
                     annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_L4_SRC_PORT)"
                     annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_L4_DST_PORT)"
                   }
                 }
               }
               actions_by_name {
                 key: "compute_lag_hash_ipv4"
                 value {
                   preamble {
                     id: 17825802
                     name: "ingress.hashing.compute_lag_hash_ipv4"
                     alias: "compute_lag_hash_ipv4"
                     annotations: "@sai_lag_hash(SAI_SWITCH_ATTR_LAG_HASH_IPV4)"
                     annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_SRC_IPV4)"
                     annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_DST_IPV4)"
                     annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_L4_SRC_PORT)"
                     annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_L4_DST_PORT)"
                   }
                 }
               }
               actions_by_name {
                 key: "compute_ecmp_hash_ipv6"
                 value {
                   preamble {
                     id: 17825802
                     name: "ingress.hashing.compute_ecmp_hash_ipv6"
                     alias: "compute_ecmp_hash_ipv6"
                     annotations: "@sai_ecmp_hash(SAI_SWITCH_ATTR_ECMP_HASH_IPV6)"
                     annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_SRC_IPV6)"
                     annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_DST_IPV6)"
                     annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_L4_SRC_PORT)"
                     annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_L4_DST_PORT)"
                     annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_IPV6_FLOW_LABEL)"
                   }
                 }
               }
               actions_by_name {
                 key: "compute_lag_hash_ipv6"
                 value {
                   preamble {
                     id: 17825802
                     name: "ingress.hashing.compute_lag_hash_ipv6"
                     alias: "compute_lag_hash_ipv6"
                     annotations: "@sai_lag_hash(SAI_SWITCH_ATTR_LAG_HASH_IPV6)"
                     annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_SRC_IPV6)"
                     annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_DST_IPV6)"
                     annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_L4_SRC_PORT)"
                     annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_L4_DST_PORT)"
                     annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_IPV6_FLOW_LABEL)"
                   }
                 }
               })pb",
          &ir_p4info)) {
    LOG(FATAL) << "Failed to generate default IrP4Info string.";
  }
  return ir_p4info;
}

TEST(HashingTest, ProgramSwitchTableSucceeds) {
  pdpi::IrP4Info ir_p4_info = FullHashIrP4Info();

  ASSERT_OK_AND_ASSIGN(auto hash_field_configs,
                       ExtractHashPacketFieldConfigs(ir_p4_info));
  ASSERT_OK_AND_ASSIGN(auto hash_value_configs,
                       ExtractHashParamConfigs(ir_p4_info));

  FakeTable fake_table;
  SwitchTable switch_table = fake_table.GenerateSwitchTable();
  ASSERT_OK(
      ProgramSwitchTable(switch_table, hash_value_configs, hash_field_configs));
  ASSERT_THAT(fake_table.db_table().GetAllKeys(), ElementsAre("switch"));
  EXPECT_THAT(fake_table.db_table().ReadTableEntry("switch"),
              IsOkAndHolds(UnorderedElementsAre(
                  Pair("lag_hash_seed", "10"), Pair("lag_hash_offset", "20"),
                  Pair("lag_hash_algorithm", "crc"),
                  Pair("lag_hash_ipv4", "compute_lag_hash_ipv4"),
                  Pair("lag_hash_ipv6", "compute_lag_hash_ipv6"),
                  Pair("ecmp_hash_seed", "1"), Pair("ecmp_hash_offset", "2"),
                  Pair("ecmp_hash_algorithm", "crc_32lo"),
                  Pair("ecmp_hash_ipv4", "compute_ecmp_hash_ipv4"),
                  Pair("ecmp_hash_ipv6", "compute_ecmp_hash_ipv6"))));
}

TEST(HashingTest, ProgramHashFieldTableReturnsErrorForBackendFailure) {
  FakeTable fake_table;
  HashTable hash_table = fake_table.GenerateHashTable();
  fake_table.db_table().SetResponseForKey("compute_ecmp_hash_ipv4",
                                          "SWSS_RC_UNKNOWN", "Test Failure");
  ASSERT_OK_AND_ASSIGN(auto hash_field_configs,
                       ExtractHashPacketFieldConfigs(FullHashIrP4Info()));
  EXPECT_THAT(ProgramHashFieldTable(hash_table, hash_field_configs),
              StatusIs(absl::StatusCode::kInternal, HasSubstr("Test Failure")));
}

TEST(HashingTest, ProgramSwitchTableReturnsErrorForBackendFailure) {
  FakeTable fake_table;
  SwitchTable switch_table = fake_table.GenerateSwitchTable();
  fake_table.db_table().SetResponseForKey("switch", "SWSS_RC_UNKNOWN",
                                          "Test Failure");
  ASSERT_OK_AND_ASSIGN(auto hash_field_configs,
                       ExtractHashPacketFieldConfigs(FullHashIrP4Info()));
  ASSERT_OK_AND_ASSIGN(auto hash_value_configs,
                       ExtractHashParamConfigs(FullHashIrP4Info()));

  EXPECT_THAT(
      ProgramSwitchTable(switch_table, hash_value_configs, hash_field_configs),
      StatusIs(absl::StatusCode::kInternal, HasSubstr("Test Failure")));
}

TEST(HashingTest, RemoveHashFieldTableRemovesTableFromDb) {
   FakeTable fake_table;
   HashTable hash_table = fake_table.GenerateHashTable();

   ASSERT_OK_AND_ASSIGN(auto hash_field_configs,
                        ExtractHashPacketFieldConfigs(FullHashIrP4Info()));
   ASSERT_OK(ProgramHashFieldTable(hash_table, hash_field_configs));

   std::vector<std::string> keys = fake_table.db_table().GetAllKeys();
   ASSERT_THAT(keys, SizeIs(hash_field_configs.size()));

   std::vector<std::string> keys_to_remove;
   keys_to_remove.push_back(keys.back());
   keys.pop_back();
   keys_to_remove.push_back(keys.back());
   keys.pop_back();

   ASSERT_OK(RemoveFromHashFieldTable(hash_table, keys_to_remove));
   ASSERT_THAT(fake_table.db_table().GetAllKeys(),
               UnorderedElementsAreArray(keys));
}

TEST(HashingTest, RemoveFromHashFieldTableReturnsErrorForBackendFailure) {
   FakeTable fake_table;
   HashTable hash_table = fake_table.GenerateHashTable();
   fake_table.db_table().SetResponseForKey("compute_ecmp_hash_ipv4",
                                           "SWSS_RC_UNKNOWN", "Test Failure");
   EXPECT_THAT(RemoveFromHashFieldTable(hash_table,
                                        {"a", "compute_ecmp_hash_ipv4", "b"}),
               StatusIs(absl::StatusCode::kInternal, HasSubstr("Test Failure")));
}

}  // namespace
}  // namespace sonic
}  // namespace p4rt_app
