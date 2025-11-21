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
#include "p4rt_app/sonic/app_db_to_pdpi_ir_translator.h"

#include <utility>
#include <vector>

#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "gmock/gmock.h"
#include "google/protobuf/text_format.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "p4_pdpi/ir.h"
#include "sai_p4/instantiations/google/sai_p4info.h"

namespace p4rt_app {
namespace sonic {
namespace {

using ::google::protobuf::TextFormat;
using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::testing::ContainerEq;
using ::testing::HasSubstr;
using ::testing::UnorderedElementsAreArray;

absl::StatusOr<pdpi::IrP4Info> GetCanonicalP4Info() {
  return pdpi::CreateIrP4Info(sai::GetP4Info(sai::Instantiation::kMiddleblock));
}

TEST(TranslatePdpiToAppDbTest, MatchKeyExact) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(R"pb(
                                            matches {
                                              name: "router_interface_id"
                                              exact { str: "16" }
                                            })pb",
                                          &table_entry));

  EXPECT_THAT(IrTableEntryToAppDbKey(table_entry),
              IsOkAndHolds(R"({"match/router_interface_id":"16"})"));
}

TEST(TranslatePdpiToAppDbTest, MatchKeyLpm) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(R"pb(
                                            matches {
                                              name: "ip_addr"
                                              lpm {
                                                value { ipv4: "10.1.1.0" }
                                                prefix_length: 24
                                              }
                                            })pb",
                                          &table_entry));

  EXPECT_THAT(IrTableEntryToAppDbKey(table_entry),
              IsOkAndHolds(R"({"match/ip_addr":"10.1.1.0/24"})"));
}

TEST(TranslatePdpiToAppDbTest, MatchKeyTernary) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(R"pb(
                                            priority: 123
                                            matches {
                                              name: "ether_type"
                                              ternary {
                                                value { hex_str: "0x1200" }
                                                mask { hex_str: "0xFF00" }
                                              }
                                            })pb",
                                          &table_entry));

  EXPECT_THAT(
      IrTableEntryToAppDbKey(table_entry),
      IsOkAndHolds(R"({"match/ether_type":"0x1200&0xFF00","priority":123})"));
}

TEST(TranslatePdpiToAppDbTest, MatchKeyOptional) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(
      TextFormat::ParseFromString(R"pb(
                                    priority: 123
                                    matches {
                                      name: "is_ip"
                                      optional { value { hex_str: "0x1" } }
                                    })pb",
                                  &table_entry));

  EXPECT_THAT(IrTableEntryToAppDbKey(table_entry),
              IsOkAndHolds(R"({"match/is_ip":"0x1","priority":123})"));
}

TEST(TranslatePdpiToAppDbTest, ActionSingle) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(
      TextFormat::ParseFromString(R"pb(
                                    action {
                                      name: "set_port_and_src_mac"
                                      params {
                                        name: "port"
                                        value { str: "Ethernet28/5" }
                                      }
                                      params {
                                        name: "src_mac"
                                        value { mac: "00:02:03:04:05:06" }
                                      }
                                    })pb",
                                  &table_entry));

  EXPECT_THAT(IrTableEntryToAppDbValues(table_entry),
              IsOkAndHolds(ContainerEq(std::vector<swss::FieldValueTuple>{
                  {"action", "set_port_and_src_mac"},
                  {"param/port", "Ethernet28/5"},
                  {"param/src_mac", "00:02:03:04:05:06"},
              })));
}

TEST(TranslatePdpiToAppDbTest, ActionSet) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(
      TextFormat::ParseFromString(R"pb(
                                    action_set {
                                      actions {
                                        action {
                                          name: "set_nexthop_id"
                                          params {
                                            name: "nexthop_id"
                                            value { str: "node-1:eth-1/1" }
                                          }
                                        }
                                        weight: 1
                                      }
                                      actions {
                                        action {
                                          name: "set_nexthop_id"
                                          params {
                                            name: "nexthop_id"
                                            value { str: "node-1:eth-2/1" }
                                          }
                                        }
                                        weight: 2
                                      }
                                    })pb",
                                  &table_entry));

  auto status = IrTableEntryToAppDbValues(table_entry);
  ASSERT_THAT(
      status,
      IsOkAndHolds(ContainerEq(std::vector<swss::FieldValueTuple>{
          {"actions",
           R"([{"action":"set_nexthop_id","param/nexthop_id":"node-1:eth-1/1","weight":1},)"
           R"({"action":"set_nexthop_id","param/nexthop_id":"node-1:eth-2/1","weight":2}])"},
      })));
}

TEST(TranslatePdpiToAppDbTest, ControllerMetadata) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(
      R"pb(
        action { name: "set_port_and_src_mac" }  # action required.
        controller_metadata: "abcdefg"
      )pb",
      &table_entry));
  EXPECT_THAT(
      IrTableEntryToAppDbValues(table_entry),
      IsOkAndHolds(UnorderedElementsAreArray(std::vector<swss::FieldValueTuple>(
          {{"action", "set_port_and_src_mac"},
           {"controller_metadata", "abcdefg"}}))));
}

TEST(TranslatePdpiToAppDbTest, Meters) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(
      R"pb(
        action { name: "set_port_and_src_mac" }  # action required.
        meter_config { cir: 123 cburst: 234 pir: 345 pburst: 456 }
      )pb",
      &table_entry));
  EXPECT_THAT(
      IrTableEntryToAppDbValues(table_entry),
      IsOkAndHolds(UnorderedElementsAreArray(std::vector<swss::FieldValueTuple>(
          {{"action", "set_port_and_src_mac"},
           {"meter/cir", "123"},
           {"meter/cburst", "234"},
           {"meter/pir", "345"},
           {"meter/pburst", "456"}}))));
}

TEST(TranslateAppDbToPdpiTest, AppDbKeyAndValuesToIrTableEntryExactMatch) {
  const std::string app_db_key =
      R"(FIXED_ROUTER_INTERFACE_TABLE:)"
      R"({"priority":123,"match/router_interface_id":"16"})";
  std::vector<std::pair<std::string, std::string>> app_db_values = {
      {"action", "set_port_and_src_mac"},
      {"param/port", "Ethernet28/5"},
      {"param/src_mac", "00:02:03:04:05:06"},
      {"meter/cir", "123"},
      {"meter/cburst", "234"},
      {"meter/pir", "345"},
      {"meter/pburst", "456"},
  };

  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info p4_info, GetCanonicalP4Info());
  ASSERT_THAT(
      AppDbKeyAndValuesToIrTableEntry(p4_info, app_db_key, app_db_values),
      IsOkAndHolds(EqualsProto(R"pb(
        table_name: "router_interface_table"
        priority: 123
        matches {
          name: "router_interface_id"
          exact { str: "16" }
        }
        action {
          name: "set_port_and_src_mac"
          params {
            name: "port"
            value { str: "Ethernet28/5" }
          }
          params {
            name: "src_mac"
            value { mac: "00:02:03:04:05:06" }
          }
        }
        meter_config { cir: 123 cburst: 234 pir: 345 pburst: 456 })pb")));
}

TEST(TranslateAppDbToPdpiTest, InvalidMatchKeyLpmFails) {
  // Missing prefix length in LPM field.
  const std::string app_db_key =
      R"(FIXED_IPV4_TABLE:{"match/ipv4_dst":"10.81.8.0"})";
  std::vector<std::pair<std::string, std::string>> app_db_values;

  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info p4_info, GetCanonicalP4Info());
  EXPECT_THAT(
      AppDbKeyAndValuesToIrTableEntry(p4_info, app_db_key, app_db_values),
      StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(TranslateAppDbToPdpiTest, MatchKeyTernary) {
  const std::string app_db_key =
      R"(ACL_ACL_INGRESS_TABLE:)"
      R"({"match/dst_ipv6":"ff02::&ffff:ffff:ffff:ffff::"})";
  std::vector<std::pair<std::string, std::string>> app_db_values;

  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info p4_info, GetCanonicalP4Info());
  ASSERT_THAT(
      AppDbKeyAndValuesToIrTableEntry(p4_info, app_db_key, app_db_values),
      IsOkAndHolds(EqualsProto(
          R"pb(
            table_name: "acl_ingress_table"
            matches {
              name: "dst_ipv6"
              ternary {
                value { ipv6: "ff02::" }
                mask { ipv6: "ffff:ffff:ffff:ffff::" }
              }
            }
          )pb")));
}

TEST(TranslateAppDbToPdpiTest, InvalidMatchKeyTernaryFails) {
  // Missing mask in ternary field.
  const std::string app_db_key =
      R"(ACL_ACL_INGRESS_TABLE:{"match/dst_ipv6":"ff02::"})";
  std::vector<std::pair<std::string, std::string>> app_db_values;

  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info p4_info, GetCanonicalP4Info());
  EXPECT_THAT(
      AppDbKeyAndValuesToIrTableEntry(p4_info, app_db_key, app_db_values),
      StatusIs(absl::StatusCode::kInvalidArgument));
}

// TODO: Renable when qos_queue_t is supported.
TEST(TranslateAppDbToPdpiTest,
     DISABLED_AppDbKeyAndValuesToIrTableEntryOptionalMatch) {
  const std::string app_db_key = R"(ACL_ACL_INGRESS_TABLE:)"
                                 R"({"priority":123, "match/is_ip":"0x1"})";
  std::vector<std::pair<std::string, std::string>> app_db_values = {
      {"action", "copy"},   {"param/qos_queue", "AF4"},
      {"meter/cir", "123"}, {"meter/cburst", "234"},
      {"meter/pir", "345"}, {"meter/pburst", "456"},
  };

  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info p4_info, GetCanonicalP4Info());
  ASSERT_THAT(
      AppDbKeyAndValuesToIrTableEntry(p4_info, app_db_key, app_db_values),
      IsOkAndHolds(EqualsProto(R"pb(
        table_name: "acl_ingress_table"
        priority: 123
        matches {
          name: "is_ip"
          optional { value { hex_str: "0x1" } }
        }
        action {
          name: "copy"
          params {
            name: "qos_queue"
            value { str: "AF4" }
          }
        }
        meter_config { cir: 123 cburst: 234 pir: 345 pburst: 456 })pb")));
}

TEST(TranslateAppDbToPdpiTest, ActionSetToIrTableEntry) {
  const std::string app_db_key =
      R"(FIXED_WCMP_GROUP_TABLE:{"match/wcmp_group_id":"8","priority":0})";
  std::vector<std::pair<std::string, std::string>> app_db_values = {
      {"actions",
       R"([{"action":"set_nexthop_id","param/nexthop_id":"8","weight":1},)"
       R"({"action":"set_nexthop_id","param/nexthop_id":"9","weight":2}])"},
  };

  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info p4_info, GetCanonicalP4Info());
  ASSERT_THAT(
      AppDbKeyAndValuesToIrTableEntry(p4_info, app_db_key, app_db_values),
      IsOkAndHolds(EqualsProto(
          R"pb(
            table_name: "wcmp_group_table"
            matches {
              name: "wcmp_group_id"
              exact { str: "8" }
            }
            action_set {
              actions {
                action {
                  name: "set_nexthop_id"
                  params {
                    name: "nexthop_id"
                    value { str: "8" }
                  }
                }
                weight: 1
              }
              actions {
                action {
                  name: "set_nexthop_id"
                  params {
                    name: "nexthop_id"
                    value { str: "9" }
                  }
                }
                weight: 2
              }
            })pb")));
}

TEST(TranslateAppDbToPdpiTest, UnspecifiedMatchFieldFails) {
  const std::string app_db_key =
      R"(FIXED_IPV4_TABLE:{"match/ipv4_dst":"10.81.8.0/8"})";

  // Assign ipv4_dst's match type to UNSPECIFIED
  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info p4_info, GetCanonicalP4Info());
  auto table_iter = p4_info.mutable_tables_by_name()->find("ipv4_table");
  ASSERT_TRUE(table_iter != p4_info.mutable_tables_by_name()->end());
  auto match_field_iter =
      table_iter->second.mutable_match_fields_by_name()->find("ipv4_dst");
  ASSERT_TRUE(match_field_iter !=
              table_iter->second.mutable_match_fields_by_name()->end());
  match_field_iter->second.mutable_match_field()->set_match_type(
      p4::config::v1::MatchField::UNSPECIFIED);

  EXPECT_THAT(AppDbKeyAndValuesToIrTableEntry(p4_info, app_db_key,
                                              /*app_db_values=*/{}),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(TranslateAppDbToPdpiTest, MatchFieldMustHaveAPrefix) {
  const std::string app_db_key =
      R"(FIXED_WCMP_GROUP_TABLE:{"wcmp_group_id":"8","priority":0})";

  // P4 match fields should start with match/.
  pdpi::IrP4Info p4info;
  EXPECT_THAT(AppDbKeyAndValuesToIrTableEntry(p4info, app_db_key,
                                              /*app_db_values=*/{}),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(TranslateAppDbToPdpiTest, InvalidMatchFieldNameFails) {
  const std::string app_db_key =
      R"(FIXED_ROUTER_INTERFACE_TABLE:{"match/bad_match_field":"16"})";

  // The router interface table does not have a 'bad_match_field' match field.
  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info p4_info, GetCanonicalP4Info());
  EXPECT_THAT(AppDbKeyAndValuesToIrTableEntry(p4_info, app_db_key,
                                              /*app_db_values=*/{}),
              StatusIs(absl::StatusCode::kNotFound,
                       HasSubstr("match field 'bad_match_field'")));
}

TEST(TranslateAppDbToPdpiTest, ActionParameterMustHaveAPrefix) {
  const std::string app_db_key =
      R"(FIXED_WCMP_GROUP_TABLE:{"match/wcmp_group_id":"8","priority":0})";
  std::vector<std::pair<std::string, std::string>> app_db_values = {
      {"actions",
       R"([{"action":"set_nexthop_id","nexthop_id":"8","weight":1},)"
       R"({"action":"set_nexthop_id","param/nexthop_id":"9","weight":2}])"},
  };

  // P4 action parameters should start with param/.
  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info p4info, GetCanonicalP4Info());
  EXPECT_THAT(
      AppDbKeyAndValuesToIrTableEntry(p4info, app_db_key, app_db_values),
      StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(TranslateAppDbToPdpiTest, InvalidActionParameterNameFails) {
  const std::string app_db_key =
      R"(FIXED_ROUTER_INTERFACE_TABLE:)"
      R"({"priority":123,"match/router_interface_id":"16"})";
  std::vector<std::pair<std::string, std::string>> app_db_values = {
      {"action", "set_port_and_src_mac"},
      {"param/invalid", "Ethernet28/5"},
      {"param/src_mac", "00:02:03:04:05:06"},
      {"meter/cir", "123"},
      {"meter/cburst", "234"},
      {"meter/pir", "345"},
      {"meter/pburst", "456"},
  };

  // the set_port_and_src_mac action does not have 'invalid' as a parameter.
  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info p4_info, GetCanonicalP4Info());
  EXPECT_THAT(
      AppDbKeyAndValuesToIrTableEntry(p4_info, app_db_key, app_db_values),
      StatusIs(absl::StatusCode::kNotFound,
               HasSubstr("action parameter 'invalid'")));
}

TEST(TranslateAppDbToPdpiTest, InvalidTableTypFails) {
  const std::string app_db_key =
      R"(RANDOM_ROUTER_INTERFACE_TABLE:{"match/router_interface_id":"16"})";

  // All P4 tables must start with "P4RT".
  pdpi::IrP4Info p4info;
  EXPECT_THAT(AppDbKeyAndValuesToIrTableEntry(p4info, app_db_key,
                                              /*app_db_values=*/{}),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       HasSubstr("<TableType>_<P4TableName>")));
}

TEST(TranslateAppDbToPdpiTest, InvalidTableNameFails) {
  const std::string app_db_key =
      R"(FIXED_FAKE_TABLE:{"match/bad_match_field":"16"})";

  // There should be no fixed 'FAKE_TABLE' in the p4rt program.
  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info p4_info, GetCanonicalP4Info());
  EXPECT_THAT(AppDbKeyAndValuesToIrTableEntry(p4_info, app_db_key,
                                              /*app_db_values=*/{}),
              StatusIs(absl::StatusCode::kNotFound,
                       HasSubstr("table 'fake_table' does not exist")));
}

TEST(TranslateAppDbToPdpiTest, MulticastGroupEntrySuccess) {
  pdpi::IrMulticastGroupEntry entry;
  ASSERT_TRUE(TextFormat::ParseFromString(
      R"pb(
        multicast_group_id: 17
        replicas { port: "Ethernet1/1/1" instance: 2 }
        replicas { port: "Ethernet1/1/1" instance: 3 }
      )pb",
      &entry));

  EXPECT_EQ(IrMulticastGroupEntryToAppDbKey(entry), "0x0011");
}

}  // namespace
}  // namespace sonic
}  // namespace p4rt_app
