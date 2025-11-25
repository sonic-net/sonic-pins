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
#include "p4rt_app/sonic/app_db_manager.h"

#include <memory>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "gmock/gmock.h"
#include "google/protobuf/text_format.h"
#include "google/rpc/code.pb.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status_matchers.h"
#include "p4_pdpi/ir.pb.h"
#include "p4rt_app/sonic/adapters/fake_consumer_notifier_adapter.h"
#include "p4rt_app/sonic/adapters/fake_producer_state_table_adapter.h"
#include "p4rt_app/sonic/adapters/fake_sonic_db_table.h"
#include "p4rt_app/sonic/adapters/fake_table_adapter.h"
#include "p4rt_app/sonic/adapters/fake_zmq_producer_state_table_adapter.h"
#include "p4rt_app/sonic/adapters/mock_consumer_notifier_adapter.h"
#include "p4rt_app/sonic/adapters/mock_producer_state_table_adapter.h"
#include "p4rt_app/sonic/adapters/mock_table_adapter.h"
#include "p4rt_app/sonic/adapters/mock_zmq_producer_state_table_adapter.h"
#include "p4rt_app/sonic/packet_replication_entry_translation.h"
#include "p4rt_app/sonic/redis_connections.h"
#include "p4rt_app/sonic/vrf_entry_translation.h"
#include "p4rt_app/tests/lib/app_db_entry_builder.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "swss/rediscommand.h"
#include "swss/schema.h"
#include "swss/table.h"

namespace p4rt_app {
namespace sonic {
namespace {

using ::google::protobuf::TextFormat;
using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::p4rt_app::test_lib::AppDbEntryBuilder;
using ::testing::ContainerEq;
using ::testing::DoAll;
using ::testing::ElementsAre;
using ::testing::Eq;
using ::testing::IsEmpty;
using ::testing::Return;
using ::testing::SetArgReferee;
using ::testing::SizeIs;
using ::testing::StrictMock;

constexpr int kRpcOk = ::google::rpc::Code::OK;
constexpr int kRpcAborted = ::google::rpc::Code::ABORTED;
constexpr int kRpcInternal = ::google::rpc::Code::INTERNAL;
constexpr int kRpcNotFound = ::google::rpc::Code::NOT_FOUND;

MATCHER_P(HasErrorCode, code,
          absl::StrCat(".code() = ", google::rpc::Code_Name(code))) {
  return arg.code() == code;
}

const std::vector<std::pair<std::string, std::string>>&
GetSuccessfulResponseValues() {
  static const std::vector<std::pair<std::string, std::string>>* const
      kResponse = new std::vector<std::pair<std::string, std::string>>{
          {"SWSS_RC_SUCCESS", "SWSS_RC_SUCCESS"}};
  return *kResponse;
}

class AppDbP4TableEntryTest : public ::testing::Test {
 protected:
  AppDbP4TableEntryTest() {
    auto p4rt_producer = std::make_unique<MockZmqProducerStateTableAdapter>();
    auto p4rt_app_db = std::make_unique<StrictMock<MockTableAdapter>>();
    auto p4rt_counter_db = std::make_unique<MockTableAdapter>();
    auto vrf_producer_state = std::make_unique<MockProducerStateTableAdapter>();

    // Save a pointer so we can test against the mocks.
    mock_p4rt_producer_ = p4rt_producer.get();
    mock_p4rt_app_db_ = p4rt_app_db.get();
    mock_p4rt_counter_db_ = p4rt_counter_db.get();

    mock_p4rt_table_ = P4rtTable{
        .producer = std::move(p4rt_producer),
        .app_db = std::move(p4rt_app_db),
        .counter_db = std::move(p4rt_counter_db),
    };

    mock_vrf_producer_ = vrf_producer_state.get();

    mock_vrf_table_ = VrfTable{
        .producer_state = std::move(vrf_producer_state),
        .notification_consumer =
            std::make_unique<MockConsumerNotifierAdapter>(),
        .app_db = std::make_unique<MockTableAdapter>(),
        .app_state_db = std::make_unique<MockTableAdapter>(),
    };
  }

  // Mock AppDb tables.
  MockZmqProducerStateTableAdapter* mock_p4rt_producer_;
  StrictMock<MockTableAdapter>* mock_p4rt_app_db_;
  MockTableAdapter* mock_p4rt_counter_db_;
  P4rtTable mock_p4rt_table_;
  MockProducerStateTableAdapter* mock_vrf_producer_;
  VrfTable mock_vrf_table_;
};

TEST_F(AppDbP4TableEntryTest, InsertTableEntry) {
  pdpi::IrEntity entity;
  ASSERT_TRUE(
      TextFormat::ParseFromString(R"pb(
                                    table_entry {
                                      table_name: "router_interface_table"
                                      priority: 123
                                      matches {
                                        name: "router_interface_id"
                                        exact { hex_str: "16" }
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
                                    })pb",
                                  &entity));

  ASSERT_OK_AND_ASSIGN(
      auto update,
      CreateAppDbUpdate(p4::v1::Update::INSERT, entity,
                        sai::GetIrP4Info(sai::Instantiation::kMiddleblock)));
  // Expected RedisDB entry.
  const auto expected = AppDbEntryBuilder{}
                            .SetTableName("FIXED_ROUTER_INTERFACE_TABLE")
                            .SetPriority(123)
                            .AddMatchField("router_interface_id", "16")
                            .SetAction("set_port_and_src_mac")
                            .AddActionParam("port", "Ethernet28/5")
                            .AddActionParam("src_mac", "00:02:03:04:05:06");
  const std::vector<swss::KeyOpFieldsValuesTuple> expected_key_value = {
      std::make_tuple(expected.GetKey(), "SET", expected.GetValueList())};
  EXPECT_CALL(*mock_p4rt_producer_, send(expected_key_value)).Times(1);

  // Expected OrchAgent response.
  const swss::KeyOpFieldsValuesTuple expected_resp_key_value =
      std::make_tuple(expected.GetKey(), "", GetSuccessfulResponseValues());
  const std::vector<std::shared_ptr<swss::KeyOpFieldsValuesTuple>> kcos = {
      std::make_shared<swss::KeyOpFieldsValuesTuple>(expected_resp_key_value)};
  EXPECT_CALL(*mock_p4rt_producer_, wait)
      .WillOnce(DoAll(SetArgReferee<0>("APPL_DB"),
                      SetArgReferee<1>("P4RT_TABLE"), SetArgReferee<2>(kcos),
                      Return(true)));

  pdpi::IrUpdateStatus status;
  ASSERT_OK(PerformAppDbUpdates(mock_p4rt_table_, mock_vrf_table_,
                                {{update, &status}}));
  EXPECT_THAT(status, EqualsProto("code: OK"));
}

TEST_F(AppDbP4TableEntryTest, ModifyTableEntry) {
  pdpi::IrEntity entity;
  ASSERT_TRUE(
      TextFormat::ParseFromString(R"pb(
                                    table_entry {
                                      table_name: "router_interface_table"
                                      priority: 123
                                      matches {
                                        name: "router_interface_id"
                                        exact { hex_str: "16" }
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
                                    })pb",
                                  &entity));
  ASSERT_OK_AND_ASSIGN(
      auto update,
      CreateAppDbUpdate(p4::v1::Update::MODIFY, entity,
                        sai::GetIrP4Info(sai::Instantiation::kMiddleblock)));

  const auto expected = AppDbEntryBuilder{}
                            .SetTableName("FIXED_ROUTER_INTERFACE_TABLE")
                            .SetPriority(123)
                            .AddMatchField("router_interface_id", "16")
                            .SetAction("set_port_and_src_mac")
                            .AddActionParam("port", "Ethernet28/5")
                            .AddActionParam("src_mac", "00:02:03:04:05:06");
  const std::vector<swss::KeyOpFieldsValuesTuple> expected_key_value = {
      std::make_tuple(expected.GetKey(), "SET", expected.GetValueList())};
  EXPECT_CALL(*mock_p4rt_producer_, send(expected_key_value)).Times(1);

  // OrchAgent returns success.
  const swss::KeyOpFieldsValuesTuple expected_resp_key_value =
      std::make_tuple(expected.GetKey(), "", GetSuccessfulResponseValues());
  const std::vector<std::shared_ptr<swss::KeyOpFieldsValuesTuple>> kcos = {
      std::make_shared<swss::KeyOpFieldsValuesTuple>(expected_resp_key_value)};
  EXPECT_CALL(*mock_p4rt_producer_, wait)
      .WillOnce(DoAll(SetArgReferee<0>("APPL_DB"),
                      SetArgReferee<1>("P4RT_TABLE"), SetArgReferee<2>(kcos),
                      Return(true)));

  pdpi::IrUpdateStatus status;
  ASSERT_OK(PerformAppDbUpdates(mock_p4rt_table_, mock_vrf_table_,
                                {{update, &status}}));
  EXPECT_THAT(status, EqualsProto("code: OK"));
}

TEST_F(AppDbP4TableEntryTest, DeleteTableEntry) {
  pdpi::IrEntity entity;
  ASSERT_TRUE(
      TextFormat::ParseFromString(R"pb(
                                    table_entry {
                                      table_name: "router_interface_table"
                                      priority: 123
                                      matches {
                                        name: "router_interface_id"
                                        exact { hex_str: "16" }
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
                                    })pb",
                                  &entity));
  ASSERT_OK_AND_ASSIGN(
      auto update,
      CreateAppDbUpdate(p4::v1::Update::DELETE, entity,
                        sai::GetIrP4Info(sai::Instantiation::kMiddleblock)));

  const auto expected = AppDbEntryBuilder{}
                            .SetTableName("FIXED_ROUTER_INTERFACE_TABLE")
                            .SetPriority(123)
                            .AddMatchField("router_interface_id", "16");
  const std::vector<swss::KeyOpFieldsValuesTuple> expected_key_value = {
      std::make_tuple(expected.GetKey(), "DEL",
                      std::vector<swss::FieldValueTuple>{})};
  EXPECT_CALL(*mock_p4rt_producer_, send(expected_key_value)).Times(1);

  // OrchAgent returns success.
  const swss::KeyOpFieldsValuesTuple expected_resp_key_value =
      std::make_tuple(expected.GetKey(), "", GetSuccessfulResponseValues());
  const std::vector<std::shared_ptr<swss::KeyOpFieldsValuesTuple>> kcos = {
      std::make_shared<swss::KeyOpFieldsValuesTuple>(expected_resp_key_value)};
  EXPECT_CALL(*mock_p4rt_producer_, wait)
      .WillOnce(DoAll(SetArgReferee<0>("APPL_DB"),
                      SetArgReferee<1>("P4RT_TABLE"), SetArgReferee<2>(kcos),
                      Return(true)));

  pdpi::IrUpdateStatus status;
  ASSERT_OK(PerformAppDbUpdates(mock_p4rt_table_, mock_vrf_table_,
                                {{update, &status}}));
  EXPECT_THAT(status, EqualsProto("code: OK"));
}

TEST_F(AppDbP4TableEntryTest, ReadTableAclEntryWithoutCounterData) {
  const auto app_db_entry = AppDbEntryBuilder{}
                                .SetTableName("ACL_ACL_INGRESS_TABLE")
                                .SetPriority(123)
                                .AddMatchField("ether_type", "0x0800&0xFFFF")
                                .SetAction("drop");

  EXPECT_CALL(*mock_p4rt_app_db_, getTablePrefix());
  EXPECT_CALL(*mock_p4rt_app_db_, get(Eq(app_db_entry.GetKey())))
      .WillOnce(Return(app_db_entry.GetValueList()));

  // We will always check the CountersDB for packet data, but if nothing exists
  // we should not update the table entry.
  EXPECT_CALL(*mock_p4rt_counter_db_, get(app_db_entry.GetKey()))
      .WillOnce(Return(std::vector<std::pair<std::string, std::string>>{}));

  auto table_entry_status = ReadP4TableEntry(
      mock_p4rt_table_, sai::GetIrP4Info(sai::Instantiation::kMiddleblock),
      app_db_entry.GetKey());
  ASSERT_TRUE(table_entry_status.ok()) << table_entry_status.status();
  pdpi::IrTableEntry table_entry = table_entry_status.value();

  EXPECT_THAT(table_entry, EqualsProto(R"pb(
                table_name: "acl_ingress_table"
                priority: 123
                matches {
                  name: "ether_type"
                  ternary {
                    value { hex_str: "0x0800" }
                    mask { hex_str: "0xFFFF" }
                  }
                }
                action { name: "drop" })pb"));
}

TEST_F(AppDbP4TableEntryTest, ReadAclTableEntryWithCounterData) {
  const auto app_db_entry = AppDbEntryBuilder{}
                                .SetTableName("ACL_ACL_INGRESS_TABLE")
                                .SetPriority(123)
                                .AddMatchField("ether_type", "0x0800&0xFFFF")
                                .SetAction("drop");

  EXPECT_CALL(*mock_p4rt_app_db_, getTablePrefix());
  EXPECT_CALL(*mock_p4rt_app_db_, get(Eq(app_db_entry.GetKey())))
      .WillOnce(Return(app_db_entry.GetValueList()));

  // We want to support 64-bit integers for both the number of packets, as well
  // as the number of bytes.
  //
  // Using decimal numbers:
  //    1152921504606846975 = 0x0FFF_FFFF_FFFF_FFFF
  //    1076078835964837887 = 0x0EEE_FFFF_FFFF_FFFF
  EXPECT_CALL(*mock_p4rt_counter_db_, get(app_db_entry.GetKey()))
      .WillOnce(Return(std::vector<std::pair<std::string, std::string>>{
          {"packets", "1076078835964837887"},
          {"bytes", "1152921504606846975"}}));

  auto table_entry_status = ReadP4TableEntry(
      mock_p4rt_table_, sai::GetIrP4Info(sai::Instantiation::kMiddleblock),
      app_db_entry.GetKey());
  ASSERT_TRUE(table_entry_status.ok()) << table_entry_status.status();
  pdpi::IrTableEntry table_entry = table_entry_status.value();

  EXPECT_THAT(table_entry, EqualsProto(R"pb(
                table_name: "acl_ingress_table"
                priority: 123
                matches {
                  name: "ether_type"
                  ternary {
                    value { hex_str: "0x0800" }
                    mask { hex_str: "0xFFFF" }
                  }
                }
                action { name: "drop" }
                counter_data {
                  byte_count: 1152921504606846975
                  packet_count: 1076078835964837887
                })pb"));
}

TEST_F(AppDbP4TableEntryTest, ReadAclTableEntryIgnoresInvalidCounterData) {
  const auto app_db_entry = AppDbEntryBuilder{}
                                .SetTableName("ACL_ACL_INGRESS_TABLE")
                                .SetPriority(123)
                                .AddMatchField("ether_type", "0x0800&0xFFFF")
                                .SetAction("drop");
  auto app_db_values = app_db_entry.GetValueList();
  app_db_values.push_back(std::make_pair("meter/cir", "123"));
  app_db_values.push_back(std::make_pair("meter/cburst", "234"));
  app_db_values.push_back(std::make_pair("meter/pir", "345"));
  app_db_values.push_back(std::make_pair("meter/pburst", "456"));

  EXPECT_CALL(*mock_p4rt_app_db_, getTablePrefix());
  EXPECT_CALL(*mock_p4rt_app_db_, get(Eq(app_db_entry.GetKey())))
      .WillOnce(Return(app_db_values));

  EXPECT_CALL(*mock_p4rt_counter_db_, get(app_db_entry.GetKey()))
      .WillOnce(Return(std::vector<std::pair<std::string, std::string>>{
          {"packets", "A"},
          {"bytes", "B"},
          {"green_packets", "A"},
          {"green_bytes", "B"},
          {"yellow_packets", "A"},
          {"yellow_bytes", "B"},
          {"red_packets", "A"},
          {"red_bytes", "B"},
      }));

  auto table_entry_status = ReadP4TableEntry(
      mock_p4rt_table_, sai::GetIrP4Info(sai::Instantiation::kMiddleblock),
      app_db_entry.GetKey());
  ASSERT_TRUE(table_entry_status.ok()) << table_entry_status.status();
  pdpi::IrTableEntry table_entry = table_entry_status.value();

  EXPECT_THAT(
      table_entry, EqualsProto(R"pb(
        table_name: "acl_ingress_table"
        priority: 123
        matches {
          name: "ether_type"
          ternary {
            value { hex_str: "0x0800" }
            mask { hex_str: "0xFFFF" }
          }
        }
        action { name: "drop" }
        meter_config { cir: 123 cburst: 234 pir: 345 pburst: 456 })pb"));
}

TEST_F(AppDbP4TableEntryTest, ReadAclTableEntryIgnoresCountersForFixedTables) {
  const auto app_db_entry = AppDbEntryBuilder{}
                                .SetTableName("FIXED_ROUTER_INTERFACE_TABLE")
                                .SetPriority(123)
                                .AddMatchField("router_interface_id", "16")
                                .SetAction("set_port_and_src_mac")
                                .AddActionParam("port", "Ethernet28/5")
                                .AddActionParam("src_mac", "00:02:03:04:05:06");

  EXPECT_CALL(*mock_p4rt_app_db_, get(Eq(app_db_entry.GetKey())))
      .WillOnce(Return(app_db_entry.GetValueList()));
  EXPECT_CALL(*mock_p4rt_counter_db_, get).Times(0);

  auto table_entry_status = ReadP4TableEntry(
      mock_p4rt_table_, sai::GetIrP4Info(sai::Instantiation::kMiddleblock),
      app_db_entry.GetKey());
  ASSERT_TRUE(table_entry_status.ok()) << table_entry_status.status();
  pdpi::IrTableEntry table_entry = table_entry_status.value();

  EXPECT_THAT(table_entry, EqualsProto(R"pb(
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
                })pb"));
}

TEST_F(AppDbP4TableEntryTest, ReadAclTableEntryWithMeterCounterData) {
  const auto app_db_entry = AppDbEntryBuilder{}
                                .SetTableName("ACL_ACL_INGRESS_TABLE")
                                .SetPriority(123)
                                .AddMatchField("ether_type", "0x0800&0xFFFF")
                                .SetAction("drop");
  EXPECT_CALL(*mock_p4rt_app_db_, getTablePrefix());
  auto app_db_values = app_db_entry.GetValueList();
  app_db_values.push_back(std::make_pair("meter/cir", "123"));
  app_db_values.push_back(std::make_pair("meter/cburst", "234"));
  app_db_values.push_back(std::make_pair("meter/pir", "345"));
  app_db_values.push_back(std::make_pair("meter/pburst", "456"));
  EXPECT_CALL(*mock_p4rt_app_db_, get(Eq(app_db_entry.GetKey())))
      .WillOnce(Return(app_db_values));

  // We want to support 64-bit integers for both the number of packets, as well
  // as the number of bytes.
  //
  // Using decimal numbers:
  //    1152921504606846975 = 0x0FFF_FFFF_FFFF_FFFF
  //    1076078835964837887 = 0x0EEE_FFFF_FFFF_FFFF
  EXPECT_CALL(*mock_p4rt_counter_db_, get(app_db_entry.GetKey()))
      .WillOnce(Return(std::vector<std::pair<std::string, std::string>>{
          {"packets", "1076078835964837887"},
          {"bytes", "1152921504606846975"},
          {"green_packets", "10"},
          {"green_bytes", "100"},
          {"yellow_packets", "11"},
          {"yellow_bytes", "101"},
          {"red_packets", "12"},
          {"red_bytes", "102"},
      }));

  auto table_entry_status = ReadP4TableEntry(
      mock_p4rt_table_, sai::GetIrP4Info(sai::Instantiation::kMiddleblock),
      app_db_entry.GetKey());
  ASSERT_TRUE(table_entry_status.ok()) << table_entry_status.status();
  pdpi::IrTableEntry table_entry = table_entry_status.value();
  EXPECT_THAT(table_entry, EqualsProto(R"pb(
                table_name: "acl_ingress_table"
                priority: 123
                matches {
                  name: "ether_type"
                  ternary {
                    value { hex_str: "0x0800" }
                    mask { hex_str: "0xFFFF" }
                  }
                }
                action { name: "drop" }
                meter_config { cir: 123 cburst: 234 pir: 345 pburst: 456 }
                counter_data {
                  byte_count: 1152921504606846975
                  packet_count: 1076078835964837887
                }
                meter_counter_data {
                  green { byte_count: 100 packet_count: 10 }
                  yellow { byte_count: 101 packet_count: 11 }
                  red { byte_count: 102 packet_count: 12 }
                })pb"));
}

TEST_F(AppDbP4TableEntryTest, GetAllP4KeysReturnsInstalledKeys) {
  EXPECT_CALL(*mock_p4rt_app_db_, keys)
      .WillOnce(Return(std::vector<std::string>{"TABLE:{key}"}));

  EXPECT_THAT(GetAllP4TableEntryKeys(mock_p4rt_table_),
              ContainerEq(std::vector<std::string>{"TABLE:{key}"}));
}

TEST_F(AppDbP4TableEntryTest, GetAllP4KeysIgnoresCertainTables) {
  EXPECT_CALL(*mock_p4rt_app_db_, keys)
      .WillOnce(Return(std::vector<std::string>{
          "TABLE:{key}",
          "REPLICATION_IP_MULTICAST_TABLE:{key}",
          "ACL_TABLE_DEFINITION_TABLE:{key}",
      }));
  EXPECT_THAT(GetAllP4TableEntryKeys(mock_p4rt_table_),
              ContainerEq(std::vector<std::string>{"TABLE:{key}"}));
}

class AppDbManagerTest : public AppDbP4TableEntryTest {
 public:
  void SetUp() override {
    AppDbP4TableEntryTest::SetUp();

    mock_p4rt_table_.producer =
        std::make_unique<FakeZmqProducerStateTableAdapter>(&fake_p4rt_table_);
    mock_p4rt_table_.app_db =
        std::make_unique<FakeTableAdapter>(&fake_p4rt_table_, "P4RT_TABLE");

    mock_vrf_table_ = {
        .producer_state =
            std::make_unique<FakeProducerStateTableAdapter>(&fake_vrf_table_),
        .notification_consumer =
            std::make_unique<FakeConsumerNotifierAdapter>(&fake_vrf_table_),
        .app_db = std::make_unique<FakeTableAdapter>(&fake_vrf_table_, "VRF"),
        .app_state_db = std::make_unique<sonic::FakeTableAdapter>(
            &fake_vrf_state_table_, "VRF"),
    };
  }

 protected:
  FakeSonicDbTable fake_p4rt_table_;
  FakeSonicDbTable fake_vrf_table_;
  FakeSonicDbTable fake_vrf_state_table_;
};

TEST_F(AppDbManagerTest, InsertVrfTableEntry) {
  pdpi::IrEntity entity;
  ASSERT_TRUE(TextFormat::ParseFromString(R"pb(table_entry {
                                                 table_name: "vrf_table"
                                                 matches {
                                                   name: "vrf_id"
                                                   exact { str: "vrf-1" }
                                                 }
                                                 action { name: "no_action" }
                                               })pb",
                                          &entity));

  ASSERT_OK_AND_ASSIGN(
      auto update,
      CreateAppDbUpdate(p4::v1::Update::INSERT, entity,
                        sai::GetIrP4Info(sai::Instantiation::kMiddleblock)));
  pdpi::IrUpdateStatus status;
  ASSERT_OK(PerformAppDbUpdates(mock_p4rt_table_, mock_vrf_table_,
                                {{update, &status}}));
  EXPECT_THAT(status, EqualsProto("code: OK"));
  EXPECT_THAT(GetAllAppDbVrfTableEntries(mock_vrf_table_),
              IsOkAndHolds(ElementsAre(EqualsProto(entity.table_entry()))));
}

TEST_F(AppDbManagerTest, DeleteVrfTableEntry) {
  pdpi::IrEntity entity;
  ASSERT_TRUE(TextFormat::ParseFromString(R"pb(table_entry {
                                                 table_name: "vrf_table"
                                                 matches {
                                                   name: "vrf_id"
                                                   exact { str: "vrf-1" }
                                                 }
                                                 action { name: "no_action" }
                                               })pb",
                                          &entity));

  ASSERT_OK_AND_ASSIGN(
      auto insert_update,
      CreateAppDbUpdate(p4::v1::Update::INSERT, entity,
                        sai::GetIrP4Info(sai::Instantiation::kMiddleblock)));
  ASSERT_OK_AND_ASSIGN(
      auto delete_update,
      CreateAppDbUpdate(p4::v1::Update::DELETE, entity,
                        sai::GetIrP4Info(sai::Instantiation::kMiddleblock)));
  pdpi::IrUpdateStatus insert_status, delete_status;
  ASSERT_OK(PerformAppDbUpdates(mock_p4rt_table_, mock_vrf_table_,
                                {
                                    {insert_update, &insert_status},
                                    {delete_update, &delete_status},
                                }));
  EXPECT_THAT(insert_status, EqualsProto("code: OK"));
  EXPECT_THAT(delete_status, EqualsProto("code: OK"));
  EXPECT_THAT(GetAllAppDbVrfTableEntries(mock_vrf_table_),
              IsOkAndHolds(IsEmpty()));
}

TEST_F(AppDbManagerTest, ModifyVrfTableEntry) {
  pdpi::IrEntity entity;
  ASSERT_TRUE(TextFormat::ParseFromString(R"pb(table_entry {
                                                 table_name: "vrf_table"
                                                 matches {
                                                   name: "vrf_id"
                                                   exact { str: "vrf-1" }
                                                 }
                                                 action { name: "no_action" }
                                               })pb",
                                          &entity));
  EXPECT_THAT(
      CreateAppDbUpdate(p4::v1::Update::MODIFY, entity,
                        sai::GetIrP4Info(sai::Instantiation::kMiddleblock))
          .status(),
      StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_F(AppDbManagerTest, InsertPacketReplicationEngineEntry) {
  pdpi::IrEntity entity;
  ASSERT_TRUE(
      TextFormat::ParseFromString(R"pb(packet_replication_engine_entry {
                                         multicast_group_entry {
                                           multicast_group_id: 1
                                           replicas { port: "1" instance: 0 }
                                           replicas { port: "2" instance: 0 }
                                         }
                                       })pb",
                                  &entity));
  ASSERT_OK_AND_ASSIGN(
      auto update,
      CreateAppDbUpdate(p4::v1::Update::INSERT, entity,
                        sai::GetIrP4Info(sai::Instantiation::kMiddleblock)));
  pdpi::IrUpdateStatus status;
  ASSERT_OK(PerformAppDbUpdates(mock_p4rt_table_, mock_vrf_table_,
                                {{update, &status}}));
  EXPECT_THAT(status, EqualsProto("code: OK"));
  EXPECT_THAT(GetAllAppDbPacketReplicationTableEntries(mock_p4rt_table_),
              IsOkAndHolds(ElementsAre(
                  EqualsProto(entity.packet_replication_engine_entry()))));
}

TEST_F(AppDbManagerTest, DeletePacketReplicationEngineEntry) {
  pdpi::IrEntity entity;
  ASSERT_TRUE(
      TextFormat::ParseFromString(R"pb(packet_replication_engine_entry {
                                         multicast_group_entry {
                                           multicast_group_id: 1
                                           replicas { port: "1" instance: 0 }
                                           replicas { port: "2" instance: 0 }
                                         }
                                       })pb",
                                  &entity));
  ASSERT_OK_AND_ASSIGN(
      auto insert_update,
      CreateAppDbUpdate(p4::v1::Update::INSERT, entity,
                        sai::GetIrP4Info(sai::Instantiation::kMiddleblock)));
  pdpi::IrUpdateStatus insert_status, delete_status;
  ASSERT_OK(PerformAppDbUpdates(mock_p4rt_table_, mock_vrf_table_,
                                {{insert_update, &insert_status}}));
  EXPECT_THAT(insert_status, EqualsProto("code: OK"));

  ASSERT_OK_AND_ASSIGN(
      auto delete_update,
      CreateAppDbUpdate(p4::v1::Update::DELETE, entity,
                        sai::GetIrP4Info(sai::Instantiation::kMiddleblock)));
  ASSERT_OK(PerformAppDbUpdates(mock_p4rt_table_, mock_vrf_table_,
                                {{delete_update, &delete_status}}));
  EXPECT_THAT(delete_status, EqualsProto("code: OK"));
  EXPECT_THAT(GetAllAppDbPacketReplicationTableEntries(mock_p4rt_table_),
              IsOkAndHolds(IsEmpty()));
}

TEST_F(AppDbManagerTest, ModifyPacketReplicationEngineEntry) {
  pdpi::IrEntity entity;
  ASSERT_TRUE(
      TextFormat::ParseFromString(R"pb(packet_replication_engine_entry {
                                         multicast_group_entry {
                                           multicast_group_id: 1
                                           replicas { port: "1" instance: 0 }
                                           replicas { port: "2" instance: 0 }
                                         }
                                       })pb",
                                  &entity));
  ASSERT_OK_AND_ASSIGN(
      auto insert_update,
      CreateAppDbUpdate(p4::v1::Update::INSERT, entity,
                        sai::GetIrP4Info(sai::Instantiation::kMiddleblock)));

  pdpi::IrUpdateStatus insert_status;
  ASSERT_OK(PerformAppDbUpdates(mock_p4rt_table_, mock_vrf_table_,
                                {{insert_update, &insert_status}}));
  EXPECT_THAT(insert_status, EqualsProto("code: OK"));

  pdpi::IrEntity modified_entity;
  ASSERT_TRUE(
      TextFormat::ParseFromString(R"pb(packet_replication_engine_entry {
                                         multicast_group_entry {
                                           multicast_group_id: 1
                                           replicas { port: "3" instance: 1 }
                                           replicas { port: "4" instance: 2 }
                                         }
                                       })pb",
                                  &modified_entity));
  ASSERT_OK_AND_ASSIGN(
      auto modify_update,
      CreateAppDbUpdate(p4::v1::Update::MODIFY, modified_entity,
                        sai::GetIrP4Info(sai::Instantiation::kMiddleblock)));

  pdpi::IrUpdateStatus modify_status;
  ASSERT_OK(PerformAppDbUpdates(mock_p4rt_table_, mock_vrf_table_,
                                {{modify_update, &modify_status}}));
  EXPECT_THAT(modify_status, EqualsProto("code: OK"));

  EXPECT_THAT(GetAllAppDbPacketReplicationTableEntries(mock_p4rt_table_),
              IsOkAndHolds(ElementsAre(EqualsProto(
                  modified_entity.packet_replication_engine_entry()))));
}

TEST_F(AppDbManagerTest, InsertP4rtTableEntry) {
  pdpi::IrEntity entity;
  ASSERT_TRUE(
      TextFormat::ParseFromString(R"pb(
                                    table_entry {
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
                                    })pb",
                                  &entity));
  ASSERT_OK_AND_ASSIGN(
      auto update,
      CreateAppDbUpdate(p4::v1::Update::INSERT, entity,
                        sai::GetIrP4Info(sai::Instantiation::kMiddleblock)));
  pdpi::IrUpdateStatus status;
  ASSERT_OK(PerformAppDbUpdates(mock_p4rt_table_, mock_vrf_table_,
                                {{update, &status}}));
  EXPECT_THAT(status, EqualsProto("code: OK"));
  auto keys = GetAllP4TableEntryKeys(mock_p4rt_table_);
  ASSERT_THAT(keys, SizeIs(1));
  EXPECT_THAT(ReadP4TableEntry(
                  mock_p4rt_table_,
                  sai::GetIrP4Info(sai::Instantiation::kMiddleblock), keys[0]),
              IsOkAndHolds(EqualsProto(entity.table_entry())));
}

TEST_F(AppDbManagerTest, DeleteP4rtTableEntry) {
  pdpi::IrEntity entity;
  ASSERT_TRUE(
      TextFormat::ParseFromString(R"pb(
                                    table_entry {
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
                                    })pb",
                                  &entity));
  ASSERT_OK_AND_ASSIGN(
      auto insert_update,
      CreateAppDbUpdate(p4::v1::Update::INSERT, entity,
                        sai::GetIrP4Info(sai::Instantiation::kMiddleblock)));
  pdpi::IrUpdateStatus insert_status, delete_status;
  ASSERT_OK(PerformAppDbUpdates(mock_p4rt_table_, mock_vrf_table_,
                                {{insert_update, &insert_status}}));
  EXPECT_THAT(insert_status, EqualsProto("code: OK"));

  ASSERT_OK_AND_ASSIGN(
      auto delete_update,
      CreateAppDbUpdate(p4::v1::Update::DELETE, entity,
                        sai::GetIrP4Info(sai::Instantiation::kMiddleblock)));
  ASSERT_OK(PerformAppDbUpdates(mock_p4rt_table_, mock_vrf_table_,
                                {{delete_update, &delete_status}}));
  EXPECT_THAT(delete_status, EqualsProto("code: OK"));

  EXPECT_THAT(GetAllP4TableEntryKeys(mock_p4rt_table_), IsEmpty());
}

TEST_F(AppDbManagerTest, ModifyP4rtTableEntry) {
  pdpi::IrEntity entity;
  ASSERT_TRUE(
      TextFormat::ParseFromString(R"pb(
                                    table_entry {
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
                                    })pb",
                                  &entity));
  ASSERT_OK_AND_ASSIGN(
      auto insert_update,
      CreateAppDbUpdate(p4::v1::Update::INSERT, entity,
                        sai::GetIrP4Info(sai::Instantiation::kMiddleblock)));
  pdpi::IrUpdateStatus insert_status;
  ASSERT_OK(PerformAppDbUpdates(mock_p4rt_table_, mock_vrf_table_,
                                {{insert_update, &insert_status}}));
  EXPECT_THAT(insert_status, EqualsProto("code: OK"));

  pdpi::IrUpdateStatus modify_status;
  pdpi::IrEntity modified_entity = entity;
  modified_entity.mutable_table_entry()
      ->mutable_action()
      ->mutable_params(0)
      ->mutable_value()
      ->set_str("Ethernet1/2");
  ASSERT_OK_AND_ASSIGN(
      auto modify_update,
      CreateAppDbUpdate(p4::v1::Update::MODIFY, modified_entity,
                        sai::GetIrP4Info(sai::Instantiation::kMiddleblock)));
  ASSERT_OK(PerformAppDbUpdates(mock_p4rt_table_, mock_vrf_table_,
                                {{modify_update, &modify_status}}));
  EXPECT_THAT(modify_status, EqualsProto("code: OK"));

  auto keys = GetAllP4TableEntryKeys(mock_p4rt_table_);
  ASSERT_THAT(keys, SizeIs(1));
  EXPECT_THAT(ReadP4TableEntry(
                  mock_p4rt_table_,
                  sai::GetIrP4Info(sai::Instantiation::kMiddleblock), keys[0]),
              IsOkAndHolds(EqualsProto(modified_entity.table_entry())));
}

TEST_F(AppDbManagerTest, PerformAppDbUpdatesFailsOnFirstP4rtTableError) {
  std::vector<pdpi::IrUpdateStatus> results(10);
  std::vector<std::pair<AppDbUpdate, pdpi::IrUpdateStatus*>> updates = {
      {{.table = AppDbTableType::VRF_TABLE,
        .update = {"VRF_TABLE|KEY0", SET_COMMAND, {{}}}},
       &results[0]},
      {{.table = AppDbTableType::P4RT,
        .update = {"P4RT_TABLE|Key0", SET_COMMAND, {{}}}},
       &results[1]},
      {{.table = AppDbTableType::P4RT,
        .update = {"P4RT_TABLE|Key1", SET_COMMAND, {{}}}},
       &results[2]},
      {{.table = AppDbTableType::VRF_TABLE,
        .update = {"VRF_TABLE|KEY1", SET_COMMAND, {{}}}},
       &results[3]},
      {{.table = AppDbTableType::P4RT,
        .update = {"P4RT_TABLE|Key2", SET_COMMAND, {{}}}},
       &results[4]},
      {{.table = AppDbTableType::P4RT,
        .update = {"P4RT_TABLE|Key3", DEL_COMMAND, {{}}}},  // Fail here
       &results[5]},
      {{.table = AppDbTableType::VRF_TABLE,
        .update = {"VRF_TABLE|KEY2", SET_COMMAND, {{}}}},
       &results[6]},
      {{.table = AppDbTableType::VRF_TABLE,
        .update = {"VRF_TABLE|KEY3", SET_COMMAND, {{}}}},
       &results[7]},
      {{.table = AppDbTableType::P4RT,
        .update = {"P4RT_TABLE|Key5", SET_COMMAND, {{}}}},
       &results[8]},
      {{.table = AppDbTableType::P4RT,
        .update = {"P4RT_TABLE|Key6", SET_COMMAND, {{}}}},
       &results[9]},
  };
  fake_p4rt_table_.SetResponseForKey("P4RT_TABLE|Key3", "SWSS_RC_NOT_FOUND",
                                     "Test error");
  EXPECT_OK(PerformAppDbUpdates(mock_p4rt_table_, mock_vrf_table_, updates));

  EXPECT_THAT(
      results,
      ElementsAre(HasErrorCode(kRpcOk),        // VRF_TABLE|KEY0
                  HasErrorCode(kRpcOk),        // P4RT_TABLE|Key0
                  HasErrorCode(kRpcOk),        // P4RT_TABLE|Key1
                  HasErrorCode(kRpcOk),        // VRF_TABLE|KEY1
                  HasErrorCode(kRpcOk),        // P4RT_TABLE|KEY2
                  HasErrorCode(kRpcNotFound),  // P4RT_TABLE|Key3 (Failure)
                  HasErrorCode(kRpcAborted), HasErrorCode(kRpcAborted),
                  HasErrorCode(kRpcAborted), HasErrorCode(kRpcAborted)));
}

TEST_F(AppDbManagerTest, PerformAppDbUpdatesFailsOnFirstVrfTableError) {
  std::vector<pdpi::IrUpdateStatus> results(10);
  std::vector<std::pair<AppDbUpdate, pdpi::IrUpdateStatus*>> updates = {
      {{.table = AppDbTableType::VRF_TABLE,
        .update = {"VRF_TABLE|KEY0", SET_COMMAND, {{}}}},
       &results[0]},
      {{.table = AppDbTableType::P4RT,
        .update = {"P4RT_TABLE|Key0", SET_COMMAND, {{}}}},
       &results[1]},
      {{.table = AppDbTableType::P4RT,
        .update = {"P4RT_TABLE|Key1", SET_COMMAND, {{}}}},
       &results[2]},
      {{.table = AppDbTableType::VRF_TABLE,
        .update = {"VRF_TABLE|KEY1", SET_COMMAND, {{}}}},
       &results[3]},
      {{.table = AppDbTableType::P4RT,
        .update = {"P4RT_TABLE|Key2", SET_COMMAND, {{}}}},
       &results[4]},
      {{.table = AppDbTableType::P4RT,
        .update = {"P4RT_TABLE|Key3", SET_COMMAND, {{}}}},
       &results[5]},
      {{.table = AppDbTableType::VRF_TABLE,
        .update = {"VRF_TABLE|KEY2", SET_COMMAND, {{}}}},  // Fail here
       &results[6]},
      {{.table = AppDbTableType::VRF_TABLE,
        .update = {"VRF_TABLE|KEY3", SET_COMMAND, {{}}}},
       &results[7]},
      {{.table = AppDbTableType::P4RT,
        .update = {"P4RT_TABLE|Key5", SET_COMMAND, {{}}}},
       &results[8]},
      {{.table = AppDbTableType::P4RT,
        .update = {"P4RT_TABLE|Key6", SET_COMMAND, {{}}}},
       &results[9]},
  };
  fake_vrf_table_.SetResponseForKey("VRF_TABLE|KEY2", "SWSS_RC_INTERNAL",
                                    "Test error");

  EXPECT_OK(PerformAppDbUpdates(mock_p4rt_table_, mock_vrf_table_, updates));

  EXPECT_THAT(
      results,
      ElementsAre(HasErrorCode(kRpcOk),        // VRF_TABLE|KEY0
                  HasErrorCode(kRpcOk),        // P4RT_TABLE|Key0
                  HasErrorCode(kRpcOk),        // P4RT_TABLE|Key1
                  HasErrorCode(kRpcOk),        // VRF_TABLE|KEY1
                  HasErrorCode(kRpcOk),        // P4RT_TABLE|KEY2
                  HasErrorCode(kRpcOk),        // P4RT_TABLE|Key3
                  HasErrorCode(kRpcInternal),  // VRF_TABLE|KEY2 (Failure)
                  HasErrorCode(kRpcAborted), HasErrorCode(kRpcAborted),
                  HasErrorCode(kRpcAborted)));
}

TEST(AppDbUpdateTest, EqualsSelf) {
  AppDbUpdate update;
  update.table = AppDbTableType::P4RT;
  kfvOp(update.update) = SET_COMMAND;
  kfvKey(update.update) = "update_key";
  kfvFieldsValues(update.update) = {
      {"field_a", "value_a"},
      {"field_b", "value_b"},
      {"field_c", "value_c"},
  };
  EXPECT_TRUE(update == update);
  EXPECT_FALSE(update != update);
}

TEST(AppDbUpdateTest, TableDiffDoesNotEqual) {
  AppDbUpdate update;
  update.table = AppDbTableType::P4RT;
  kfvOp(update.update) = SET_COMMAND;
  kfvKey(update.update) = "update_key";
  kfvFieldsValues(update.update) = {
      {"field_a", "value_a"},
      {"field_b", "value_b"},
      {"field_c", "value_c"},
  };

  AppDbUpdate update2 = update;
  update2.table = AppDbTableType::VRF_TABLE;

  EXPECT_FALSE(update == update2);
  EXPECT_FALSE(update2 == update);
  EXPECT_TRUE(update != update2);
  EXPECT_TRUE(update2 != update);
}

TEST(AppDbUpdateTest, OpDiffDoesNotEqual) {
  AppDbUpdate update;
  update.table = AppDbTableType::P4RT;
  kfvOp(update.update) = SET_COMMAND;
  kfvKey(update.update) = "update_key";
  kfvFieldsValues(update.update) = {
      {"field_a", "value_a"},
      {"field_b", "value_b"},
      {"field_c", "value_c"},
  };

  AppDbUpdate update2 = update;
  kfvOp(update2.update) = DEL_COMMAND;

  EXPECT_FALSE(update == update2);
  EXPECT_FALSE(update2 == update);
  EXPECT_TRUE(update != update2);
  EXPECT_TRUE(update2 != update);
}

TEST(AppDbUpdateTest, KeyDiffDoesNotEqual) {
  AppDbUpdate update;
  update.table = AppDbTableType::P4RT;
  kfvOp(update.update) = SET_COMMAND;
  kfvKey(update.update) = "update_key";
  kfvFieldsValues(update.update) = {
      {"field_a", "value_a"},
      {"field_b", "value_b"},
      {"field_c", "value_c"},
  };

  AppDbUpdate update2 = update;
  kfvKey(update2.update) = "update2_key";

  EXPECT_FALSE(update == update2);
  EXPECT_FALSE(update2 == update);
  EXPECT_TRUE(update != update2);
  EXPECT_TRUE(update2 != update);
}

TEST(AppDbUpdateTest, FieldCountDiffDoesNotEqual) {
  AppDbUpdate update;
  update.table = AppDbTableType::P4RT;
  kfvOp(update.update) = SET_COMMAND;
  kfvKey(update.update) = "update_key";
  kfvFieldsValues(update.update) = {
      {"field_a", "value_a"},
      {"field_b", "value_b"},
      {"field_c", "value_c"},
  };

  AppDbUpdate update2 = update;
  kfvFieldsValues(update2.update).push_back({"field_c", "value_c"});

  EXPECT_FALSE(update == update2);
  EXPECT_FALSE(update2 == update);
  EXPECT_TRUE(update != update2);
  EXPECT_TRUE(update2 != update);
}

TEST(AppDbUpdateTest, FieldDiffDoesNotEqual) {
  AppDbUpdate update;
  update.table = AppDbTableType::P4RT;
  kfvOp(update.update) = SET_COMMAND;
  kfvKey(update.update) = "update_key";
  kfvFieldsValues(update.update) = {
      {"field_a", "value_a"},
      {"field_b", "value_b"},
      {"field_c", "value_c"},
  };

  AppDbUpdate update2 = update;
  kfvFieldsValues(update2.update)[1].first = "field_d";

  EXPECT_FALSE(update == update2);
  EXPECT_FALSE(update2 == update);
  EXPECT_TRUE(update != update2);
  EXPECT_TRUE(update2 != update);
}

TEST(AppDbUpdateTest, ValueDiffDoesNotEqual) {
  AppDbUpdate update;
  update.table = AppDbTableType::P4RT;
  kfvOp(update.update) = SET_COMMAND;
  kfvKey(update.update) = "update_key";
  kfvFieldsValues(update.update) = {
      {"field_a", "value_a"},
      {"field_b", "value_b"},
      {"field_c", "value_c"},
  };

  AppDbUpdate update2 = update;
  kfvFieldsValues(update2.update)[1].second = "value_c";

  EXPECT_FALSE(update == update2);
  EXPECT_FALSE(update2 == update);
  EXPECT_TRUE(update != update2);
  EXPECT_TRUE(update2 != update);
}

}  // namespace
}  // namespace sonic
}  // namespace p4rt_app
