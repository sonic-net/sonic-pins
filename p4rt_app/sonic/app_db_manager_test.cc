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

#include <map>
#include <memory>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/memory/memory.h"
#include "absl/status/statusor.h"
#include "glog/logging.h"
#include "google/protobuf/text_format.h"
#include "google/rpc/code.pb.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4rt_app/sonic/adapters/mock_consumer_notifier_adapter.h"
#include "p4rt_app/sonic/adapters/mock_producer_state_table_adapter.h"
#include "p4rt_app/sonic/adapters/mock_table_adapter.h"
#include "p4rt_app/sonic/redis_connections.h"
#include "p4rt_app/tests/lib/app_db_entry_builder.h"
#include "p4rt_app/utils/table_utility.h"
#include "sai_p4/instantiations/google/sai_p4info.h"

namespace p4rt_app {
namespace sonic {
namespace {

using ::google::protobuf::TextFormat;
using ::gutil::EqualsProto;
using ::gutil::StatusIs;
using ::p4rt_app::test_lib::AppDbEntryBuilder;
using ::testing::ContainerEq;
using ::testing::DoAll;
using ::testing::Eq;
using ::testing::Return;
using ::testing::SetArgReferee;

const std::vector<std::pair<std::string, std::string>>&
GetSuccessfulResponseValues() {
  static const std::vector<std::pair<std::string, std::string>>* const
      kResponse = new std::vector<std::pair<std::string, std::string>>{
          {"err_str", "SWSS_RC_SUCCESS"}};
  return *kResponse;
}

class AppDbManagerTest : public ::testing::Test {
 protected:
  AppDbManagerTest() {
    auto p4rt_producer_state =
        std::make_unique<MockProducerStateTableAdapter>();
    auto p4rt_notifier = std::make_unique<MockConsumerNotifierAdapter>();
    auto p4rt_app_db = std::make_unique<MockTableAdapter>();
    auto p4rt_app_state_db = std::make_unique<MockTableAdapter>();
    auto p4rt_counter_db = std::make_unique<MockTableAdapter>();

    // Save a pointer so we can test against the mocks.
    mock_p4rt_producer_state_ = p4rt_producer_state.get();
    mock_p4rt_notifier_ = p4rt_notifier.get();
    mock_p4rt_app_db_ = p4rt_app_db.get();
    mock_p4rt_app_state_db_ = p4rt_app_state_db.get();
    mock_p4rt_counter_db_ = p4rt_counter_db.get();

    mock_p4rt_table_ = P4rtTable{
        .producer_state = std::move(p4rt_producer_state),
        .notifier = std::move(p4rt_notifier),
        .app_db = std::move(p4rt_app_db),
        .app_state_db = std::move(p4rt_app_state_db),
        .counter_db = std::move(p4rt_counter_db),
    };
  }

  // Mock AppDb tables.
  MockProducerStateTableAdapter* mock_p4rt_producer_state_;
  MockConsumerNotifierAdapter* mock_p4rt_notifier_;
  MockTableAdapter* mock_p4rt_app_db_;
  MockTableAdapter* mock_p4rt_app_state_db_;
  MockTableAdapter* mock_p4rt_counter_db_;
  P4rtTable mock_p4rt_table_;
};

TEST_F(AppDbManagerTest, InsertTableEntry) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(
      TextFormat::ParseFromString(R"pb(
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
                                    })pb",
                                  &table_entry));
  AppDbUpdates updates;
  updates.entries.push_back(AppDbEntry{
      .rpc_index = 0,
      .entry = table_entry,
      .update_type = p4::v1::Update::INSERT,
      .appdb_table = AppDbTableType::P4RT,
  });
  updates.total_rpc_updates = 1;

  // Expected RedisDB entry.
  const auto expected = AppDbEntryBuilder{}
                            .SetTableName("FIXED_ROUTER_INTERFACE_TABLE")
                            .SetPriority(123)
                            .AddMatchField("router_interface_id", "16")
                            .SetAction("set_port_and_src_mac")
                            .AddActionParam("port", "Ethernet28/5")
                            .AddActionParam("src_mac", "00:02:03:04:05:06");
  const std::vector<swss::KeyOpFieldsValuesTuple> expected_key_value = {
      std::make_tuple(expected.GetKey(), "", expected.GetValueList())};
  EXPECT_CALL(*mock_p4rt_producer_state_, batch_set(expected_key_value))
      .Times(1);

  // Expected OrchAgent response.
  EXPECT_CALL(*mock_p4rt_notifier_, WaitForNotificationAndPop)
      .WillOnce(DoAll(SetArgReferee<0>("SWSS_RC_SUCCESS"),
                      SetArgReferee<1>(expected.GetKey()),
                      SetArgReferee<2>(GetSuccessfulResponseValues()),
                      Return(true)));

  pdpi::IrWriteResponse response;
  response.add_statuses();
  EXPECT_OK(UpdateAppDb(mock_p4rt_table_, updates,
                        sai::GetIrP4Info(sai::Instantiation::kMiddleblock),
                        &response));
  ASSERT_EQ(response.statuses_size(), 1);
  EXPECT_EQ(response.statuses(0).code(), google::rpc::OK);
}

TEST_F(AppDbManagerTest, InsertWithUnknownAppDbTableTypeFails) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(
      TextFormat::ParseFromString(R"pb(
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
                                    })pb",
                                  &table_entry));

  // The appdb_table value is set to unknown.
  AppDbUpdates updates;
  updates.entries.push_back(AppDbEntry{
      .rpc_index = 0,
      .entry = table_entry,
      .update_type = p4::v1::Update::INSERT,
      .appdb_table = AppDbTableType::UNKNOWN,
  });
  updates.total_rpc_updates = 1;

  pdpi::IrWriteResponse response;
  EXPECT_THAT(UpdateAppDb(mock_p4rt_table_, updates,
                          sai::GetIrP4Info(sai::Instantiation::kMiddleblock),
                          &response),
              StatusIs(absl::StatusCode::kInternal));
}

TEST_F(AppDbManagerTest, InsertDuplicateTableEntryFails) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(
      TextFormat::ParseFromString(R"pb(
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
                                    })pb",
                                  &table_entry));
  AppDbUpdates updates;
  updates.entries.push_back(AppDbEntry{
      .rpc_index = 0,
      .entry = table_entry,
      .update_type = p4::v1::Update::INSERT,
      .appdb_table = AppDbTableType::P4RT,
  });
  updates.total_rpc_updates = 1;

  // RedisDB returns that the entry already exists.
  const auto expected = AppDbEntryBuilder{}
                            .SetTableName("FIXED_ROUTER_INTERFACE_TABLE")
                            .SetPriority(123)
                            .AddMatchField("router_interface_id", "16");
  EXPECT_CALL(*mock_p4rt_app_db_, exists(Eq(expected.GetKey())))
      .WillOnce(Return(true));

  pdpi::IrWriteResponse response;
  response.add_statuses();
  EXPECT_OK(UpdateAppDb(mock_p4rt_table_, updates,
                        sai::GetIrP4Info(sai::Instantiation::kMiddleblock),
                        &response));
  EXPECT_EQ(response.statuses(0).code(), google::rpc::ALREADY_EXISTS);
}

TEST_F(AppDbManagerTest, ModifyTableEntry) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(
      TextFormat::ParseFromString(R"pb(
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
                                    })pb",
                                  &table_entry));
  AppDbUpdates updates;
  updates.entries.push_back(AppDbEntry{
      .rpc_index = 0,
      .entry = table_entry,
      .update_type = p4::v1::Update::MODIFY,
      .appdb_table = AppDbTableType::P4RT,
  });
  updates.total_rpc_updates = 1;

  const auto expected = AppDbEntryBuilder{}
                            .SetTableName("FIXED_ROUTER_INTERFACE_TABLE")
                            .SetPriority(123)
                            .AddMatchField("router_interface_id", "16")
                            .SetAction("set_port_and_src_mac")
                            .AddActionParam("port", "Ethernet28/5")
                            .AddActionParam("src_mac", "00:02:03:04:05:06");

  // RedisDB returns that the entry exists so it can be modified.
  const std::vector<swss::KeyOpFieldsValuesTuple> expected_key_value = {
      std::make_tuple(expected.GetKey(), "", expected.GetValueList())};
  EXPECT_CALL(*mock_p4rt_app_db_, exists(expected.GetKey()))
      .WillOnce(Return(true));
  EXPECT_CALL(*mock_p4rt_app_db_,
              batch_del(std::vector<std::string>{expected.GetKey()}))
      .Times(1);
  EXPECT_CALL(*mock_p4rt_producer_state_, batch_set(expected_key_value))
      .Times(1);

  // OrchAgent returns success.
  EXPECT_CALL(*mock_p4rt_notifier_, WaitForNotificationAndPop)
      .WillOnce(DoAll(SetArgReferee<0>("SWSS_RC_SUCCESS"),
                      SetArgReferee<1>(expected.GetKey()),
                      SetArgReferee<2>(GetSuccessfulResponseValues()),
                      Return(true)));

  pdpi::IrWriteResponse response;
  response.add_statuses();
  EXPECT_OK(UpdateAppDb(mock_p4rt_table_, updates,
                        sai::GetIrP4Info(sai::Instantiation::kMiddleblock),
                        &response));
  ASSERT_EQ(response.statuses_size(), 1);
  EXPECT_EQ(response.statuses(0).code(), google::rpc::OK);
}

TEST_F(AppDbManagerTest, ModifyNonExistentTableEntryFails) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(
      TextFormat::ParseFromString(R"pb(
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
                                    })pb",
                                  &table_entry));
  AppDbUpdates updates;
  updates.entries.push_back(AppDbEntry{
      .rpc_index = 0,
      .entry = table_entry,
      .update_type = p4::v1::Update::MODIFY,
      .appdb_table = AppDbTableType::P4RT,
  });
  updates.total_rpc_updates = 1;

  // RedisDB returns that the entry does not exists.
  const auto expected = AppDbEntryBuilder{}
                            .SetTableName("FIXED_ROUTER_INTERFACE_TABLE")
                            .SetPriority(123)
                            .AddMatchField("router_interface_id", "16");
  EXPECT_CALL(*mock_p4rt_app_db_, exists(Eq(expected.GetKey())))
      .WillOnce(Return(false));

  pdpi::IrWriteResponse response;
  response.add_statuses();
  EXPECT_OK(UpdateAppDb(mock_p4rt_table_, updates,
                        sai::GetIrP4Info(sai::Instantiation::kMiddleblock),
                        &response));
  EXPECT_EQ(response.statuses(0).code(), google::rpc::NOT_FOUND);
}

TEST_F(AppDbManagerTest, DeleteTableEntry) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(
      TextFormat::ParseFromString(R"pb(
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
                                    })pb",
                                  &table_entry));
  AppDbUpdates updates;
  updates.entries.push_back(AppDbEntry{
      .rpc_index = 0,
      .entry = table_entry,
      .update_type = p4::v1::Update::DELETE,
      .appdb_table = AppDbTableType::P4RT,
  });
  updates.total_rpc_updates = 1;

  const auto expected = AppDbEntryBuilder{}
                            .SetTableName("FIXED_ROUTER_INTERFACE_TABLE")
                            .SetPriority(123)
                            .AddMatchField("router_interface_id", "16");

  // RedisDB returns that the entry exists so it can be deleted.
  EXPECT_CALL(*mock_p4rt_app_db_, exists(expected.GetKey()))
      .WillOnce(Return(true));
  EXPECT_CALL(*mock_p4rt_producer_state_,
              batch_del(std::vector<std::string>{expected.GetKey()}))
      .Times(1);

  // OrchAgent returns success.
  EXPECT_CALL(*mock_p4rt_notifier_, WaitForNotificationAndPop)
      .WillOnce(DoAll(SetArgReferee<0>("SWSS_RC_SUCCESS"),
                      SetArgReferee<1>(expected.GetKey()),
                      SetArgReferee<2>(GetSuccessfulResponseValues()),
                      Return(true)));

  pdpi::IrWriteResponse response;
  response.add_statuses();
  EXPECT_OK(UpdateAppDb(mock_p4rt_table_, updates,
                        sai::GetIrP4Info(sai::Instantiation::kMiddleblock),
                        &response));
  ASSERT_EQ(response.statuses_size(), 1);
  EXPECT_EQ(response.statuses(0).code(), google::rpc::OK);
}

TEST_F(AppDbManagerTest, DeleteNonExistentTableEntryFails) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(
      TextFormat::ParseFromString(R"pb(
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
                                    })pb",
                                  &table_entry));
  AppDbUpdates updates;
  updates.entries.push_back(AppDbEntry{
      .rpc_index = 0,
      .entry = table_entry,
      .update_type = p4::v1::Update::DELETE,
      .appdb_table = AppDbTableType::P4RT,
  });
  updates.total_rpc_updates = 1;

  // RedisDB returns that the entry does not exists.
  const auto expected = AppDbEntryBuilder{}
                            .SetTableName("FIXED_ROUTER_INTERFACE_TABLE")
                            .SetPriority(123)
                            .AddMatchField("router_interface_id", "16");
  EXPECT_CALL(*mock_p4rt_app_db_, exists(Eq(expected.GetKey())))
      .WillOnce(Return(false));

  pdpi::IrWriteResponse response;
  response.add_statuses();
  EXPECT_OK(UpdateAppDb(mock_p4rt_table_, updates,
                        sai::GetIrP4Info(sai::Instantiation::kMiddleblock),
                        &response));
  EXPECT_EQ(response.statuses(0).code(), google::rpc::NOT_FOUND);
}

TEST_F(AppDbManagerTest, ReadAppStateDbP4TableEntryWithoutCounterData) {
  const auto app_db_entry = AppDbEntryBuilder{}
                                .SetTableName("FIXED_ROUTER_INTERFACE_TABLE")
                                .SetPriority(123)
                                .AddMatchField("router_interface_id", "16")
                                .SetAction("set_port_and_src_mac")
                                .AddActionParam("port", "Ethernet28/5")
                                .AddActionParam("src_mac", "00:02:03:04:05:06");

  EXPECT_CALL(*mock_p4rt_app_state_db_, get(Eq(app_db_entry.GetKey())))
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

TEST_F(AppDbManagerTest, ReadAppStateDbP4TableEntryWithCounterData) {
  const auto app_db_entry = AppDbEntryBuilder{}
                                .SetTableName("FIXED_ROUTER_INTERFACE_TABLE")
                                .SetPriority(123)
                                .AddMatchField("router_interface_id", "16")
                                .SetAction("set_port_and_src_mac")
                                .AddActionParam("port", "Ethernet28/5")
                                .AddActionParam("src_mac", "00:02:03:04:05:06");

  EXPECT_CALL(*mock_p4rt_app_state_db_, get(Eq(app_db_entry.GetKey())))
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
                counter_data {
                  byte_count: 1152921504606846975
                  packet_count: 1076078835964837887
                })pb"));
}

TEST_F(AppDbManagerTest, ReadAppStateDbP4TableEntryIgnoresInvalidCounterData) {
  const auto app_db_entry = AppDbEntryBuilder{}
                                .SetTableName("FIXED_ROUTER_INTERFACE_TABLE")
                                .SetPriority(123)
                                .AddMatchField("router_interface_id", "16")
                                .SetAction("set_port_and_src_mac")
                                .AddActionParam("port", "Ethernet28/5")
                                .AddActionParam("src_mac", "00:02:03:04:05:06");

  EXPECT_CALL(*mock_p4rt_app_state_db_, get(Eq(app_db_entry.GetKey())))
      .WillOnce(Return(app_db_entry.GetValueList()));

  EXPECT_CALL(*mock_p4rt_counter_db_, get(app_db_entry.GetKey()))
      .WillOnce(Return(std::vector<std::pair<std::string, std::string>>{
          {"packets", "A"}, {"bytes", "B"}}));

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

TEST_F(AppDbManagerTest, GetAllP4KeysReturnsInstalledKeys) {
  EXPECT_CALL(*mock_p4rt_app_state_db_, keys)
      .WillOnce(Return(std::vector<std::string>{"TABLE:{key}"}));

  EXPECT_THAT(GetAllP4TableEntryKeys(mock_p4rt_table_),
              ContainerEq(std::vector<std::string>{"TABLE:{key}"}));
}

}  // namespace
}  // namespace sonic
}  // namespace p4rt_app
