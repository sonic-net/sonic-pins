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
#include "p4rt_app/sonic/packet_replication_entry_translation.h"

#include <memory>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "gmock/gmock.h"
#include "google/protobuf/text_format.h"
#include "google/rpc/code.pb.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status_matchers.h"  // IWYU pragma: keep
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4rt_app/sonic/adapters/mock_consumer_notifier_adapter.h"
#include "p4rt_app/sonic/adapters/mock_notification_producer_adapter.h"
#include "p4rt_app/sonic/adapters/mock_table_adapter.h"
#include "p4rt_app/sonic/redis_connections.h"
#include "swss/rediscommand.h"

namespace p4rt_app {
namespace sonic {
namespace {

using ::google::protobuf::TextFormat;
using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::testing::ContainerEq;
using ::testing::Eq;
using ::testing::IsEmpty;
using ::testing::Return;
using ::testing::UnorderedElementsAre;

class PacketReplicationEntryTranslationTest : public ::testing::Test {
 protected:
  PacketReplicationEntryTranslationTest() {
    auto pre_app_db = std::make_unique<MockTableAdapter>();
    auto pre_counter_db = std::make_unique<MockTableAdapter>();

    // Save a pointer so we can test against the mocks.
    mock_pre_app_db_ = pre_app_db.get();
    mock_pre_counter_db_ = pre_counter_db.get();

    mock_p4rt_table_ = P4rtTable{
        .app_db = std::move(pre_app_db),
        .counter_db = std::move(pre_counter_db),
    };
  }

  MockTableAdapter* mock_pre_app_db_;
  MockTableAdapter* mock_pre_counter_db_;
  P4rtTable mock_p4rt_table_;
};

TEST_F(PacketReplicationEntryTranslationTest, InsertPacketReplicationEntry) {
  pdpi::IrPacketReplicationEngineEntry pre_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(
      R"pb(multicast_group_entry {
             multicast_group_id: 1
             replicas { port: "Ethernet1/1/1" instance: 1 }
             replicas { port: "Ethernet3/1/1" instance: 1 }
             replicas { port: "Ethernet5/1/1" instance: 1 }
           })pb",
      &pre_entry));

  // Expected RedisDB entry.
  const std::string json_array =
      R"j([{"multicast_replica_instance":"0x0001",)j"
      R"j("multicast_replica_port":"Ethernet1/1/1"},)j"
      R"j({"multicast_replica_instance":"0x0001",)j"
      R"j("multicast_replica_port":"Ethernet3/1/1"},)j"
      R"j({"multicast_replica_instance":"0x0001",)j"
      R"j("multicast_replica_port":"Ethernet5/1/1"}])j";

  const std::vector<std::pair<std::string, std::string>> kfv_values = {
      std::make_pair("replicas", json_array),
  };
  const std::string expected_key = "REPLICATION_IP_MULTICAST_TABLE:0x0001";
  swss::KeyOpFieldsValuesTuple expected_key_value =
      std::make_tuple(expected_key, "SET", kfv_values);

  ASSERT_THAT(CreateAppDbPacketReplicationTableUpdate(p4::v1::Update::INSERT,
                                                      pre_entry),
              IsOkAndHolds(expected_key_value));
}

TEST_F(PacketReplicationEntryTranslationTest, ModifyPacketReplicationEntry) {
  pdpi::IrPacketReplicationEngineEntry pre_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(
      R"pb(multicast_group_entry {
             multicast_group_id: 1
             replicas { port: "Ethernet1/1/1" instance: 1 }
             replicas { port: "Ethernet3/1/1" instance: 1 }
           })pb",
      &pre_entry));

  // Expected RedisDB entry.
  const std::string json_array =
      R"j([{"multicast_replica_instance":"0x0001",)j"
      R"j("multicast_replica_port":"Ethernet1/1/1"},)j"
      R"j({"multicast_replica_instance":"0x0001",)j"
      R"j("multicast_replica_port":"Ethernet3/1/1"}])j";

  const std::vector<std::pair<std::string, std::string>> kfv_values = {
      std::make_pair("replicas", json_array),
  };
  const std::string expected_key = "REPLICATION_IP_MULTICAST_TABLE:0x0001";
  swss::KeyOpFieldsValuesTuple expected_key_value =
      std::make_tuple(expected_key, "SET", kfv_values);

  ASSERT_THAT(CreateAppDbPacketReplicationTableUpdate(p4::v1::Update::INSERT,
                                                      pre_entry),
              IsOkAndHolds(expected_key_value));
}

TEST_F(PacketReplicationEntryTranslationTest, DeletePacketReplicationEntry) {
  pdpi::IrPacketReplicationEngineEntry pre_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(
      R"pb(multicast_group_entry {
             multicast_group_id: 1
             replicas { port: "Ethernet1/1/1" instance: 1 }
             replicas { port: "Ethernet3/1/1" instance: 1 }
           })pb",
      &pre_entry));

  // Expected RedisDB entry.
  const std::vector<std::pair<std::string, std::string>> empty_values;
  const std::string expected_key = "REPLICATION_IP_MULTICAST_TABLE:0x0001";
  swss::KeyOpFieldsValuesTuple expected_key_value = std::make_tuple(
      "REPLICATION_IP_MULTICAST_TABLE:0x0001", "DEL", empty_values);

  ASSERT_THAT(CreateAppDbPacketReplicationTableUpdate(p4::v1::Update::DELETE,
                                                      pre_entry),
              IsOkAndHolds(expected_key_value));
}

TEST_F(PacketReplicationEntryTranslationTest, UnspecifiedOperationFails) {
  pdpi::IrPacketReplicationEngineEntry pre_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(
      R"pb(multicast_group_entry {
             multicast_group_id: 1
             replicas { port: "Ethernet1/1/1" instance: 1 }
           })pb",
      &pre_entry));

  // Expected RedisDB entry.
  const std::vector<std::pair<std::string, std::string>> empty_values;
  swss::KeyOpFieldsValuesTuple expected_key_value = std::make_tuple(
      "REPLICATION_IP_MULTICAST_TABLE:0x0001", "SET", empty_values);

  EXPECT_THAT(CreateAppDbPacketReplicationTableUpdate(
                  p4::v1::Update::UNSPECIFIED, pre_entry),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_F(PacketReplicationEntryTranslationTest,
       GetAllPacketReplicationTableEntryKeys) {
  EXPECT_CALL(*mock_pre_app_db_, keys)
      .WillOnce(Return(
          std::vector<std::string>{"REPLICATION_IP_MULTICAST_TABLE:{key1}",
                                   "REPLICATION_IP_MULTICAST_TABLE:{key2}"}));

  EXPECT_THAT(GetAllPacketReplicationTableEntryKeys(mock_p4rt_table_),
              ContainerEq(std::vector<std::string>{
                  "REPLICATION_IP_MULTICAST_TABLE:{key1}",
                  "REPLICATION_IP_MULTICAST_TABLE:{key2}"}));
}

TEST_F(PacketReplicationEntryTranslationTest,
       GetAllAppDbPacketReplicationTableEntries) {
  const std::string json_array1 =
      R"j([{"multicast_replica_instance":"0x0001",)j"
      R"j("multicast_replica_port":"Ethernet1/1/1"},)j"
      R"j({"multicast_replica_instance":"0x0001",)j"
      R"j("multicast_replica_port":"Ethernet3/1/1"}])j";
  const std::string app_db_key1 = "REPLICATION_IP_MULTICAST_TABLE:0x0001";
  const std::vector<std::pair<std::string, std::string>> kfv_values1 = {
      std::make_pair("replicas", json_array1),
  };

  const std::string json_array2 =
      R"j([{"multicast_replica_instance":"0x0001",)j"
      R"j("multicast_replica_port":"Ethernet1/1/1"}])j";
  const std::string app_db_key2 = "REPLICATION_IP_MULTICAST_TABLE:0x0002";
  const std::vector<std::pair<std::string, std::string>> kfv_values2 = {
      std::make_pair("replicas", json_array2),
  };

  EXPECT_CALL(*mock_pre_app_db_, keys)
      .WillOnce(Return(std::vector<std::string>{app_db_key1, app_db_key2}));
  EXPECT_CALL(*mock_pre_app_db_, get(Eq(app_db_key1)))
      .WillOnce(Return(kfv_values1));
  EXPECT_CALL(*mock_pre_app_db_, get(Eq(app_db_key2)))
      .WillOnce(Return(kfv_values2));

  EXPECT_THAT(GetAllAppDbPacketReplicationTableEntries(mock_p4rt_table_),
              IsOkAndHolds(UnorderedElementsAre(
                  EqualsProto(R"pb(
                    multicast_group_entry {
                      multicast_group_id: 1
                      replicas { port: "Ethernet1/1/1" instance: 1 }
                      replicas { port: "Ethernet3/1/1" instance: 1 }
                    })pb"),
                  EqualsProto(R"pb(
                    multicast_group_entry {
                      multicast_group_id: 2
                      replicas { port: "Ethernet1/1/1" instance: 1 }
                    })pb"))));
}

TEST_F(PacketReplicationEntryTranslationTest, InvalidTableName) {
  const std::string bad_app_db_key =
      "FIXED_MULTICAST_ROUTER_INTERFACE_TABLE:0x1";

  EXPECT_CALL(*mock_pre_app_db_, keys)
      .WillOnce(Return(std::vector<std::string>{bad_app_db_key}));

  EXPECT_THAT(GetAllAppDbPacketReplicationTableEntries(mock_p4rt_table_),
              IsOkAndHolds(IsEmpty()));
}

TEST_F(PacketReplicationEntryTranslationTest, InvalidMulticastGroupId) {
  const std::string bad_app_db_key = "REPLICATION_IP_MULTICAST_TABLE:0xzz";

  EXPECT_CALL(*mock_pre_app_db_, keys)
      .WillOnce(Return(std::vector<std::string>{bad_app_db_key}));

  EXPECT_FALSE(GetAllAppDbPacketReplicationTableEntries(mock_p4rt_table_).ok());
}

TEST_F(PacketReplicationEntryTranslationTest, InvalidInstance) {
  const std::string json_array1 =
      R"j([{"multicast_replica_instance":"0xZZ",)j"
      R"j("multicast_replica_port":"Ethernet1/1/1"},)j"
      R"j({"multicast_replica_instance":"0x0001",)j"
      R"j("multicast_replica_port":"Ethernet3/1/1"}])j";
  const std::string app_db_key1 = "REPLICATION_IP_MULTICAST_TABLE:0x0001";
  const std::vector<std::pair<std::string, std::string>> kfv_values1 = {
      std::make_pair("replicas", json_array1),
  };

  EXPECT_CALL(*mock_pre_app_db_, keys)
      .WillOnce(Return(std::vector<std::string>{app_db_key1}));
  EXPECT_CALL(*mock_pre_app_db_, get(Eq(app_db_key1)))
      .WillOnce(Return(kfv_values1));

  EXPECT_FALSE(GetAllAppDbPacketReplicationTableEntries(mock_p4rt_table_).ok());
}

TEST_F(PacketReplicationEntryTranslationTest, MissingMulticastReplicaPort) {
  const std::string json_array1 =
      R"j([{"multicast_replica_instance":"0x0001"}])j";
  const std::string app_db_key1 = "REPLICATION_IP_MULTICAST_TABLE:0x0001";
  const std::vector<std::pair<std::string, std::string>> kfv_values1 = {
      std::make_pair("replicas", json_array1),
  };

  EXPECT_CALL(*mock_pre_app_db_, keys)
      .WillOnce(Return(std::vector<std::string>{app_db_key1}));
  EXPECT_CALL(*mock_pre_app_db_, get(Eq(app_db_key1)))
      .WillOnce(Return(kfv_values1));

  EXPECT_FALSE(GetAllAppDbPacketReplicationTableEntries(mock_p4rt_table_).ok());
}

TEST_F(PacketReplicationEntryTranslationTest, MissingMulticastReplicaInstance) {
  const std::string json_array1 =
      R"j([{"multicast_replica_port":"Ethernet1/1/1"}])j";
  const std::string app_db_key1 = "REPLICATION_IP_MULTICAST_TABLE:0x0001";
  const std::vector<std::pair<std::string, std::string>> kfv_values1 = {
      std::make_pair("replicas", json_array1),
  };

  EXPECT_CALL(*mock_pre_app_db_, keys)
      .WillOnce(Return(std::vector<std::string>{app_db_key1}));
  EXPECT_CALL(*mock_pre_app_db_, get(Eq(app_db_key1)))
      .WillOnce(Return(kfv_values1));

  EXPECT_FALSE(GetAllAppDbPacketReplicationTableEntries(mock_p4rt_table_).ok());
}

TEST_F(PacketReplicationEntryTranslationTest, CompareEntriesSuccess) {
  pdpi::IrEntity entity;
  ASSERT_TRUE(TextFormat::ParseFromString(
      R"pb(
        packet_replication_engine_entry {
          multicast_group_entry {
            multicast_group_id: 1
            replicas { port: "Ethernet0" instance: 0 }
            replicas { port: "Ethernet1" instance: 0 }
          }
        })pb",
      &entity));

  std::vector<pdpi::IrEntity> input = {entity};
  EXPECT_THAT(ComparePacketReplicationTableEntries(input, input).size(), 0);
}

TEST_F(PacketReplicationEntryTranslationTest, CompareEntriesMissingId) {
  pdpi::IrEntity entity1;
  ASSERT_TRUE(TextFormat::ParseFromString(
      R"pb(
        packet_replication_engine_entry {
          multicast_group_entry {
            multicast_group_id: 1
            replicas { port: "Ethernet0" instance: 0 }
          }
        })pb",
      &entity1));
  pdpi::IrEntity entity2;
  ASSERT_TRUE(TextFormat::ParseFromString(
      R"pb(
        packet_replication_engine_entry {
          multicast_group_entry {
            multicast_group_id: 2
            replicas { port: "Ethernet0" instance: 0 }
          }
        })pb",
      &entity2));

  std::vector<pdpi::IrEntity> input1 = {entity1};
  std::vector<pdpi::IrEntity> input2 = {entity2};
  auto result = ComparePacketReplicationTableEntries(input1, input2);
  ASSERT_THAT(result.size(), 2);
  EXPECT_EQ(result.at(0),
            "Packet replication cache is missing multicast group ID 1");
  EXPECT_EQ(result.at(1), "APP DB is missing multicast group ID 2");
}

TEST_F(PacketReplicationEntryTranslationTest, CompareEntriesMissingId2) {
  pdpi::IrEntity entity1;
  ASSERT_TRUE(TextFormat::ParseFromString(
      R"pb(
        packet_replication_engine_entry {
          multicast_group_entry {
            multicast_group_id: 1
            replicas { port: "Ethernet0" instance: 0 }
          }
        })pb",
      &entity1));
  pdpi::IrEntity entity2;
  ASSERT_TRUE(TextFormat::ParseFromString(
      R"pb(
        packet_replication_engine_entry {
          multicast_group_entry {
            multicast_group_id: 1
            replicas { port: "Ethernet0" instance: 0 }
          }
        })pb",
      &entity2));
  pdpi::IrEntity entity3;
  ASSERT_TRUE(TextFormat::ParseFromString(
      R"pb(
        packet_replication_engine_entry {
          multicast_group_entry {
            multicast_group_id: 2
            replicas { port: "Ethernet0" instance: 0 }
          }
        })pb",
      &entity3));

  std::vector<pdpi::IrEntity> input1 = {entity1};
  std::vector<pdpi::IrEntity> input2 = {entity2, entity3};
  auto result = ComparePacketReplicationTableEntries(input1, input2);
  ASSERT_THAT(result.size(), 1);
  EXPECT_EQ(result.at(0), "APP DB is missing multicast group ID 2");
}

TEST_F(PacketReplicationEntryTranslationTest, CompareEntriesDifferentReplica) {
  pdpi::IrEntity entity1;
  ASSERT_TRUE(TextFormat::ParseFromString(
      R"pb(
        packet_replication_engine_entry {
          multicast_group_entry {
            multicast_group_id: 1
            replicas { port: "Ethernet0" instance: 0 }
          }
        })pb",
      &entity1));
  pdpi::IrEntity entity2;
  ASSERT_TRUE(TextFormat::ParseFromString(
      R"pb(
        packet_replication_engine_entry {
          multicast_group_entry {
            multicast_group_id: 1
            replicas { port: "Ethernet0" instance: 1 }
          }
        })pb",
      &entity2));

  std::vector<pdpi::IrEntity> input1 = {entity1};
  std::vector<pdpi::IrEntity> input2 = {entity2};
  auto result = ComparePacketReplicationTableEntries(input1, input2);
  ASSERT_THAT(result.size(), 2);
  EXPECT_EQ(
      result.at(0),
      "Packet replication cache is missing replica Ethernet0_0 for group id 1");
  EXPECT_EQ(result.at(1),
            "APP DB is missing replica Ethernet0_1 for group id 1");
}

}  // namespace
}  // namespace sonic
}  // namespace p4rt_app
