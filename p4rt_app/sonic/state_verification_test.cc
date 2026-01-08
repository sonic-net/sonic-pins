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
#include "p4rt_app/sonic/state_verification.h"

#include <memory>
#include <unordered_map>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "gmock/gmock.h"
#include "google/protobuf/text_format.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status_matchers.h"
#include "p4rt_app/sonic/adapters/mock_consumer_notifier_adapter.h"
#include "p4rt_app/sonic/adapters/mock_notification_producer_adapter.h"
#include "p4rt_app/sonic/adapters/mock_table_adapter.h"
#include "p4rt_app/sonic/redis_connections.h"

namespace p4rt_app {
namespace sonic {
namespace {

using ::google::protobuf::TextFormat;
using ::testing::ElementsAre;
using ::testing::Eq;
using ::testing::HasSubstr;
using ::testing::IsEmpty;
using ::testing::Return;

using ListOfKeys = std::vector<std::string>;
using ListOfValues = std::vector<std::pair<std::string, std::string>>;

class StateVerificationPacketReplicationTest : public ::testing::Test {
 protected:
  StateVerificationPacketReplicationTest() {
    auto p4rt_app_db = std::make_unique<MockTableAdapter>();
    auto p4rt_counter_db = std::make_unique<MockTableAdapter>();

    // Save a pointer so we can test against the mocks.
    mock_p4rt_app_db_ = p4rt_app_db.get();

    mock_p4rt_table_ = P4rtTable{
        .app_db = std::move(p4rt_app_db),
        .counter_db = std::move(p4rt_counter_db),
    };
  }

  // Mock AppDb tables.
  MockTableAdapter* mock_p4rt_app_db_;
  P4rtTable mock_p4rt_table_;
};

TEST(StateVerificationTest, VerifyStateMatches) {
  MockTableAdapter mock_app_state_db;
  MockTableAdapter mock_app_db;

  // Read 2 keys from the AppDb and AppStateDb. Order should not matter.
  EXPECT_CALL(mock_app_db, keys).WillOnce(Return(ListOfKeys{"key1", "key0"}));
  EXPECT_CALL(mock_app_state_db, keys)
      .WillOnce(Return(ListOfKeys{"key0", "key1"}));

  // Because the key0 matches we'll read the full entry from both DBs.
  EXPECT_CALL(mock_app_db, get("key0"))
      .WillOnce(
          Return(ListOfValues{{"field1", "value1"}, {"field0", "value0"}}));
  EXPECT_CALL(mock_app_state_db, get("key0"))
      .WillOnce(
          Return(ListOfValues{{"field0", "value0"}, {"field1", "value1"}}));

  // Because the key1 matches we'll read the full entry from both DBs.
  EXPECT_CALL(mock_app_db, get("key1"))
      .WillOnce(
          Return(ListOfValues{{"field11", "value11"}, {"field10", "value10"}}));
  EXPECT_CALL(mock_app_state_db, get("key1"))
      .WillOnce(
          Return(ListOfValues{{"field10", "value10"}, {"field11", "value11"}}));

  // Because everything matches the state verification should return no errors.
  EXPECT_THAT(VerifyAppStateDbAndAppDbEntries(mock_app_state_db, mock_app_db),
              IsEmpty());
}

TEST(StateVerificationTest, MissingEntryInAppDbFails) {
  MockTableAdapter mock_app_state_db;
  MockTableAdapter mock_app_db;

  // Read only 1 key from the AppDb and 2 keys from the AppStateDb.
  EXPECT_CALL(mock_app_db, keys).WillOnce(Return(ListOfKeys{"key1"}));
  EXPECT_CALL(mock_app_db, get("key1"))
      .WillOnce(
          Return(ListOfValues{{"field1", "value1"}, {"field0", "value0"}}));

  EXPECT_CALL(mock_app_state_db, keys)
      .WillOnce(Return(ListOfKeys{"key0", "key1"}));
  EXPECT_CALL(mock_app_state_db, get("key0"))
      .WillOnce(Return(ListOfValues{{}}));
  EXPECT_CALL(mock_app_state_db, get("key1"))
      .WillOnce(
          Return(ListOfValues{{"field0", "value0"}, {"field1", "value1"}}));

  // Because of the missing key we should return 1 failure.
  EXPECT_THAT(VerifyAppStateDbAndAppDbEntries(mock_app_state_db, mock_app_db),
              ElementsAre(HasSubstr("AppDb is missing key")));
}

TEST(StateVerificationTest, MissingEntryInAppStateDbFails) {
  MockTableAdapter mock_app_state_db;
  MockTableAdapter mock_app_db;

  // Read 2 key from the AppDb and only 1 key from the AppStateDb.
  EXPECT_CALL(mock_app_db, keys).WillOnce(Return(ListOfKeys{"key0", "key1"}));
  EXPECT_CALL(mock_app_db, get("key0")).WillOnce(Return(ListOfValues{{}}));
  EXPECT_CALL(mock_app_db, get("key1"))
      .WillOnce(
          Return(ListOfValues{{"field1", "value1"}, {"field0", "value0"}}));

  EXPECT_CALL(mock_app_state_db, keys).WillOnce(Return(ListOfKeys{"key1"}));
  EXPECT_CALL(mock_app_state_db, get("key1"))
      .WillOnce(
          Return(ListOfValues{{"field0", "value0"}, {"field1", "value1"}}));

  // Because of the missing key we should return 1 failure.
  EXPECT_THAT(VerifyAppStateDbAndAppDbEntries(mock_app_state_db, mock_app_db),
              ElementsAre(HasSubstr("AppStateDb is missing key")));
}

TEST(StateVerificationTest, MissingFieldInAppDbEntryFails) {
  MockTableAdapter mock_app_state_db;
  MockTableAdapter mock_app_db;

  // Read the same key from the AppDb and AppStateDb.
  EXPECT_CALL(mock_app_db, keys).WillOnce(Return(ListOfKeys{"key0"}));
  EXPECT_CALL(mock_app_state_db, keys).WillOnce(Return(ListOfKeys{"key0"}));

  // However, the AppDb entry has 1 less field value.
  EXPECT_CALL(mock_app_db, get("key0"))
      .WillOnce(Return(ListOfValues{{"field1", "value1"}}));
  EXPECT_CALL(mock_app_state_db, get("key0"))
      .WillOnce(
          Return(ListOfValues{{"field0", "value0"}, {"field1", "value1"}}));

  // Because of the missing field we should return 1 failure.
  EXPECT_THAT(VerifyAppStateDbAndAppDbEntries(mock_app_state_db, mock_app_db),
              ElementsAre(HasSubstr("do not match")));
}

TEST(StateVerificationTest, ExtraFieldInAppDbEntryFails) {
  MockTableAdapter mock_app_state_db;
  MockTableAdapter mock_app_db;

  // Read the same key from the AppDb and AppStateDb.
  EXPECT_CALL(mock_app_db, keys).WillOnce(Return(ListOfKeys{"key0"}));
  EXPECT_CALL(mock_app_state_db, keys).WillOnce(Return(ListOfKeys{"key0"}));

  // However, the AppDb entry has 1 more field value.
  EXPECT_CALL(mock_app_db, get("key0"))
      .WillOnce(
          Return(ListOfValues{{"field0", "value0"}, {"field1", "value1"}}));
  EXPECT_CALL(mock_app_state_db, get("key0"))
      .WillOnce(Return(ListOfValues{{"field1", "value1"}}));

  // Because of the extra field we should return 1 failure.
  EXPECT_THAT(VerifyAppStateDbAndAppDbEntries(mock_app_state_db, mock_app_db),
              ElementsAre(HasSubstr("do not match")));
}

TEST(StateVerificationTest, MismatchFieldInEntryFails) {
  MockTableAdapter mock_app_state_db;
  MockTableAdapter mock_app_db;

  // Read the same key from the AppDb and AppStateDb.
  EXPECT_CALL(mock_app_db, keys).WillOnce(Return(ListOfKeys{"key0"}));
  EXPECT_CALL(mock_app_state_db, keys).WillOnce(Return(ListOfKeys{"key0"}));

  // However, the entries have different fields.
  EXPECT_CALL(mock_app_db, get("key0"))
      .WillOnce(Return(ListOfValues{{"field0", "value"}}));
  EXPECT_CALL(mock_app_state_db, get("key0"))
      .WillOnce(Return(ListOfValues{{"field1", "value"}}));

  // Because of the mismatched field names we should return 1 failure
  EXPECT_THAT(VerifyAppStateDbAndAppDbEntries(mock_app_state_db, mock_app_db),
              ElementsAre(HasSubstr("do not match")));
}

TEST(StateVerificationTest, DifferentFieldValuesInEntryFails) {
  MockTableAdapter mock_app_state_db;
  MockTableAdapter mock_app_db;

  // Read the same key from the AppDb and AppStateDb.
  EXPECT_CALL(mock_app_db, keys).WillOnce(Return(ListOfKeys{"key0"}));
  EXPECT_CALL(mock_app_state_db, keys).WillOnce(Return(ListOfKeys{"key0"}));

  // However, the entries have different values.
  EXPECT_CALL(mock_app_db, get("key0"))
      .WillOnce(Return(ListOfValues{{"field", "value0"}}));
  EXPECT_CALL(mock_app_state_db, get("key0"))
      .WillOnce(Return(ListOfValues{{"field", "value1"}}));

  // Because of the differing field values we should return 1 failure.
  EXPECT_THAT(VerifyAppStateDbAndAppDbEntries(mock_app_state_db, mock_app_db),
              ElementsAre(HasSubstr("do not match")));
}

TEST(StateVerificationTest, DuplicateAppDbFieldNameInEntryFails) {
  MockTableAdapter mock_app_state_db;
  MockTableAdapter mock_app_db;

  // Read the same key from the AppDb and AppStateDb.
  EXPECT_CALL(mock_app_db, keys).WillOnce(Return(ListOfKeys{"key0"}));
  EXPECT_CALL(mock_app_state_db, keys).WillOnce(Return(ListOfKeys{"key0"}));

  // However, the AppDb entry has 2 fields with the same name.
  EXPECT_CALL(mock_app_db, get("key0"))
      .WillOnce(Return(ListOfValues{{"field", "value0"}, {"field", "value1"}}));
  EXPECT_CALL(mock_app_state_db, get("key0"))
      .WillOnce(Return(ListOfValues{{"field", "value0"}}));

  // Because of the differing field values we should return 1 failure.
  EXPECT_THAT(VerifyAppStateDbAndAppDbEntries(mock_app_state_db, mock_app_db),
              ElementsAre(HasSubstr("AppDb has duplicate fields")));
}

TEST(StateVerificationTest, DuplicateAppStateDbFieldNameInEntryFails) {
  MockTableAdapter mock_app_state_db;
  MockTableAdapter mock_app_db;

  // Read the same key from the AppDb and AppStateDb.
  EXPECT_CALL(mock_app_db, keys).WillOnce(Return(ListOfKeys{"key0"}));
  EXPECT_CALL(mock_app_state_db, keys).WillOnce(Return(ListOfKeys{"key0"}));

  // However, the AppStateDb entry has 2 fields with the same name.
  EXPECT_CALL(mock_app_db, get("key0"))
      .WillOnce(Return(ListOfValues{{"field", "value0"}}));
  EXPECT_CALL(mock_app_state_db, get("key0"))
      .WillOnce(Return(ListOfValues{{"field", "value0"}, {"field", "value1"}}));

  // Because of the differing field values we should return 1 failure.
  EXPECT_THAT(VerifyAppStateDbAndAppDbEntries(mock_app_state_db, mock_app_db),
              ElementsAre(HasSubstr("AppStateDb has duplicate fields")));
}

TEST_F(StateVerificationPacketReplicationTest,
       PacketReplicationEntriesIgnoredByP4rtTable) {
  MockTableAdapter mock_app_db;
  pdpi::IrP4Info ir_p4_info;

  pdpi::IrEntity ir_entity;
  ASSERT_TRUE(TextFormat::ParseFromString(
      R"pb(packet_replication_engine_entry {
             multicast_group_entry {
               multicast_group_id: 1
               replicas { port: "Ethernet0" instance: 0 }
             }
           })pb",
      &ir_entity));

  const std::string app_db_key1 = "REPLICATION_IP_MULTICAST_TABLE:0x0001";

  EXPECT_EQ(
      VerifyP4rtTableWithCacheEntities(mock_app_db, {ir_entity}, ir_p4_info)
          .size(),
      0);
}

TEST_F(StateVerificationPacketReplicationTest, VerifyPacketReplicationSuccess) {
  const std::string json_array1 =
      R"j([{"multicast_replica_instance":"0x0001",)j"
      R"j("multicast_replica_port":"Ethernet1/1/1"},)j"
      R"j({"multicast_replica_instance":"0x0001",)j"
      R"j("multicast_replica_port":"Ethernet1/1/3"}])j";
  const std::string app_db_key1 = "REPLICATION_IP_MULTICAST_TABLE:0x0001";
  const std::vector<std::pair<std::string, std::string>> kfv_values1 = {
      std::make_pair("replicas", json_array1),
  };

  EXPECT_CALL(*mock_p4rt_app_db_, keys)
      .WillOnce(Return(std::vector<std::string>{app_db_key1}));
  EXPECT_CALL(*mock_p4rt_app_db_, get(Eq(app_db_key1)))
      .WillOnce(Return(kfv_values1));

  pdpi::IrEntity ir_entity;
  ASSERT_TRUE(TextFormat::ParseFromString(
      R"pb(packet_replication_engine_entry {
             multicast_group_entry {
               multicast_group_id: 1
               replicas { port: "Ethernet1/1/1" instance: 1 }
               replicas { port: "Ethernet1/1/3" instance: 1 }
             }
           })pb",
      &ir_entity));
  EXPECT_EQ(
      VerifyPacketReplicationWithCacheEntities(mock_p4rt_table_, {ir_entity})
          .size(),
      0);
}

TEST_F(StateVerificationPacketReplicationTest, VerifyPacketReplicationFails) {
  const std::string json_array1 =
      R"j([{"multicast_replica_instance":"0x0001",)j"
      R"j("multicast_replica_port":"Ethernet1/1/1"}])j";
  const std::string app_db_key1 = "REPLICATION_IP_MULTICAST_TABLE:0x0001";
  const std::vector<std::pair<std::string, std::string>> kfv_values1 = {
      std::make_pair("replicas", json_array1),
  };

  EXPECT_CALL(*mock_p4rt_app_db_, keys)
      .WillOnce(Return(std::vector<std::string>{app_db_key1}));
  EXPECT_CALL(*mock_p4rt_app_db_, get(Eq(app_db_key1)))
      .WillOnce(Return(kfv_values1));

  pdpi::IrEntity ir_entity;
  ASSERT_TRUE(TextFormat::ParseFromString(
      R"pb(packet_replication_engine_entry {
             multicast_group_entry {
               multicast_group_id: 1
               replicas { port: "Ethernet1/1/1" instance: 1 }
               replicas { port: "Ethernet1/1/3" instance: 1 }
             }
           })pb",
      &ir_entity));

  auto result =
      VerifyPacketReplicationWithCacheEntities(mock_p4rt_table_, {ir_entity});
  ASSERT_THAT(result.size(), 1);
  EXPECT_EQ(result.at(0),
            "APP DB is missing replica Ethernet1/1/3_1 for group id 1");
}

}  // namespace
}  // namespace sonic
}  // namespace p4rt_app
