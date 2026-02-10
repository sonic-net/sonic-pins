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
#include "p4_infra/p4_pdpi/entity_keys.h"

#include <sstream>

#include "absl/hash/hash_testing.h"
#include "absl/strings/match.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status_matchers.h"  // IWYU pragma: keep

namespace pdpi {
namespace {

using ::p4::v1::Entity;
using ::p4::v1::FieldMatch;
using ::p4::v1::PacketReplicationEngineEntry;
using ::p4::v1::TableEntry;
using ::testing::HasSubstr;

TEST(EntityKeyTest, UnsupportedEntityTypeCannotBeBuilt) {
  Entity entry;
  auto statusor = EntityKey::MakeEntityKey(entry);
  ASSERT_FALSE(statusor.ok());
}

TEST(EntityKeyTest, DefaultConstructorSuccess) {
  EntityKey key;
  std::stringstream msg;
  msg << key;
  EXPECT_TRUE(absl::StrContains(msg.str(), "0"));
}

TEST(EntityKeyTest, TableEntityKeyEqualsItself) {
  ASSERT_OK_AND_ASSIGN(TableEntry entry, gutil::ParseTextProto<TableEntry>(R"pb(
                         table_id: 42
                         idle_timeout_ns: 7
                       )pb"));
  EntityKey key_a(entry);
  EXPECT_TRUE(key_a == key_a);
  EXPECT_FALSE(key_a != key_a);
}

TEST(EntityKeyTest, PacketReplicationEntityKeyEqualsItself) {
  ASSERT_OK_AND_ASSIGN(Entity entry, gutil::ParseTextProto<Entity>(R"pb(
                         packet_replication_engine_entry {
                           multicast_group_entry {
                             multicast_group_id: 5
                             replicas { port: "Ethernet0" instance: 1 }
                           }
                         }
                       )pb"));
  ASSERT_OK_AND_ASSIGN(EntityKey key_a, EntityKey::MakeEntityKey(entry));
  EXPECT_TRUE(key_a == key_a);
  EXPECT_FALSE(key_a != key_a);
}

TEST(EntityKeyTest, TableKeysAreEqual) {
  ASSERT_OK_AND_ASSIGN(TableEntry entry, gutil::ParseTextProto<TableEntry>(R"pb(
                         table_id: 42
                         match { field_id: 60 }
                       )pb"));
  EntityKey key_a(entry);

  ASSERT_OK_AND_ASSIGN(Entity entry2, gutil::ParseTextProto<Entity>(R"pb(
                         table_entry {
                           table_id: 42
                           match { field_id: 60 }
                         }
                       )pb"));
  ASSERT_OK_AND_ASSIGN(EntityKey key_b, EntityKey::MakeEntityKey(entry2));

  EXPECT_TRUE(key_a == key_b);
  EXPECT_FALSE(key_a != key_b);
  EXPECT_FALSE(key_a < key_b && key_b < key_a);
}

TEST(EntityKeyTest, TrivialLessThan) {
  ASSERT_OK_AND_ASSIGN(Entity entry, gutil::ParseTextProto<Entity>(R"pb(
                         table_entry { table_id: 42 idle_timeout_ns: 7 }
                       )pb"));
  ASSERT_OK_AND_ASSIGN(EntityKey key_a, EntityKey::MakeEntityKey(entry));
  EXPECT_FALSE(key_a < key_a);

  ASSERT_OK_AND_ASSIGN(Entity entry2, gutil::ParseTextProto<Entity>(R"pb(
                         packet_replication_engine_entry {
                           multicast_group_entry {
                             multicast_group_id: 5
                             replicas { port: "Ethernet0" instance: 1 }
                           }
                         }
                       )pb"));
  ASSERT_OK_AND_ASSIGN(EntityKey key_b, EntityKey::MakeEntityKey(entry2));

  ASSERT_OK_AND_ASSIGN(Entity entry3, gutil::ParseTextProto<Entity>(R"pb(
                         packet_replication_engine_entry {
                           multicast_group_entry { multicast_group_id: 3 }
                         }
                       )pb"));
  ASSERT_OK_AND_ASSIGN(EntityKey key_c, EntityKey::MakeEntityKey(entry3));

  EXPECT_FALSE(key_b < key_b);
  EXPECT_TRUE(key_b < key_a || key_a < key_b);
  EXPECT_TRUE(key_b < key_c || key_c < key_b);
}

TEST(EntityKeyTest, TableEntryNotEqualToPacketReplicationEngineEntry) {
  ASSERT_OK_AND_ASSIGN(TableEntry entry, gutil::ParseTextProto<TableEntry>(R"pb(
                         table_id: 42
                         match { field_id: 60 }
                       )pb"));
  EntityKey key_a(entry);

  ASSERT_OK_AND_ASSIGN(Entity entry2, gutil::ParseTextProto<Entity>(R"pb(
                         packet_replication_engine_entry {
                           multicast_group_entry {
                             multicast_group_id: 5
                             replicas { port: "Ethernet0" instance: 1 }
                           }
                         }
                       )pb"));
  ASSERT_OK_AND_ASSIGN(EntityKey key_b, EntityKey::MakeEntityKey(entry2));

  EXPECT_NE(key_a, key_b);
  EXPECT_FALSE(key_a == key_b);
  EXPECT_TRUE(key_a != key_b);
  EXPECT_TRUE(key_b < key_a || key_a < key_b);
}

TEST(EntityKeyTest, TestDebugOutput) {
  ASSERT_OK_AND_ASSIGN(Entity entry, gutil::ParseTextProto<Entity>(R"pb(
                         packet_replication_engine_entry {
                           multicast_group_entry {
                             multicast_group_id: 5
                             replicas { port: "Ethernet0" instance: 1 }
                             replicas { port: "Ethernet1" instance: 1 }
                           }
                         }
                       )pb"));
  ASSERT_OK_AND_ASSIGN(EntityKey key_a, EntityKey::MakeEntityKey(entry));
  std::stringstream msg;
  msg << key_a;
  EXPECT_THAT(msg.str(), HasSubstr("5"));

  ASSERT_OK_AND_ASSIGN(Entity entry2, gutil::ParseTextProto<Entity>(R"pb(
                         table_entry {
                           table_id: 42
                           priority: 100
                           match { field_id: 7 }
                         }
                       )pb"));
  ASSERT_OK_AND_ASSIGN(EntityKey key_b, EntityKey::MakeEntityKey(entry2));
  std::stringstream msg2;
  msg2 << key_b;
  EXPECT_THAT(msg2.str(), HasSubstr("42"));
  EXPECT_THAT(msg2.str(), HasSubstr("100"));
  EXPECT_THAT(msg2.str(), HasSubstr("7"));
}

TEST(TableEntryKeyTest, TrivialEquality) {
  TableEntry entry;
  TableEntryKey key_a(entry);
  TableEntryKey key_b(entry);

  EXPECT_EQ(key_a, key_b);
}

TEST(TableEntryKeyTest, DiscardOtherValues) {
  TableEntry entry;
  entry.set_table_id(42);
  entry.set_idle_timeout_ns(7);

  TableEntry entry2;
  entry2.set_table_id(42);
  entry2.set_idle_timeout_ns(8);

  TableEntryKey key_a(entry);
  TableEntryKey key_b(entry2);

  EXPECT_EQ(key_a, key_b);

  TableEntry entry3;
  entry3.set_table_id(42);

  TableEntryKey key_c(entry3);

  EXPECT_EQ(key_a, key_c);
}

TEST(TableEntryKeyTest, Hashing) {
  TableEntry entry;
  entry.set_table_id(42);
  entry.set_idle_timeout_ns(7);

  TableEntryKey key_a(entry);

  entry.set_idle_timeout_ns(8);
  TableEntryKey key_b(entry);

  entry.set_priority(100);

  TableEntryKey key_c(entry);

  FieldMatch* field = entry.add_match();
  field->set_field_id(43);

  TableEntryKey key_d(entry);

  EXPECT_TRUE(absl::VerifyTypeImplementsAbslHashCorrectly(
      /*values = */ {key_a, key_b, key_c}));

  EXPECT_TRUE(absl::VerifyTypeImplementsAbslHashCorrectly(
      /*values = */ {key_a, key_b, key_c}));
}

TEST(TableEntryKeyTest, NotEqualOperator) {
  TableEntry entry;
  entry.set_table_id(42);
  entry.set_priority(1);

  TableEntry entry2;
  entry2.set_table_id(43);
  entry2.set_priority(1);

  TableEntry entry3;
  entry3.set_table_id(43);
  entry3.set_priority(2);

  TableEntry entry4;
  entry4.set_table_id(43);
  entry4.set_priority(2);
  FieldMatch* field4 = entry4.add_match();
  field4->set_field_id(7);

  TableEntry entry5;
  entry5.set_table_id(43);
  entry5.set_priority(2);
  FieldMatch* field5 = entry5.add_match();
  field5->set_field_id(7);
  FieldMatch* field6 = entry5.add_match();
  field6->set_field_id(8);

  TableEntry entry6;
  entry6.set_table_id(43);
  entry6.set_priority(2);
  FieldMatch* field7 = entry6.add_match();
  field7->set_field_id(9);

  TableEntry entry7;
  entry7.set_table_id(42);
  entry7.set_priority(1);

  TableEntryKey key_a(entry);
  TableEntryKey key_b(entry2);
  TableEntryKey key_c(entry3);
  TableEntryKey key_d(entry4);
  TableEntryKey key_e(entry5);
  TableEntryKey key_f(entry6);
  TableEntryKey key_g(entry7);

  EXPECT_FALSE(key_a != key_a);
  EXPECT_TRUE(key_a != key_b);
  EXPECT_TRUE(key_b != key_c);
  EXPECT_FALSE(key_d != key_d);
  EXPECT_TRUE(key_d != key_e);
  EXPECT_TRUE(key_d != key_f);
  EXPECT_TRUE(key_a == key_g);
}

TEST(TableEntryKeyTest, EqualOperator) {
  ASSERT_OK_AND_ASSIGN(TableEntry entry, gutil::ParseTextProto<TableEntry>(R"pb(
                         table_id: 42
                         match { field_id: 60 }
                         match { field_id: 70 }
                       )pb"));
  TableEntryKey key_a(entry);

  ASSERT_OK_AND_ASSIGN(TableEntry entry2,
                       gutil::ParseTextProto<TableEntry>(R"pb(
                         table_id: 42
                         match { field_id: 70 }
                         match { field_id: 60 }
                       )pb"));
  TableEntryKey key_b(entry2);

  EXPECT_TRUE(key_a == key_b);
  EXPECT_FALSE(key_a != key_b);
}

TEST(TableEntryKeyTest, StreamOperator) {
  TableEntry entry;
  entry.set_table_id(43);
  entry.set_priority(2);
  FieldMatch* field1 = entry.add_match();
  field1->set_field_id(7);
  FieldMatch* field2 = entry.add_match();
  field2->set_field_id(8);
  TableEntryKey key(entry);

  std::stringstream msg;
  msg << key;
  EXPECT_THAT(msg.str(), HasSubstr("43"));
  EXPECT_THAT(msg.str(), HasSubstr("2"));
  EXPECT_THAT(msg.str(), HasSubstr("7"));
  EXPECT_THAT(msg.str(), HasSubstr("8"));
}

TEST(PacketReplicationEntryKeyTest, TrivialEquality) {
  PacketReplicationEngineEntry entry;
  PacketReplicationEntryKey key_a(entry);
  PacketReplicationEntryKey key_b(entry);
  EXPECT_TRUE(key_a == key_b);
}

TEST(PacketReplicationEntryKeyTest, NotEqualCheck) {
  ASSERT_OK_AND_ASSIGN(PacketReplicationEngineEntry entry,
                       gutil::ParseTextProto<PacketReplicationEngineEntry>(R"pb(
                         multicast_group_entry {
                           multicast_group_id: 4
                           replicas { port: "Ethernet0" instance: 1 }
                         }
                       )pb"));

  PacketReplicationEngineEntry entry2 = entry;
  auto* group_entry2 = entry2.mutable_multicast_group_entry();
  group_entry2->set_multicast_group_id(5);

  PacketReplicationEntryKey key_a(entry);
  PacketReplicationEntryKey key_b(entry2);

  EXPECT_FALSE(key_a == key_b);
  EXPECT_TRUE(key_a != key_b);
  EXPECT_FALSE(key_a != key_a);
  EXPECT_FALSE(key_b != key_b);
  EXPECT_TRUE(key_b == key_b);
}

TEST(PacketReplicationEntryKeyTest, VerifyHash) {
  ASSERT_OK_AND_ASSIGN(PacketReplicationEngineEntry entry,
                       gutil::ParseTextProto<PacketReplicationEngineEntry>(R"pb(
                         multicast_group_entry {
                           multicast_group_id: 5
                           replicas { port: "Ethernet0" instance: 1 }
                         }
                       )pb"));
  PacketReplicationEntryKey key_a(entry);

  PacketReplicationEngineEntry entry2 = entry;
  auto* group_entry = entry2.mutable_multicast_group_entry();
  group_entry->set_multicast_group_id(6);
  PacketReplicationEntryKey key_b(entry2);

  EXPECT_TRUE(absl::VerifyTypeImplementsAbslHashCorrectly(
      /*values = */ {key_a, key_b}));
}

TEST(PacketReplicationEntryKeyTest, LessThanCheck) {
  ASSERT_OK_AND_ASSIGN(PacketReplicationEngineEntry entry,
                       gutil::ParseTextProto<PacketReplicationEngineEntry>(R"pb(
                         multicast_group_entry { multicast_group_id: 5 }
                       )pb"));

  PacketReplicationEngineEntry entry2 = entry;
  auto* group_entry2 = entry2.mutable_multicast_group_entry();
  group_entry2->set_multicast_group_id(6);

  PacketReplicationEntryKey key_a(entry);
  PacketReplicationEntryKey key_b(entry2);

  EXPECT_FALSE(key_a < key_a);
  EXPECT_TRUE(key_b < key_a || key_a < key_b);
}

TEST(PacketReplicationEntryKeyTest, CloneSessionsNotEqual) {
  ASSERT_OK_AND_ASSIGN(PacketReplicationEngineEntry entry,
                       gutil::ParseTextProto<PacketReplicationEngineEntry>(R"pb(
                         clone_session_entry {
                           session_id: 6
                           class_of_service: 2
                           packet_length_bytes: 1500
                           replicas { port: "Ethernet0" instance: 1 }
                         }
                       )pb"));
  PacketReplicationEntryKey key_a(entry);

  PacketReplicationEngineEntry entry2 = entry;
  auto* clone_entry2 = entry2.mutable_clone_session_entry();
  clone_entry2->set_session_id(88);
  PacketReplicationEntryKey key_b(entry2);

  EXPECT_FALSE(key_a == key_b);
  EXPECT_TRUE(key_a != key_b);
  EXPECT_TRUE(key_a == key_a);
  EXPECT_FALSE(key_a != key_a);
}

TEST(PacketReplicationEntryKeyTest, UnknownPacketReplicationType) {
  PacketReplicationEngineEntry entry;
  PacketReplicationEntryKey key_a(entry);

  std::stringstream msg;
  msg << key_a;
  EXPECT_THAT(msg.str(), HasSubstr("0"));
}

TEST(PacketReplicationEntryKeyTest, TypesNotEqual) {
  ASSERT_OK_AND_ASSIGN(PacketReplicationEngineEntry entry,
                       gutil::ParseTextProto<PacketReplicationEngineEntry>(R"pb(
                         multicast_group_entry { multicast_group_id: 5 }
                       )pb"));
  PacketReplicationEntryKey key_a(entry);

  ASSERT_OK_AND_ASSIGN(PacketReplicationEngineEntry entry2,
                       gutil::ParseTextProto<PacketReplicationEngineEntry>(R"pb(
                         clone_session_entry { session_id: 6 }
                       )pb"));
  PacketReplicationEntryKey key_b(entry2);

  EXPECT_FALSE(key_a == key_b);
  EXPECT_TRUE(key_a != key_b);
  EXPECT_TRUE(key_a < key_b || key_b < key_a);
}

}  // namespace
}  // namespace pdpi
