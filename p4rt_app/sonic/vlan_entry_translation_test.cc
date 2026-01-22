// Copyright 2025 Google LLC
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
#include "p4rt_app/sonic/vlan_entry_translation.h"

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
#include "gutil/gutil/status_matchers.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4rt_app/sonic/adapters/mock_consumer_notifier_adapter.h"
#include "p4rt_app/sonic/adapters/mock_producer_state_table_adapter.h"
#include "p4rt_app/sonic/adapters/mock_table_adapter.h"
#include "p4rt_app/sonic/redis_connections.h"
#include "swss/rediscommand.h"
#include "swss/table.h"

namespace p4rt_app {
namespace sonic {
namespace {

using ::google::protobuf::TextFormat;
using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::testing::_;
using ::testing::DoAll;
using ::testing::Eq;
using ::testing::Return;
using ::testing::SetArgReferee;
using ::testing::SizeIs;

class VlanEntryTranslationTest : public ::testing::Test {
 protected:
  VlanEntryTranslationTest() {
    auto vlan_producer_state =
        std::make_unique<MockProducerStateTableAdapter>();
    auto vlan_notifier = std::make_unique<MockConsumerNotifierAdapter>();
    auto vlan_app_db = std::make_unique<MockTableAdapter>();
    auto vlan_app_state_db = std::make_unique<MockTableAdapter>();

    auto vlan_member_producer_state =
        std::make_unique<MockProducerStateTableAdapter>();
    auto vlan_member_notifier = std::make_unique<MockConsumerNotifierAdapter>();
    auto vlan_member_app_db = std::make_unique<MockTableAdapter>();
    auto vlan_member_app_state_db = std::make_unique<MockTableAdapter>();

    // Save a pointer so we can test against the mocks.
    mock_vlan_producer_state_ = vlan_producer_state.get();
    mock_vlan_notifier_ = vlan_notifier.get();
    mock_vlan_app_db_ = vlan_app_db.get();
    mock_vlan_app_state_db_ = vlan_app_state_db.get();

    mock_vlan_member_producer_state_ = vlan_member_producer_state.get();
    mock_vlan_member_notifier_ = vlan_member_notifier.get();
    mock_vlan_member_app_db_ = vlan_member_app_db.get();
    mock_vlan_member_app_state_db_ = vlan_member_app_state_db.get();

    vlan_table_ = VlanTable{
        .producer_state = std::move(vlan_producer_state),
        .notification_consumer = std::move(vlan_notifier),
        .app_db = std::move(vlan_app_db),
        .app_state_db = std::move(vlan_app_state_db),
    };

    vlan_member_table_ = VlanMemberTable{
        .producer_state = std::move(vlan_member_producer_state),
        .notification_consumer = std::move(vlan_member_notifier),
        .app_db = std::move(vlan_member_app_db),
        .app_state_db = std::move(vlan_member_app_state_db),
    };
  }

  MockProducerStateTableAdapter* mock_vlan_producer_state_;
  MockConsumerNotifierAdapter* mock_vlan_notifier_;
  MockProducerStateTableAdapter* mock_vlan_member_producer_state_;
  MockConsumerNotifierAdapter* mock_vlan_member_notifier_;
  MockTableAdapter* mock_vlan_app_db_;
  MockTableAdapter* mock_vlan_app_state_db_;
  MockTableAdapter* mock_vlan_member_app_db_;
  MockTableAdapter* mock_vlan_member_app_state_db_;
  VlanTable vlan_table_;
  VlanMemberTable vlan_member_table_;
};

TEST_F(VlanEntryTranslationTest, InsertVlanEntry) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(
      R"pb(matches {
             name: "vlan_id"
             exact { hex_str: "0x064" }
           }
           action { name: "no_action" }
           controller_metadata: "test_metadata")pb",
      &table_entry));

  // Expected RedisDB entry.
  const std::vector<std::pair<std::string, std::string>> kfv_values = {
      std::make_pair("source", "P4"),
      std::make_pair("controller_metadata", "test_metadata"),
  };
  const std::string expected_key = "Vlan100";
  swss::KeyOpFieldsValuesTuple expected_key_value =
      std::make_tuple(expected_key, "SET", kfv_values);

  ASSERT_OK_AND_ASSIGN(
      auto update, CreateAppDbVlanUpdate(p4::v1::Update::INSERT, table_entry));
  ASSERT_THAT(CreateAppDbVlanUpdate(p4::v1::Update::INSERT, table_entry),
              IsOkAndHolds(expected_key_value));

  EXPECT_CALL(*mock_vlan_producer_state_, set(Eq("Vlan100"), _)).Times(1);
  EXPECT_CALL(*mock_vlan_notifier_, WaitForNotificationAndPop)
      .WillOnce(DoAll(SetArgReferee<0>("SWSS_RC_SUCCESS"),
                      SetArgReferee<1>("Vlan100"),
                      SetArgReferee<2>(std::vector<swss::FieldValueTuple>(
                          {swss::FieldValueTuple("err_str", "Ok")})),
                      Return(true)));

  EXPECT_THAT(PerformAppDbVlanUpdate(vlan_table_, update),
              IsOkAndHolds(EqualsProto("code: OK")));
}

TEST_F(VlanEntryTranslationTest, InsertVlanEntryFailsIfNotValidHexString) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(
      TextFormat::ParseFromString(R"pb(matches {
                                         name: "vlan_id"
                                         exact { hex_str: "0xx64" }
                                       }
                                       action { name: "no_action" })pb",
                                  &table_entry));

  EXPECT_THAT(CreateAppDbVlanUpdate(p4::v1::Update::INSERT, table_entry),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_F(VlanEntryTranslationTest, InsertVlanEntryFailsIfIdOutOfRange) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(
      TextFormat::ParseFromString(R"pb(matches {
                                         name: "vlan_id"
                                         exact { hex_str: "0xfff" }
                                       }
                                       action { name: "no_action" })pb",
                                  &table_entry));
  pdpi::IrTableEntry table_entry2;
  ASSERT_TRUE(
      TextFormat::ParseFromString(R"pb(matches {
                                         name: "vlan_id"
                                         exact { hex_str: "0x0" }
                                       }
                                       action { name: "no_action" })pb",
                                  &table_entry2));

  EXPECT_THAT(CreateAppDbVlanUpdate(p4::v1::Update::INSERT, table_entry),
              StatusIs(absl::StatusCode::kInvalidArgument));

  EXPECT_THAT(CreateAppDbVlanUpdate(p4::v1::Update::INSERT, table_entry2),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_F(VlanEntryTranslationTest, InsertVlanEntryFailsIfMatchFieldMissing) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(
      TextFormat::ParseFromString(R"pb(matches {
                                         name: "vlan_id_unknown"
                                         exact { hex_str: "0x10" }
                                       }
                                       action { name: "no_action" })pb",
                                  &table_entry));
  EXPECT_THAT(CreateAppDbVlanUpdate(p4::v1::Update::INSERT, table_entry),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_F(VlanEntryTranslationTest, ModifyVlanEntryIsNotAllowed) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(
      TextFormat::ParseFromString(R"pb(matches {
                                         name: "vlan_id"
                                         exact { hex_str: "0x11" }
                                       }
                                       action { name: "no_action" })pb",
                                  &table_entry));

  EXPECT_THAT(CreateAppDbVlanUpdate(p4::v1::Update::MODIFY, table_entry),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_F(VlanEntryTranslationTest, VlanEntryUnknownUpdateFails) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(
      TextFormat::ParseFromString(R"pb(matches {
                                         name: "vlan_id"
                                         exact { hex_str: "0x10" }
                                       }
                                       action { name: "no_action" })pb",
                                  &table_entry));

  EXPECT_THAT(CreateAppDbVlanUpdate(p4::v1::Update::UNSPECIFIED, table_entry),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_F(VlanEntryTranslationTest, VlanEntryUnknownOperationFails) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(
      TextFormat::ParseFromString(R"pb(matches {
                                         name: "vlan_id"
                                         exact { hex_str: "0x10" }
                                       }
                                       action { name: "no_action" })pb",
                                  &table_entry));

  ASSERT_OK_AND_ASSIGN(
      swss::KeyOpFieldsValuesTuple update,
      CreateAppDbVlanUpdate(p4::v1::Update::INSERT, table_entry));
  kfvOp(update) = "Other";
  EXPECT_THAT(PerformAppDbVlanUpdate(vlan_table_, update),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_F(VlanEntryTranslationTest, DeleteVlanEntry) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(
      TextFormat::ParseFromString(R"pb(matches {
                                         name: "vlan_id"
                                         exact { hex_str: "0xff" }
                                       }
                                       action { name: "no_action" })pb",
                                  &table_entry));
  ASSERT_OK_AND_ASSIGN(
      auto update, CreateAppDbVlanUpdate(p4::v1::Update::DELETE, table_entry));

  EXPECT_CALL(*mock_vlan_producer_state_, del(Eq("Vlan255"))).Times(1);
  EXPECT_CALL(*mock_vlan_notifier_, WaitForNotificationAndPop)
      .WillOnce(DoAll(SetArgReferee<0>("SWSS_RC_SUCCESS"),
                      SetArgReferee<1>("Vlan255"),
                      SetArgReferee<2>(std::vector<swss::FieldValueTuple>(
                          {swss::FieldValueTuple("err_str", "Ok")})),
                      Return(true)));

  EXPECT_THAT(PerformAppDbVlanUpdate(vlan_table_, update),
              IsOkAndHolds(EqualsProto("code: OK")));
}

TEST_F(VlanEntryTranslationTest, VlanTableRead) {
  pdpi::IrTableEntry table_entry_1;
  pdpi::IrTableEntry table_entry_2;
  ASSERT_TRUE(TextFormat::ParseFromString(
      R"pb(table_name: "vlan_table"
           matches {
             name: "vlan_id"
             exact { hex_str: "0x064" }
           }
           action { name: "no_action" }
           controller_metadata: "test_metadata")pb",
      &table_entry_1));
  ASSERT_TRUE(TextFormat::ParseFromString(
      R"pb(table_name: "vlan_table"
           matches {
             name: "vlan_id"
             exact { hex_str: "0x0c8" }
           }
           action { name: "no_action" }
           controller_metadata: "test_metadata_2")pb",
      &table_entry_2));

  EXPECT_CALL(*mock_vlan_app_db_, keys)
      .WillOnce(Return(std::vector<std::string>{"Vlan100", "Vlan200"}));
  EXPECT_CALL(*mock_vlan_app_db_, get("Vlan100"))
      .WillOnce(Return(std::vector<std::pair<std::string, std::string>>{
          std::make_pair("source", "P4"),
          std::make_pair("controller_metadata", "test_metadata"),
      }));
  EXPECT_CALL(*mock_vlan_app_db_, get("Vlan200"))
      .WillOnce(Return(std::vector<std::pair<std::string, std::string>>{
          std::make_pair("source", "P4"),
          std::make_pair("controller_metadata", "test_metadata_2"),
      }));

  ASSERT_OK_AND_ASSIGN(auto entries, GetAllAppDbVlanTableEntries(vlan_table_));
  EXPECT_THAT(entries, SizeIs(2));
  EXPECT_THAT(entries[0], EqualsProto(table_entry_1));
  EXPECT_THAT(entries[1], EqualsProto(table_entry_2));
}

TEST_F(VlanEntryTranslationTest, VlanTableReadFailsIfKeyHasIncorrectPrefix) {
  pdpi::IrTableEntry table_entry;

  EXPECT_CALL(*mock_vlan_app_db_, keys)
      .WillOnce(Return(std::vector<std::string>{"nlaV100", "Vlan100"}));

  EXPECT_THAT(GetAllAppDbVlanTableEntries(vlan_table_),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_F(VlanEntryTranslationTest, VlanTableReadFailsIfKeyOutOfRange) {
  pdpi::IrTableEntry table_entry;

  EXPECT_CALL(*mock_vlan_app_db_, keys)
      .WillOnce(Return(std::vector<std::string>{"Vlan4096"}));

  EXPECT_THAT(GetAllAppDbVlanTableEntries(vlan_table_),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_F(VlanEntryTranslationTest, VlanTableReadFailsIfVlanIdIsNotANumber) {
  pdpi::IrTableEntry table_entry;

  EXPECT_CALL(*mock_vlan_app_db_, keys)
      .WillOnce(Return(std::vector<std::string>{"VlanNotANumber", "Vlan100"}));

  EXPECT_THAT(GetAllAppDbVlanTableEntries(vlan_table_),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_F(VlanEntryTranslationTest, InsertVlanMemberEntryTaggedMember) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(
      R"pb(matches {
             name: "vlan_id"
             exact { hex_str: "0x064" }
           }
           matches {
             name: "port"
             exact { str: "Ethernet1/1/1" }
           }
           action { name: "make_tagged_member" }
           controller_metadata: "test_metadata")pb",
      &table_entry));

  // Expected RedisDB entry.
  const std::vector<std::pair<std::string, std::string>> kfv_values = {
      std::make_pair("source", "P4"),
      std::make_pair("tagging_mode", "tagged"),
      std::make_pair("controller_metadata", "test_metadata"),
  };
  const std::string expected_key = "Vlan100:Ethernet1/1/1";
  swss::KeyOpFieldsValuesTuple expected_key_value =
      std::make_tuple(expected_key, "SET", kfv_values);

  ASSERT_OK_AND_ASSIGN(auto update, CreateAppDbVlanMemberUpdate(
                                        p4::v1::Update::INSERT, table_entry));
  ASSERT_THAT(CreateAppDbVlanMemberUpdate(p4::v1::Update::INSERT, table_entry),
              IsOkAndHolds(expected_key_value));

  EXPECT_CALL(*mock_vlan_member_producer_state_,
              set(Eq("Vlan100:Ethernet1/1/1"), _))
      .Times(1);
  EXPECT_CALL(*mock_vlan_member_notifier_, WaitForNotificationAndPop)
      .WillOnce(DoAll(SetArgReferee<0>("SWSS_RC_SUCCESS"),
                      SetArgReferee<1>("Vlan100:Ethernet1/1/1"),
                      SetArgReferee<2>(std::vector<swss::FieldValueTuple>(
                          {swss::FieldValueTuple("err_str", "Ok")})),
                      Return(true)));

  EXPECT_THAT(PerformAppDbVlanMemberUpdate(vlan_member_table_, update),
              IsOkAndHolds(EqualsProto("code: OK")));
}

TEST_F(VlanEntryTranslationTest, InsertVlanMemberEntryUntaggedMember) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(
      R"pb(matches {
             name: "vlan_id"
             exact { hex_str: "0x064" }
           }
           matches {
             name: "port"
             exact { str: "Ethernet1/1/1" }
           }
           action { name: "make_untagged_member" }
           controller_metadata: "test_metadata")pb",
      &table_entry));

  // Expected RedisDB entry.
  const std::vector<std::pair<std::string, std::string>> kfv_values = {
      std::make_pair("source", "P4"),
      std::make_pair("tagging_mode", "untagged"),
      std::make_pair("controller_metadata", "test_metadata"),
  };
  const std::string expected_key = "Vlan100:Ethernet1/1/1";
  swss::KeyOpFieldsValuesTuple expected_key_value =
      std::make_tuple(expected_key, "SET", kfv_values);

  ASSERT_OK_AND_ASSIGN(auto update, CreateAppDbVlanMemberUpdate(
                                        p4::v1::Update::INSERT, table_entry));
  ASSERT_THAT(CreateAppDbVlanMemberUpdate(p4::v1::Update::INSERT, table_entry),
              IsOkAndHolds(expected_key_value));

  EXPECT_CALL(*mock_vlan_member_producer_state_,
              set(Eq("Vlan100:Ethernet1/1/1"), _))
      .Times(1);
  EXPECT_CALL(*mock_vlan_member_notifier_, WaitForNotificationAndPop)
      .WillOnce(DoAll(SetArgReferee<0>("SWSS_RC_SUCCESS"),
                      SetArgReferee<1>("Vlan100:Ethernet1/1/1"),
                      SetArgReferee<2>(std::vector<swss::FieldValueTuple>(
                          {swss::FieldValueTuple("err_str", "Ok")})),
                      Return(true)));

  EXPECT_THAT(PerformAppDbVlanMemberUpdate(vlan_member_table_, update),
              IsOkAndHolds(EqualsProto("code: OK")));
}

TEST_F(VlanEntryTranslationTest, InsertVlanMemberEntryFailsIfVlanIdOutOfRange) {
  pdpi::IrTableEntry table_entry;
  pdpi::IrTableEntry table_entry2;
  ASSERT_TRUE(TextFormat::ParseFromString(R"pb(matches {
                                                 name: "vlan_id"
                                                 exact { hex_str: "0xfff" }
                                               }
                                               matches {
                                                 name: "port"
                                                 exact { str: "Ethernet1/1/1" }
                                               })pb",
                                          &table_entry));

  ASSERT_TRUE(TextFormat::ParseFromString(R"pb(matches {
                                                 name: "vlan_id"
                                                 exact { hex_str: "0x0" }
                                               }
                                               matches {
                                                 name: "port"
                                                 exact { str: "Ethernet1/1/1" }
                                               })pb",
                                          &table_entry));

  EXPECT_THAT(CreateAppDbVlanMemberUpdate(p4::v1::Update::INSERT, table_entry),
              StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_THAT(CreateAppDbVlanMemberUpdate(p4::v1::Update::INSERT, table_entry2),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_F(VlanEntryTranslationTest, InsertVlanMemberEntryFailsIfVlanIdInvalidHex) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(R"pb(matches {
                                                 name: "vlan_id"
                                                 exact { hex_str: "0xSorry" }
                                               }
                                               matches {
                                                 name: "port"
                                                 exact { str: "Ethernet1/1/1" }
                                               })pb",
                                          &table_entry));

  EXPECT_THAT(CreateAppDbVlanMemberUpdate(p4::v1::Update::INSERT, table_entry),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_F(VlanEntryTranslationTest,
       InsertVlanMemberEntryFailsIfMatchFieldsMissing) {
  pdpi::IrTableEntry table_entry;
  pdpi::IrTableEntry table_entry2;
  ASSERT_TRUE(TextFormat::ParseFromString(R"pb(matches {
                                                 name: "vlan_id"
                                                 exact { hex_str: "0x1" }
                                               })pb",
                                          &table_entry));

  ASSERT_TRUE(TextFormat::ParseFromString(R"pb(matches {
                                                 name: "port"
                                                 exact { str: "Ethernet1/1/1" }
                                               })pb",
                                          &table_entry2));

  EXPECT_THAT(CreateAppDbVlanMemberUpdate(p4::v1::Update::INSERT, table_entry),
              StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_THAT(CreateAppDbVlanMemberUpdate(p4::v1::Update::INSERT, table_entry2),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_F(VlanEntryTranslationTest, DeleteVlanMemberEntry) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(R"pb(matches {
                                                 name: "vlan_id"
                                                 exact { hex_str: "0xff" }
                                               }
                                               matches {
                                                 name: "port"
                                                 exact { str: "Ethernet1/1/1" }
                                               })pb",
                                          &table_entry));
  ASSERT_OK_AND_ASSIGN(auto update, CreateAppDbVlanMemberUpdate(
                                        p4::v1::Update::DELETE, table_entry));

  EXPECT_CALL(*mock_vlan_member_producer_state_,
              del(Eq("Vlan255:Ethernet1/1/1")))
      .Times(1);
  EXPECT_CALL(*mock_vlan_member_notifier_, WaitForNotificationAndPop)
      .WillOnce(DoAll(SetArgReferee<0>("SWSS_RC_SUCCESS"),
                      SetArgReferee<1>("Vlan255:Ethernet1/1/1"),
                      SetArgReferee<2>(std::vector<swss::FieldValueTuple>(
                          {swss::FieldValueTuple("err_str", "Ok")})),
                      Return(true)));

  EXPECT_THAT(PerformAppDbVlanMemberUpdate(vlan_member_table_, update),
              IsOkAndHolds(EqualsProto("code: OK")));
}

TEST_F(VlanEntryTranslationTest, ModifyVlanMemberEntry) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(R"pb(matches {
                                                 name: "vlan_id"
                                                 exact { hex_str: "0x064" }
                                               }
                                               matches {
                                                 name: "port"
                                                 exact { str: "Ethernet1/1/1" }
                                               })pb",
                                          &table_entry));

  ASSERT_OK_AND_ASSIGN(auto update, CreateAppDbVlanMemberUpdate(
                                        p4::v1::Update::MODIFY, table_entry));

  EXPECT_CALL(*mock_vlan_member_producer_state_,
              set(Eq("Vlan100:Ethernet1/1/1"), _))
      .Times(1);
  EXPECT_CALL(*mock_vlan_member_notifier_, WaitForNotificationAndPop)
      .WillOnce(DoAll(SetArgReferee<0>("SWSS_RC_SUCCESS"),
                      SetArgReferee<1>("Vlan100:Ethernet1/1/1"),
                      SetArgReferee<2>(std::vector<swss::FieldValueTuple>(
                          {swss::FieldValueTuple("err_str", "Ok")})),
                      Return(true)));

  EXPECT_THAT(PerformAppDbVlanMemberUpdate(vlan_member_table_, update),
              IsOkAndHolds(EqualsProto("code: OK")));
}

TEST_F(VlanEntryTranslationTest, VlanMemberEntryUnknownUpdateFails) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(R"pb(matches {
                                                 name: "vlan_id"
                                                 exact { hex_str: "0xff" }
                                               }
                                               matches {
                                                 name: "port"
                                                 exact { str: "Ethernet1/1/1" }
                                               })pb",
                                          &table_entry));

  EXPECT_THAT(
      CreateAppDbVlanMemberUpdate(p4::v1::Update::UNSPECIFIED, table_entry),
      StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_F(VlanEntryTranslationTest, VlanMemberEntryUnknownOperationFails) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(R"pb(matches {
                                                 name: "vlan_id"
                                                 exact { hex_str: "0xff" }
                                               }
                                               matches {
                                                 name: "port"
                                                 exact { str: "Ethernet1/1/1" }
                                               })pb",
                                          &table_entry));
  ASSERT_OK_AND_ASSIGN(
      swss::KeyOpFieldsValuesTuple update,
      CreateAppDbVlanMemberUpdate(p4::v1::Update::INSERT, table_entry));
  kfvOp(update) = "Other";
  EXPECT_THAT(PerformAppDbVlanMemberUpdate(vlan_member_table_, update),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_F(VlanEntryTranslationTest, VlanMemberTableRead) {
  pdpi::IrTableEntry table_entry_1;
  pdpi::IrTableEntry table_entry_2;
  ASSERT_TRUE(TextFormat::ParseFromString(
      R"pb(table_name: "vlan_membership_table"
           matches {
             name: "vlan_id"
             exact { hex_str: "0x064" }
           }
           matches {
             name: "port"
             exact { str: "Ethernet1/1/1" }
           }
           action { name: "make_untagged_member" }
           controller_metadata: "test_metadata")pb",
      &table_entry_1));
  ASSERT_TRUE(TextFormat::ParseFromString(
      R"pb(table_name: "vlan_membership_table"
           matches {
             name: "vlan_id"
             exact { hex_str: "0x0c8" }
           }
           matches {
             name: "port"
             exact { str: "Ethernet1/1/2" }
           }
           action { name: "make_tagged_member" }
           controller_metadata: "test_metadata_2")pb",
      &table_entry_2));

  EXPECT_CALL(*mock_vlan_member_app_db_, keys)
      .WillOnce(Return(std::vector<std::string>{"Vlan100:Ethernet1/1/1",
                                                "Vlan200:Ethernet1/1/2"}));
  EXPECT_CALL(*mock_vlan_member_app_db_, get("Vlan100:Ethernet1/1/1"))
      .WillOnce(Return(std::vector<std::pair<std::string, std::string>>{
          std::make_pair("source", "P4"),
          std::make_pair("tagging_mode", "untagged"),
          std::make_pair("controller_metadata", "test_metadata"),
      }));
  EXPECT_CALL(*mock_vlan_member_app_db_, get("Vlan200:Ethernet1/1/2"))
      .WillOnce(Return(std::vector<std::pair<std::string, std::string>>{
          std::make_pair("source", "P4"),
          std::make_pair("tagging_mode", "tagged"),
          std::make_pair("controller_metadata", "test_metadata_2"),
      }));

  ASSERT_OK_AND_ASSIGN(auto entries,
                       GetAllAppDbVlanMemberTableEntries(vlan_member_table_));
  EXPECT_THAT(entries, SizeIs(2));
  EXPECT_THAT(entries[0], EqualsProto(table_entry_1));
  EXPECT_THAT(entries[1], EqualsProto(table_entry_2));
}

TEST_F(VlanEntryTranslationTest, VlanMemberTableReadFailsIfKeyFormatIncorrect) {
  pdpi::IrTableEntry table_entry;

  EXPECT_CALL(*mock_vlan_member_app_db_, keys)
      .WillOnce(Return(std::vector<std::string>{"Vlan1Ethernet1/1/1",
                                                "Vlan2:Ethernet1/1/1"}));

  EXPECT_THAT(GetAllAppDbVlanMemberTableEntries(vlan_member_table_),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_F(VlanEntryTranslationTest,
       VlanMemberTableReadFailsIfKeyFormatIncorrect2) {
  pdpi::IrTableEntry table_entry;

  EXPECT_CALL(*mock_vlan_member_app_db_, keys)
      .WillOnce(Return(std::vector<std::string>{"Vlan1:Ethernet1/1/1:Extra",
                                                "Vlan2:Ethernet1/1/1"}));

  EXPECT_THAT(GetAllAppDbVlanMemberTableEntries(vlan_member_table_),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_F(VlanEntryTranslationTest, VlanMemberTableReadFailsIfVlanIdIncorrect) {
  pdpi::IrTableEntry table_entry;

  EXPECT_CALL(*mock_vlan_member_app_db_, keys)
      .WillOnce(Return(std::vector<std::string>{"vlan1:Ethernet1/1/1",
                                                "Vlan2:Ethernet1/1/1"}));

  EXPECT_THAT(GetAllAppDbVlanMemberTableEntries(vlan_member_table_),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_F(VlanEntryTranslationTest, VlanMemberTableReadFailsIfVlanIdIncorrect2) {
  pdpi::IrTableEntry table_entry;

  EXPECT_CALL(*mock_vlan_member_app_db_, keys)
      .WillOnce(Return(std::vector<std::string>{"Vlan:Ethernet1/1/1",
                                                "Vlan2:Ethernet1/1/1"}));

  EXPECT_THAT(GetAllAppDbVlanMemberTableEntries(vlan_member_table_),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

}  // namespace
}  // namespace sonic
}  // namespace p4rt_app
