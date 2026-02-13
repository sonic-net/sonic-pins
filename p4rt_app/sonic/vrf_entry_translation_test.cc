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
#include "p4rt_app/sonic/vrf_entry_translation.h"

#include <utility>

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "gmock/gmock.h"
#include "google/protobuf/text_format.h"
#include "google/rpc/code.pb.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4rt_app/sonic/adapters/mock_consumer_notifier_adapter.h"
#include "p4rt_app/sonic/adapters/mock_producer_state_table_adapter.h"
#include "p4rt_app/sonic/adapters/mock_table_adapter.h"
#include "p4rt_app/sonic/redis_connections.h"

namespace p4rt_app {
namespace sonic {
namespace {

using ::google::protobuf::TextFormat;
using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::testing::_;
using ::testing::DoAll;
using ::testing::Eq;
using ::testing::Return;
using ::testing::SetArgReferee;
using ::testing::UnorderedElementsAre;

class VrfEntryTranslationTest : public ::testing::Test {
 protected:
  VrfEntryTranslationTest() {
    auto vrf_producer_state = std::make_unique<MockProducerStateTableAdapter>();
    auto vrf_notifier = std::make_unique<MockConsumerNotifierAdapter>();
    auto vrf_app_db = std::make_unique<MockTableAdapter>();
    auto vrf_app_state_db = std::make_unique<MockTableAdapter>();

    // Save a pointer so we can test against the mocks.
    mock_vrf_producer_state_ = vrf_producer_state.get();
    mock_vrf_notifier_ = vrf_notifier.get();
    mock_vrf_app_db_ = vrf_app_db.get();
    mock_vrf_app_state_db_ = vrf_app_state_db.get();

    vrf_table_ = VrfTable{
        .producer_state = std::move(vrf_producer_state),
        .notification_consumer = std::move(vrf_notifier),
        .app_db = std::move(vrf_app_db),
        .app_state_db = std::move(vrf_app_state_db),
    };
  }

  MockProducerStateTableAdapter* mock_vrf_producer_state_;
  MockConsumerNotifierAdapter* mock_vrf_notifier_;
  MockTableAdapter* mock_vrf_app_db_;
  MockTableAdapter* mock_vrf_app_state_db_;
  VrfTable vrf_table_;
};

TEST_F(VrfEntryTranslationTest, InsertVrfEntry) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(R"pb(matches {
                                                 name: "vrf_id"
                                                 exact { str: "vrf-1" }
                                               })pb",
                                          &table_entry));

  EXPECT_CALL(*mock_vrf_producer_state_, set(Eq("vrf-1"), _)).Times(1);
  EXPECT_CALL(*mock_vrf_notifier_, WaitForNotificationAndPop)
      .WillOnce(DoAll(SetArgReferee<0>("SWSS_RC_SUCCESS"),
                      SetArgReferee<1>("vrf-1"),
                      SetArgReferee<2>(std::vector<swss::FieldValueTuple>(
                          {swss::FieldValueTuple("err_str", "Ok")})),
                      Return(true)));

  pdpi::IrWriteResponse response;
  response.add_statuses();
  EXPECT_OK(UpdateAppDbVrfTable(vrf_table_, p4::v1::Update::INSERT,
                                /*rpc_index=*/0, table_entry, response));
  EXPECT_EQ(response.statuses(0).code(), google::rpc::Code::OK);
}

TEST_F(VrfEntryTranslationTest, CannotInsertDuplicateVrfEntry) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(R"pb(matches {
                                                 name: "vrf_id"
                                                 exact { str: "vrf-1" }
                                               })pb",
                                          &table_entry));

  // When checking for existance we return `true`. Then because it already
  // exists we should not try to add a VRF entry.
  EXPECT_CALL(*mock_vrf_app_db_, exists("vrf-1")).WillOnce(Return(true));
  EXPECT_CALL(*mock_vrf_producer_state_, set).Times(0);

  pdpi::IrWriteResponse response;
  response.add_statuses();
  EXPECT_OK(UpdateAppDbVrfTable(vrf_table_, p4::v1::Update::INSERT,
                                /*rpc_index=*/0, table_entry, response));
  EXPECT_EQ(response.statuses(0).code(), google::rpc::Code::ALREADY_EXISTS);
}

TEST_F(VrfEntryTranslationTest, DeleteVrfEntry) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(R"pb(matches {
                                                 name: "vrf_id"
                                                 exact { str: "vrf-1" }
                                               })pb",
                                          &table_entry));

  EXPECT_CALL(*mock_vrf_app_db_, exists("vrf-1")).WillOnce(Return(true));
  EXPECT_CALL(*mock_vrf_producer_state_, del(Eq("vrf-1"))).Times(1);
  EXPECT_CALL(*mock_vrf_notifier_, WaitForNotificationAndPop)
      .WillOnce(DoAll(SetArgReferee<0>("SWSS_RC_SUCCESS"),
                      SetArgReferee<1>("vrf-1"),
                      SetArgReferee<2>(std::vector<swss::FieldValueTuple>(
                          {swss::FieldValueTuple("err_str", "Ok")})),
                      Return(true)));

  pdpi::IrWriteResponse response;
  response.add_statuses();
  EXPECT_OK(UpdateAppDbVrfTable(vrf_table_, p4::v1::Update::DELETE,
                                /*rpc_index=*/0, table_entry, response));
  EXPECT_EQ(response.statuses(0).code(), google::rpc::Code::OK);
}

TEST_F(VrfEntryTranslationTest, CannotDeleteMissingVrfEntry) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(R"pb(matches {
                                                 name: "vrf_id"
                                                 exact { str: "vrf-1" }
                                               })pb",
                                          &table_entry));

  // When checking for existance we return `false`. Then because the entry does
  // not exist we should not try to delete it.
  EXPECT_CALL(*mock_vrf_app_db_, exists("vrf-1")).WillOnce(Return(false));
  EXPECT_CALL(*mock_vrf_producer_state_, del).Times(0);

  pdpi::IrWriteResponse response;
  response.add_statuses();
  EXPECT_OK(UpdateAppDbVrfTable(vrf_table_, p4::v1::Update::DELETE,
                                /*rpc_index=*/0, table_entry, response));
  EXPECT_EQ(response.statuses(0).code(), google::rpc::Code::NOT_FOUND);
}

TEST_F(VrfEntryTranslationTest, ModifyVrfEntryIsNotAllowed) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(R"pb(matches {
                                                 name: "vrf_id"
                                                 exact { str: "vrf-1" }
                                               })pb",
                                          &table_entry));

  pdpi::IrWriteResponse response;
  response.add_statuses();
  EXPECT_OK(UpdateAppDbVrfTable(vrf_table_, p4::v1::Update::MODIFY,
                                /*rpc_index=*/0, table_entry, response));
  EXPECT_EQ(response.statuses(0).code(), google::rpc::INVALID_ARGUMENT);
}

TEST_F(VrfEntryTranslationTest, RequireVrfIdMatchField) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(R"pb(matches {
                                                 name: "invalid_name"
                                                 exact { str: "vrf-1" }
                                               })pb",
                                          &table_entry));

  pdpi::IrWriteResponse response;
  response.add_statuses();
  EXPECT_OK(UpdateAppDbVrfTable(vrf_table_, p4::v1::Update::INSERT,
                                /*rpc_index=*/0, table_entry, response));
  EXPECT_EQ(response.statuses(0).code(), google::rpc::INVALID_ARGUMENT);
}

TEST_F(VrfEntryTranslationTest, CannotChangeTheSonicDefaultVrf) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(R"pb(matches {
                                                 name: "invalid_name"
                                                 exact { str: "" }
                                               })pb",
                                          &table_entry));

  pdpi::IrWriteResponse response;
  response.add_statuses();
  EXPECT_OK(UpdateAppDbVrfTable(vrf_table_, p4::v1::Update::INSERT,
                                /*rpc_index=*/0, table_entry, response));
  EXPECT_EQ(response.statuses(0).code(), google::rpc::INVALID_ARGUMENT);
}

TEST_F(VrfEntryTranslationTest, CannotTouchSonicDefaultVrf) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(R"pb(matches {
                                                 name: "vrf_id"
                                                 exact { str: "" }
                                               })pb",
                                          &table_entry));

  EXPECT_CALL(*mock_vrf_producer_state_, set).Times(0);

  pdpi::IrWriteResponse response;
  response.add_statuses();
  EXPECT_OK(UpdateAppDbVrfTable(vrf_table_, p4::v1::Update::INSERT,
                                /*rpc_index=*/0, table_entry, response));
  EXPECT_EQ(response.statuses(0).code(), google::rpc::Code::INVALID_ARGUMENT);
}

}  // namespace
}  // namespace sonic
}  // namespace p4rt_app
