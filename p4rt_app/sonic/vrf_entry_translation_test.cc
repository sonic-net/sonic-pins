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
#include "p4rt_app/sonic/vrf_entry_translation.h"

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
#include "swss/mocks/mock_consumer_notifier.h"
#include "swss/mocks/mock_db_connector.h"
#include "swss/mocks/mock_producer_state_table.h"

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
using ::testing::HasSubstr;
using ::testing::Return;
using ::testing::SetArgReferee;
using ::testing::UnorderedElementsAre;

class VrfEntryTranslationTest : public ::testing::Test {
 protected:
  VrfEntryTranslationTest() {
    ON_CALL(mock_vrf_table_, get_table_name)
        .WillByDefault(Return(vrf_table_name_));
  }

  const std::string vrf_table_name_ = "VRF_TABLE";
  swss::MockProducerStateTable mock_vrf_table_;
  swss::MockConsumerNotifier mock_vrf_notifier_;
  swss::MockDBConnector mock_app_db_client_;
  swss::MockDBConnector mock_state_db_client_;
  absl::flat_hash_map<std::string, int> vrf_id_reference_count_;
};

TEST_F(VrfEntryTranslationTest, InsertVrfEntry) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(R"pb(matches {
                                                 name: "vrf_id"
                                                 exact { str: "vrf-1" }
                                               })pb",
                                          &table_entry));

  EXPECT_CALL(mock_vrf_table_, set(Eq("vrf-1"), _, _, _)).Times(1);
  EXPECT_CALL(mock_vrf_notifier_, WaitForNotificationAndPop)
      .WillOnce(DoAll(SetArgReferee<0>("SWSS_RC_SUCCESS"),
                      SetArgReferee<1>("vrf-1"),
                      SetArgReferee<2>(std::vector<swss::FieldValueTuple>(
                          {swss::FieldValueTuple("err_str", "Ok")})),
                      Return(true)));

  pdpi::IrWriteResponse response;
  response.add_statuses();
  EXPECT_OK(UpdateAppDbVrfTable(p4::v1::Update::INSERT, /*rpc_index=*/0,
                                table_entry, mock_vrf_table_,
                                mock_vrf_notifier_, mock_app_db_client_,
                                mock_state_db_client_, response));
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
  EXPECT_CALL(mock_app_db_client_, exists("VRF_TABLE:vrf-1"))
      .WillOnce(Return(true));
  EXPECT_CALL(mock_vrf_table_, set(_, _, _, _)).Times(0);

  pdpi::IrWriteResponse response;
  response.add_statuses();
  EXPECT_OK(UpdateAppDbVrfTable(p4::v1::Update::INSERT, /*rpc_index=*/0,
                                table_entry, mock_vrf_table_,
                                mock_vrf_notifier_, mock_app_db_client_,
                                mock_state_db_client_, response));
  EXPECT_EQ(response.statuses(0).code(), google::rpc::Code::ALREADY_EXISTS);
}

TEST_F(VrfEntryTranslationTest, DeleteVrfEntry) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(R"pb(matches {
                                                 name: "vrf_id"
                                                 exact { str: "vrf-1" }
                                               })pb",
                                          &table_entry));

  EXPECT_CALL(mock_app_db_client_, exists("VRF_TABLE:vrf-1"))
      .WillOnce(Return(true));
  EXPECT_CALL(mock_vrf_table_, del(Eq("vrf-1"), _, _)).Times(1);
  EXPECT_CALL(mock_vrf_notifier_, WaitForNotificationAndPop)
      .WillOnce(DoAll(SetArgReferee<0>("SWSS_RC_SUCCESS"),
                      SetArgReferee<1>("vrf-1"),
                      SetArgReferee<2>(std::vector<swss::FieldValueTuple>(
                          {swss::FieldValueTuple("err_str", "Ok")})),
                      Return(true)));

  pdpi::IrWriteResponse response;
  response.add_statuses();
  EXPECT_OK(UpdateAppDbVrfTable(p4::v1::Update::DELETE, /*rpc_index=*/0,
                                table_entry, mock_vrf_table_,
                                mock_vrf_notifier_, mock_app_db_client_,
                                mock_state_db_client_, response));
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
  EXPECT_CALL(mock_app_db_client_, exists("VRF_TABLE:vrf-1"))
      .WillOnce(Return(false));
  EXPECT_CALL(mock_vrf_table_, del(_, _, _)).Times(0);

  pdpi::IrWriteResponse response;
  response.add_statuses();
  EXPECT_OK(UpdateAppDbVrfTable(p4::v1::Update::DELETE, /*rpc_index=*/0,
                                table_entry, mock_vrf_table_,
                                mock_vrf_notifier_, mock_app_db_client_,
                                mock_state_db_client_, response));
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
  EXPECT_OK(UpdateAppDbVrfTable(p4::v1::Update::MODIFY, /*rpc_index=*/0,
                                table_entry, mock_vrf_table_,
                                mock_vrf_notifier_, mock_app_db_client_,
                                mock_state_db_client_, response));
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
  EXPECT_OK(UpdateAppDbVrfTable(p4::v1::Update::INSERT, /*rpc_index=*/0,
                                table_entry, mock_vrf_table_,
                                mock_vrf_notifier_, mock_app_db_client_,
                                mock_state_db_client_, response));
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
  EXPECT_OK(UpdateAppDbVrfTable(p4::v1::Update::INSERT, /*rpc_index=*/0,
                                table_entry, mock_vrf_table_,
                                mock_vrf_notifier_, mock_app_db_client_,
                                mock_state_db_client_, response));
  EXPECT_EQ(response.statuses(0).code(), google::rpc::INVALID_ARGUMENT);
}

TEST_F(VrfEntryTranslationTest, ReadIgnoresUninstalledVrfs) {
  // Return 2 table entries, but only 2 have been fully installed by the OA.
  EXPECT_CALL(mock_app_db_client_, keys("*"))
      .WillOnce(Return(std::vector<std::string>{
          "VRF_TABLE:vrf-0",
          "_VRF_TABLE:vrf-1",
          "VRF_TABLE:vrf-2",
      }));

  // We expect to read back only those 2 entries that have been installed by the
  // OA.
  EXPECT_THAT(
      GetAllAppDbVrfTableEntries(mock_app_db_client_),
      IsOkAndHolds(UnorderedElementsAre(EqualsProto(
                                            R"pb(
                                              table_name: "vrf_table"
                                              matches {
                                                name: "vrf_id"
                                                exact { str: "vrf-0" }
                                              }
                                              action { name: "no_action" }
                                            )pb"),
                                        EqualsProto(
                                            R"pb(
                                              table_name: "vrf_table"
                                              matches {
                                                name: "vrf_id"
                                                exact { str: "vrf-2" }
                                              }
                                              action { name: "no_action" }
                                            )pb"))));
}

TEST_F(VrfEntryTranslationTest, CannotTouchSonicDefaultVrf) {
  pdpi::IrTableEntry table_entry;
  ASSERT_TRUE(TextFormat::ParseFromString(R"pb(matches {
                                                 name: "vrf_id"
                                                 exact { str: "" }
                                               })pb",
                                          &table_entry));

  EXPECT_CALL(mock_vrf_table_, set(_, _, _, _)).Times(0);

  pdpi::IrWriteResponse response;
  response.add_statuses();
  EXPECT_OK(UpdateAppDbVrfTable(p4::v1::Update::INSERT, /*rpc_index=*/0,
                                table_entry, mock_vrf_table_,
                                mock_vrf_notifier_, mock_app_db_client_,
                                mock_state_db_client_, response));
  EXPECT_EQ(response.statuses(0).code(), google::rpc::Code::INVALID_ARGUMENT);
}

}  // namespace
}  // namespace sonic
}  // namespace p4rt_app
