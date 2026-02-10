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
#include "p4rt_app/sonic/response_handler.h"

#include <memory>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status_matchers.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4rt_app/sonic/adapters/mock_consumer_notifier_adapter.h"
#include "p4rt_app/sonic/adapters/mock_table_adapter.h"

namespace p4rt_app {
namespace sonic {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::testing::DoAll;
using ::testing::HasSubstr;
using ::testing::Return;
using ::testing::SetArgReferee;
using ::testing::Test;

// Swss string to indicate status of the transaction, these are coming from
// sonic-swss-common/common/status_code_util.h.
static const char kSwssSuccess[] = "SWSS_RC_SUCCESS";
static const char kSwssInternal[] = "SWSS_RC_INTERNAL";

std::vector<swss::FieldValueTuple> GetSwssOkResponse() {
  return std::vector<swss::FieldValueTuple>(
      {swss::FieldValueTuple("err_str", "")});
}

std::vector<swss::FieldValueTuple> GetSwssError(const std::string& message) {
  return std::vector<swss::FieldValueTuple>(
      {swss::FieldValueTuple("err_str", message)});
}

TEST(ResponseHandlerTest, SingleRequests) {
  MockConsumerNotifierAdapter mock_notifier;
  MockTableAdapter mock_app_db_client;
  MockTableAdapter mock_state_db_client;

  // We want the response to pass.
  EXPECT_CALL(mock_notifier, WaitForNotificationAndPop)
      .WillOnce(DoAll(SetArgReferee<0>(kSwssSuccess), SetArgReferee<1>("key0"),
                      SetArgReferee<2>(GetSwssOkResponse()), Return(true)));

  EXPECT_THAT(
      GetAndProcessResponseNotification(mock_notifier, mock_app_db_client,
                                        mock_state_db_client, "key0"),
      IsOkAndHolds(EqualsProto(R"pb(code: OK)pb")));
}

TEST(ResponseHandlerTest, MultipleRequests) {
  MockConsumerNotifierAdapter mock_notifier;
  MockTableAdapter mock_app_db_client;
  MockTableAdapter mock_state_db_client;

  // The test will wait for a response for 2 keys.
  pdpi::IrWriteResponse ir_write_response;
  absl::btree_map<std::string, pdpi::IrUpdateStatus*> key_to_status_map;
  key_to_status_map["key0"] = ir_write_response.add_statuses();
  key_to_status_map["key1"] = ir_write_response.add_statuses();

  // We expect both responses to pass.
  EXPECT_CALL(mock_notifier, WaitForNotificationAndPop)
      .WillOnce(DoAll(SetArgReferee<0>(kSwssSuccess), SetArgReferee<1>("key0"),
                      SetArgReferee<2>(GetSwssOkResponse()), Return(true)))
      .WillOnce(DoAll(SetArgReferee<0>(kSwssSuccess), SetArgReferee<1>("key1"),
                      SetArgReferee<2>(GetSwssOkResponse()), Return(true)));

  // The response path will successfully handle the response.
  EXPECT_OK(GetAndProcessResponseNotification(mock_notifier, mock_app_db_client,
                                              mock_state_db_client,
                                              key_to_status_map));
  EXPECT_THAT(ir_write_response, EqualsProto(R"pb(
                statuses { code: OK }
                statuses { code: OK }
              )pb"));
}

TEST(ResponseHandlerTest, MissingResponseValueFails) {
  MockConsumerNotifierAdapter mock_notifier;
  MockTableAdapter mock_app_db_client;
  MockTableAdapter mock_state_db_client;

  // The test will wait for a response for 2 keys.
  pdpi::IrWriteResponse ir_write_response;
  absl::btree_map<std::string, pdpi::IrUpdateStatus*> key_to_status_map;
  key_to_status_map["key0"] = nullptr;

  // We expect both responses to pass.
  EXPECT_CALL(mock_notifier, WaitForNotificationAndPop)
      .WillOnce(DoAll(SetArgReferee<0>(kSwssSuccess), SetArgReferee<1>("key0"),
                      SetArgReferee<2>(GetSwssOkResponse()), Return(true)));

  // The response path will successfully handle the response.
  EXPECT_THAT(GetAndProcessResponseNotification(
                  mock_notifier, mock_app_db_client, mock_state_db_client,
                  key_to_status_map),
              StatusIs(absl::StatusCode::kInternal));
}

TEST(ResponseHandlerTest, ResponsePathReturnsDuplicateKeys) {
  MockConsumerNotifierAdapter mock_notifier;
  MockTableAdapter mock_app_db_client;
  MockTableAdapter mock_state_db_client;

  // The test will wait for a response for 2 keys.
  pdpi::IrWriteResponse ir_write_response;
  absl::btree_map<std::string, pdpi::IrUpdateStatus*> key_to_status_map;
  key_to_status_map["key0"] = ir_write_response.add_statuses();
  key_to_status_map["key1"] = ir_write_response.add_statuses();

  // However, the response path retuns two results for the same key value.
  EXPECT_CALL(mock_notifier, WaitForNotificationAndPop)
      .WillOnce(DoAll(SetArgReferee<0>(kSwssSuccess), SetArgReferee<1>("key0"),
                      SetArgReferee<2>(GetSwssOkResponse()), Return(true)))
      .WillOnce(DoAll(SetArgReferee<0>(kSwssSuccess), SetArgReferee<1>("key0"),
                      SetArgReferee<2>(GetSwssOkResponse()), Return(true)));

  // We don't support sending duplicate keys so if we see duplicate keys
  // returned it is an internal failure.
  EXPECT_THAT(GetAndProcessResponseNotification(
                  mock_notifier, mock_app_db_client, mock_state_db_client,
                  key_to_status_map),
              StatusIs(absl::StatusCode::kInternal,
                       HasSubstr("received a duplicate key")));
}

// We compare the expected keys with all response keys by iterating over 2
// separate maps. Lower and higher value keys are handled slightly different
// (e.g. missing vs. extra).
TEST(ResponseHandlerTest, ResponsePathReturnsWrongKeyWithLowerValue) {
  MockConsumerNotifierAdapter mock_notifier;
  MockTableAdapter mock_app_db_client;
  MockTableAdapter mock_state_db_client;

  // The test will wait for a response for 2 keys.
  pdpi::IrWriteResponse ir_write_response;
  absl::btree_map<std::string, pdpi::IrUpdateStatus*> key_to_status_map;
  key_to_status_map["key1"] = ir_write_response.add_statuses();

  // However, the response path retuns an unexpected key.
  EXPECT_CALL(mock_notifier, WaitForNotificationAndPop)
      .WillOnce(DoAll(SetArgReferee<0>(kSwssSuccess), SetArgReferee<1>("key0"),
                      SetArgReferee<2>(GetSwssOkResponse()), Return(true)));

  // Since we're waiting for one key and got another the P4RT App is out of sync
  // with the OrchAgent, and we should return an internal error.
  EXPECT_THAT(GetAndProcessResponseNotification(
                  mock_notifier, mock_app_db_client, mock_state_db_client,
                  key_to_status_map),
              StatusIs(absl::StatusCode::kInternal,
                       HasSubstr("Got unexpected responses")));
}

// We compare the expected keys with all response keys by iterating over 2
// separate maps. Lower and higher value keys are handled slightly different
// (e.g. missing vs. extra).
TEST(ResponseHandlerTest, ResponsePathReturnsWrongKeyWithHigherValue) {
  MockConsumerNotifierAdapter mock_notifier;
  MockTableAdapter mock_app_db_client;
  MockTableAdapter mock_state_db_client;

  // The test will wait for a response for 2 keys.
  pdpi::IrWriteResponse ir_write_response;
  absl::btree_map<std::string, pdpi::IrUpdateStatus*> key_to_status_map;
  key_to_status_map["key1"] = ir_write_response.add_statuses();

  // However, the response path retuns an unexpected key.
  EXPECT_CALL(mock_notifier, WaitForNotificationAndPop)
      .WillOnce(DoAll(SetArgReferee<0>(kSwssSuccess), SetArgReferee<1>("key2"),
                      SetArgReferee<2>(GetSwssOkResponse()), Return(true)));

  // Since we're waiting for one key and got another the P4RT App is out of sync
  // with the OrchAgent, and we should return an internal error.
  EXPECT_THAT(GetAndProcessResponseNotification(
                  mock_notifier, mock_app_db_client, mock_state_db_client,
                  key_to_status_map),
              StatusIs(absl::StatusCode::kInternal,
                       HasSubstr("Got unexpected responses")));
}

TEST(ResponseHandlerTest, ResponsePathFails) {
  MockConsumerNotifierAdapter mock_notifier;
  MockTableAdapter mock_app_db_client;
  MockTableAdapter mock_state_db_client;

  // The test will wait for a response for 1 key.
  pdpi::IrWriteResponse ir_write_response;
  absl::btree_map<std::string, pdpi::IrUpdateStatus*> key_to_status_map;
  key_to_status_map["key0"] = ir_write_response.add_statuses();

  // However, that response will return false. Signaling an error with the
  // return path itself. In which case we want to return an internal error.
  EXPECT_CALL(mock_notifier, WaitForNotificationAndPop).WillOnce(Return(false));
  EXPECT_THAT(
      GetAndProcessResponseNotification(mock_notifier, mock_app_db_client,
                                        mock_state_db_client,
                                        key_to_status_map),
      StatusIs(absl::StatusCode::kInternal, HasSubstr("timed out or failed")));
}

TEST(ResponseHandlerTest, ResponsePathDoesNotSetErrorTuple) {
  MockConsumerNotifierAdapter mock_notifier;
  MockTableAdapter mock_app_db_client;
  MockTableAdapter mock_state_db_client;

  // The test will wait for a response for 1 key.
  pdpi::IrWriteResponse ir_write_response;
  absl::btree_map<std::string, pdpi::IrUpdateStatus*> key_to_status_map;
  key_to_status_map["key0"] = ir_write_response.add_statuses();

  // However, the response path doesn't get populated (i.e. missing
  // SetArgReferee<2>).
  EXPECT_CALL(mock_notifier, WaitForNotificationAndPop)
      .WillOnce(DoAll(SetArgReferee<0>(kSwssSuccess), SetArgReferee<1>("key0"),
                      Return(true)));
  EXPECT_THAT(
      GetAndProcessResponseNotification(mock_notifier, mock_app_db_client,
                                        mock_state_db_client,
                                        key_to_status_map),
      StatusIs(absl::StatusCode::kInternal, HasSubstr("should not be empty")));
}

TEST(ResponseHandlerTest, ResponsePathSetsWrongErrorString) {
  MockConsumerNotifierAdapter mock_notifier;
  MockTableAdapter mock_app_db_client;
  MockTableAdapter mock_state_db_client;

  // The test will wait for a response for 1 key.
  pdpi::IrWriteResponse ir_write_response;
  absl::btree_map<std::string, pdpi::IrUpdateStatus*> key_to_status_map;
  key_to_status_map["key0"] = ir_write_response.add_statuses();

  // Not 'err_str' in the pop call that is returned in the response.
  EXPECT_CALL(mock_notifier, WaitForNotificationAndPop)
      .WillOnce(DoAll(SetArgReferee<0>(kSwssSuccess), SetArgReferee<1>("key0"),
                      SetArgReferee<2>(std::vector<swss::FieldValueTuple>(
                          {swss::FieldValueTuple("not_err_str", "Success")})),
                      Return(true)));
  EXPECT_THAT(GetAndProcessResponseNotification(
                  mock_notifier, mock_app_db_client, mock_state_db_client,
                  key_to_status_map),
              StatusIs(absl::StatusCode::kInternal));
}

TEST(ResponseHandlerTest, CleanupAppDbWithAnUpdate) {
  MockConsumerNotifierAdapter mock_notifier;
  MockTableAdapter mock_app_db_client;
  MockTableAdapter mock_state_db_client;

  // The test will wait for a response for 2 keys.
  pdpi::IrWriteResponse ir_write_response;
  absl::btree_map<std::string, pdpi::IrUpdateStatus*> key_to_status_map;
  key_to_status_map["key0"] = ir_write_response.add_statuses();
  key_to_status_map["key1"] = ir_write_response.add_statuses();

  // The first key will update succefully, but the second will fail.
  EXPECT_CALL(mock_notifier, WaitForNotificationAndPop)
      .WillOnce(DoAll(SetArgReferee<0>(kSwssSuccess), SetArgReferee<1>("key0"),
                      SetArgReferee<2>(GetSwssOkResponse()), Return(true)))
      .WillOnce(DoAll(SetArgReferee<0>(kSwssInternal), SetArgReferee<1>("key1"),
                      SetArgReferee<2>(GetSwssError("my_error")),
                      Return(true)));

  // The failure should invoke a cleanup response for the second key. When
  // checking the AppStateDb we return a result which implies the entry existed
  // before and should be reverted back to the old values (i.e. call hmset to
  // the AppDb entry).
  EXPECT_CALL(mock_state_db_client, get("key1"))
      .WillOnce(Return(std::vector<std::pair<std::string, std::string>>{
          {"action", "set_port_and_src_mac"},
      }));
  EXPECT_CALL(mock_app_db_client, set).Times(1);

  // Nothing goes wrong with the response path itself so we expect it to return
  // okay.
  EXPECT_OK(GetAndProcessResponseNotification(mock_notifier, mock_app_db_client,
                                              mock_state_db_client,
                                              key_to_status_map));

  // However, we expect the status to reflect the error.
  EXPECT_THAT(ir_write_response, EqualsProto(R"pb(
                statuses { code: OK }
                statuses { code: INTERNAL message: "my_error" }
              )pb"));
}

TEST(ResponseHandlerTest, CleanupAppDbWithADelete) {
  MockConsumerNotifierAdapter mock_notifier;
  MockTableAdapter mock_app_db_client;
  MockTableAdapter mock_state_db_client;

  // The test will wait for a response for 2 keys.
  pdpi::IrWriteResponse ir_write_response;
  absl::btree_map<std::string, pdpi::IrUpdateStatus*> key_to_status_map;
  key_to_status_map["key0"] = ir_write_response.add_statuses();
  key_to_status_map["key1"] = ir_write_response.add_statuses();

  // The first key will fail, but the second will update succefully.
  EXPECT_CALL(mock_notifier, WaitForNotificationAndPop)
      .WillOnce(DoAll(SetArgReferee<0>(kSwssInternal), SetArgReferee<1>("key0"),
                      SetArgReferee<2>(GetSwssError("my_error")), Return(true)))
      .WillOnce(DoAll(SetArgReferee<0>(kSwssSuccess), SetArgReferee<1>("key1"),
                      SetArgReferee<2>(GetSwssOkResponse()), Return(true)));

  // The failure should invoke a cleanup response for the first key. When
  // checking the AppStateDb we do not return any values which implies the entry
  // did not exist before and the current AppDb entry should be deleted.
  EXPECT_CALL(mock_state_db_client, get("key0"))
      .WillOnce(Return(std::vector<std::pair<std::string, std::string>>{}));
  EXPECT_CALL(mock_app_db_client, del("key0")).Times(1);

  // Nothing goes wrong with the response path itself so we expect it to return
  // okay.
  EXPECT_OK(GetAndProcessResponseNotification(mock_notifier, mock_app_db_client,
                                              mock_state_db_client,
                                              key_to_status_map));

  // However, we expect the status to reflect the error.
  EXPECT_THAT(ir_write_response, EqualsProto(R"pb(
                statuses { code: INTERNAL message: "my_error" }
                statuses { code: OK }
              )pb"));
}

struct SwssToP4rtErrorMapping {
  std::string swss_error;
  google::rpc::Code p4rt_error;
};

using ResponseHandlerErrorCodeTest =
    ::testing::TestWithParam<SwssToP4rtErrorMapping>;

TEST_P(ResponseHandlerErrorCodeTest, VerifySwssToGrpcMapping) {
  MockConsumerNotifierAdapter mock_notifier;
  MockTableAdapter mock_app_db_client;
  MockTableAdapter mock_state_db_client;

  // The test will wait for a response for 1 key.
  pdpi::IrUpdateStatus ir_update_status;
  absl::btree_map<std::string, pdpi::IrUpdateStatus*> key_to_status_map;
  key_to_status_map["key0"] = &ir_update_status;

  // The response will always fail, and then delete the current AppDb entry.
  EXPECT_CALL(mock_notifier, WaitForNotificationAndPop)
      .WillOnce(DoAll(
          SetArgReferee<0>(GetParam().swss_error), SetArgReferee<1>("key0"),
          SetArgReferee<2>(GetSwssError("my_error")), Return(true)));
  EXPECT_CALL(mock_state_db_client, get("key0"))
      .WillOnce(Return(std::vector<std::pair<std::string, std::string>>{}));
  EXPECT_CALL(mock_app_db_client, del("key0")).Times(1);

  EXPECT_OK(GetAndProcessResponseNotification(mock_notifier, mock_app_db_client,
                                              mock_state_db_client,
                                              key_to_status_map));
  EXPECT_EQ(ir_update_status.code(), GetParam().p4rt_error);
  EXPECT_EQ(ir_update_status.message(), "my_error");
}

INSTANTIATE_TEST_SUITE_P(
    ResponseHandleErrorTest, ResponseHandlerErrorCodeTest,
    ::testing::ValuesIn<SwssToP4rtErrorMapping>({
        {
            .swss_error = "SWSS_RC_INVALID_PARAM",
            .p4rt_error = google::rpc::Code::INVALID_ARGUMENT,
        },
        {
            .swss_error = "SWSS_RC_DEADLINE_EXCEEDED",
            .p4rt_error = google::rpc::Code::DEADLINE_EXCEEDED,
        },
        {
            .swss_error = "SWSS_RC_UNAVAIL",
            .p4rt_error = google::rpc::Code::UNAVAILABLE,
        },
        {
            .swss_error = "SWSS_RC_NOT_FOUND",
            .p4rt_error = google::rpc::Code::NOT_FOUND,
        },
        {
            .swss_error = "SWSS_RC_NO_MEMORY",
            .p4rt_error = google::rpc::Code::INTERNAL,
        },
        {
            .swss_error = "SWSS_RC_PERMISSION_DENIED",
            .p4rt_error = google::rpc::Code::PERMISSION_DENIED,
        },
        {
            .swss_error = "SWSS_RC_FULL",
            .p4rt_error = google::rpc::Code::RESOURCE_EXHAUSTED,
        },
        {
            .swss_error = "SWSS_RC_IN_USE",
            .p4rt_error = google::rpc::Code::INVALID_ARGUMENT,
        },
        {
            .swss_error = "SWSS_RC_INTERNAL",
            .p4rt_error = google::rpc::Code::INTERNAL,
        },
        {
            .swss_error = "SWSS_RC_UNKNOWN",
            .p4rt_error = google::rpc::Code::UNKNOWN,
        },
        {
            .swss_error = "SWSS_RC_UNIMPLEMENTED",
            .p4rt_error = google::rpc::Code::UNIMPLEMENTED,
        },
        {
            .swss_error = "SWSS_RC_NOT_EXECUTED",
            .p4rt_error = google::rpc::Code::ABORTED,
        },
    }),
    [](const testing::TestParamInfo<ResponseHandlerErrorCodeTest::ParamType>&
           info) { return info.param.swss_error; });

}  // namespace
}  // namespace sonic
}  // namespace p4rt_app
