/*
 * Copyright 2020 Google LLC
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
#include "p4rt_app/sonic/response_handler.h"

#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "absl/container/btree_map.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/escaping.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "google/rpc/code.pb.h"
#include "gutil/gutil/status.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4rt_app/sonic/adapters/consumer_notifier_adapter.h"
#include "p4rt_app/sonic/adapters/table_adapter.h"
#include "p4rt_app/sonic/adapters/zmq_producer_state_table_adapter.h"
#include "swss/rediscommand.h"
#include "swss/schema.h"
#include "swss/status_code_util.h"
#include "swss/table.h"

namespace p4rt_app {
namespace sonic {
namespace {

// Converts a SWSS error code into a Google RPC code.
google::rpc::Code SwssToP4RTErrorCode(const std::string& status_str) {
  switch (swss::strToStatusCode(status_str)) {
    case swss::StatusCode::SWSS_RC_SUCCESS:
      return google::rpc::Code::OK;
    case swss::StatusCode::SWSS_RC_UNKNOWN:
      return google::rpc::Code::UNKNOWN;
    case swss::StatusCode::SWSS_RC_IN_USE:
    case swss::StatusCode::SWSS_RC_INVALID_PARAM:
      return google::rpc::Code::INVALID_ARGUMENT;
    case swss::StatusCode::SWSS_RC_DEADLINE_EXCEEDED:
      return google::rpc::Code::DEADLINE_EXCEEDED;
    case swss::StatusCode::SWSS_RC_NOT_FOUND:
      return google::rpc::Code::NOT_FOUND;
    case swss::StatusCode::SWSS_RC_EXISTS:
      return google::rpc::Code::ALREADY_EXISTS;
    case swss::StatusCode::SWSS_RC_PERMISSION_DENIED:
      return google::rpc::Code::PERMISSION_DENIED;
    case swss::StatusCode::SWSS_RC_FULL:
      return google::rpc::Code::RESOURCE_EXHAUSTED;
    case swss::StatusCode::SWSS_RC_UNIMPLEMENTED:
      return google::rpc::Code::UNIMPLEMENTED;
    case swss::StatusCode::SWSS_RC_INTERNAL:
    case swss::StatusCode::SWSS_RC_NO_MEMORY:
      return google::rpc::Code::INTERNAL;
    case swss::StatusCode::SWSS_RC_UNAVAIL:
      return google::rpc::Code::UNAVAILABLE;
    case swss::StatusCode::SWSS_RC_NOT_EXECUTED:
      return google::rpc::Code::ABORTED;
    default:
      return google::rpc::Code::UNKNOWN;
  }
}

// Same as GetAppDbResponses() but over the zmq connection.
absl::StatusOr<absl::btree_map<std::string, pdpi::IrUpdateStatus>>
GetZmqResponses(int expected_response_count,
                ZmqProducerStateTableAdapter& producer) {
  absl::btree_map<std::string, pdpi::IrUpdateStatus> key_to_status_map;
  if (expected_response_count == 0) {
    return key_to_status_map;
  }

  std::string db_name;
  std::string table_name;
  std::vector<std::shared_ptr<swss::KeyOpFieldsValuesTuple>> kfvs;
  bool response = producer.wait(db_name, table_name, kfvs);
  if (!response) {
    return gutil::InternalErrorBuilder()
           << "[OrchAgent] P4RT App timed out on waiting for "
              "the ZMQ response from OrchAgent.";
  }

  if (kfvs.size() != expected_response_count) {
    return gutil::InternalErrorBuilder()
           << "[OrchaAgent]P4RT App did not get expected "
           << expected_response_count
           << " responses on the ZMQ channel from the OrchAgent but got "
           << kfvs.size();
  }

  if (db_name != "APPL_DB" || table_name != APP_P4RT_TABLE_NAME) {
    return gutil::InternalErrorBuilder()
           << "[OrchAgent] P4RT App did not receive the correct ZMQ response "
              "from the OrchAgent."
           << "Expected: APPL_DB table " << APP_P4RT_TABLE_NAME
           << " but got: " << db_name << " table " << table_name;
  }

  for (const auto& kfv : kfvs) {
    std::string actual_key;
    std::vector<swss::FieldValueTuple> value_tuples;

    actual_key = kfvKey(*kfv);
    value_tuples = kfvFieldsValues(*kfv);
    if (value_tuples.empty()) {
      return gutil::InternalErrorBuilder()
             << "Notification response for '" << actual_key
             << "' should not be empty.";
    }

    pdpi::IrUpdateStatus result;
    const swss::FieldValueTuple& first_tuple = value_tuples[0];
    // Sanitize any response messages coming from the OA layers.
    result.set_code(SwssToP4RTErrorCode(fvField(first_tuple)));
    result.set_message(absl::CHexEscape(fvValue(first_tuple)));

    // Insert into the responses map, but do not allow duplicates.
    if (!key_to_status_map.insert({actual_key, result}).second) {
      return gutil::InternalErrorBuilder()
             << "[P4RT App] The response path received a duplicate key from "
                "the AppDb: "
             << actual_key;
    }
  }
  return key_to_status_map;
}

// Get expected responses from the notification channel.
// It is required to get all the expected responses first and then lookup for
// the individual responses because the order of entries written to APP_DB by
// p4rt does not match the order in which the entries are pulled out from
// APP_DB. Hence, we expect to see the expected responses but not in the same
// order.
absl::StatusOr<absl::btree_map<std::string, pdpi::IrUpdateStatus>>
GetAppDbResponses(int expected_response_count,
                  ConsumerNotifierAdapter& notification_interface) {
  absl::btree_map<std::string, pdpi::IrUpdateStatus> key_to_status_map;

  // Loop through and get the expected notification responses from Orchagent,
  // max timeout 10 minutes. OrchAgent sends the status code as string in the
  // op, key as data and the actual table entries as value_tuples.
  for (int i = 0; i < expected_response_count; i++) {
    std::string status_str;
    std::string actual_key;
    std::vector<swss::FieldValueTuple> value_tuples;

    if (!notification_interface.WaitForNotificationAndPop(
            status_str, actual_key, value_tuples, /*timeout_ms=*/10 * 60000)) {
      return gutil::InternalErrorBuilder()
             << "[OrchAgent] P4RT App timed out or failed waiting on a AppDB "
                "response from the OrchAgent.";
    }
    if (value_tuples.empty()) {
      return gutil::InternalErrorBuilder()
             << "Notification response for '" << actual_key
             << "' should not be empty.";
    }

    pdpi::IrUpdateStatus result;
    // The first element in the values vector is the detailed error message in
    // the form of ("err_str", <error message>).
    const swss::FieldValueTuple& first_tuple = value_tuples[0];
    if (fvField(first_tuple) != "err_str") {
      return gutil::InternalErrorBuilder()
             << "[OrchAgent] responded with '" << fvField(first_tuple)
             << "' as its first value, but P4RT App was expecting 'err_str'.";
    } else {
      // Sanatize any response messages coming from the OA layers.
      result.set_code(SwssToP4RTErrorCode(status_str));
      result.set_message(absl::CHexEscape(fvValue(first_tuple)));
    }

    // Insert into the responses map, but do not allow duplicates.
    if (bool success = key_to_status_map.insert({actual_key, result}).second;
        !success) {
      return gutil::InternalErrorBuilder()
             << "[P4RT App] The response path received a duplicate key from "
                "the AppDb: "
             << actual_key;
    }
  }
  return key_to_status_map;
}

// Restore APPL_DB to the last successful state.
absl::Status RestoreApplDb(TableAdapter& app_db_table,
                           TableAdapter& state_db_table,
                           const std::string& key) {
  // Query the APPL_STATE_DB with the same key as in APPL_DB.
  std::vector<std::pair<std::string, std::string>> values =
      state_db_table.get(key);
  if (values.empty()) {
    LOG(INFO) << "Restoring (by delete) AppDb entry: " << key;
    app_db_table.del(key);
  } else {
    // Update APPL_DB with the retrieved values from APPL_STATE_DB.
    LOG(INFO) << "Restoring (by update) AppDb entry: " << key;
    app_db_table.del(key);
    app_db_table.set(key, values);
  }

  return absl::OkStatus();
}

absl::Status UpdateResponsesAndRestoreState(
    absl::btree_map<std::string, pdpi::IrUpdateStatus*>& key_to_status_map,
    const absl::btree_map<std::string, pdpi::IrUpdateStatus>&
        response_status_map,
    TableAdapter* app_db_table, TableAdapter* state_db_table) {
  // We have a map of all the keys we expect to have a response for, and a map
  // of all the keys returned by the OrchAgent. If anything doesn't match up
  // then we have a problem, and should raise an internal error because of it.
  auto expected_iter = key_to_status_map.begin();
  auto response_iter = response_status_map.begin();
  std::vector<std::string> error_messages;
  while (expected_iter != key_to_status_map.end() &&
         response_iter != response_status_map.end()) {
    const auto& expected_key = expected_iter->first;
    auto* expected_status = expected_iter->second;
    const auto& response_key = response_iter->first;
    const auto& response_status = response_iter->second;

    if (expected_key < response_key) {
      // Missing an expected response.
      error_messages.push_back(
          absl::StrCat("Missing response for: ", expected_key));
      ++expected_iter;
    } else if (expected_key > response_key) {
      // Got an extra response.
      error_messages.push_back(
          absl::StrCat("Extra response for: ", response_key));
      ++response_iter;
    } else {
      // If we're waiting for a response then we should have a place to put the
      // status.
      if (expected_status == nullptr) {
        LOG(ERROR) << "Cannot populate response for: " << expected_key;
        return gutil::InternalErrorBuilder()
               << "Response path is missing status object for key: "
               << expected_key;
      }

      // We got the expected response. However, if the OrchAgent failed to
      // handle it correctly then we need to cleanup state in the AppDb.
      if (response_iter->second.code() != google::rpc::Code::OK) {
        *expected_status = response_iter->second;
        LOG(WARNING) << "OrchAgent could not handle AppDb entry '"
                     << response_key << "'. Failed with: "
                     << response_status.ShortDebugString();
        if (app_db_table != nullptr && state_db_table != nullptr) {
          RETURN_IF_ERROR(
              RestoreApplDb(*app_db_table, *state_db_table, response_key));
        }
      }
      ++expected_iter;
      ++response_iter;
    }
  }

  // There should be no unvisited keys in either the expected or response maps.
  while (expected_iter != key_to_status_map.end()) {
    error_messages.push_back(
        absl::StrCat("Missing response for: ", expected_iter->first));
    ++expected_iter;
  }
  while (response_iter != response_status_map.end()) {
    error_messages.push_back(
        absl::StrCat("Extra response for: ", response_iter->first));
    ++response_iter;
  }

  if (!error_messages.empty()) {
    return gutil::InternalErrorBuilder()
           << "Got unexpected responses:\n  "
           << absl::StrJoin(error_messages, "\n  ");
  }
  return absl::OkStatus();
}

}  // namespace

absl::Status GetAndProcessResponseNotification(
    ConsumerNotifierAdapter& notification_interface, TableAdapter& app_db_table,
    TableAdapter& state_db_table,
    absl::btree_map<std::string, pdpi::IrUpdateStatus*>& key_to_status_map) {
  ASSIGN_OR_RETURN(
      auto response_status_map,
      GetAppDbResponses(key_to_status_map.size(), notification_interface));
  return UpdateResponsesAndRestoreState(key_to_status_map, response_status_map,
                                        &app_db_table, &state_db_table);
}

absl::StatusOr<pdpi::IrUpdateStatus> GetAndProcessResponseNotification(
    ConsumerNotifierAdapter& notification_interface, TableAdapter& app_db_table,
    TableAdapter& state_db_table, const std::string& key) {
  pdpi::IrUpdateStatus local_status;
  absl::btree_map<std::string, pdpi::IrUpdateStatus*> key_to_status_map;
  key_to_status_map[key] = &local_status;

  RETURN_IF_ERROR(GetAndProcessResponseNotification(
      notification_interface, app_db_table, state_db_table, key_to_status_map));

  return local_status;
}

absl::StatusOr<pdpi::IrUpdateStatus>
GetAndProcessResponseNotificationWithoutRevertingState(
    ZmqProducerStateTableAdapter& producer, const std::string& key) {
  pdpi::IrUpdateStatus local_status;
  absl::btree_map<std::string, pdpi::IrUpdateStatus*> key_to_status_map;
  key_to_status_map[key] = &local_status;

  RETURN_IF_ERROR(GetAndProcessResponseNotificationWithoutRevertingState(
      producer, key_to_status_map));
  return local_status;
}

absl::Status GetAndProcessResponseNotificationWithoutRevertingState(
    ZmqProducerStateTableAdapter& producer,
    absl::btree_map<std::string, pdpi::IrUpdateStatus*>& key_to_status_map) {
  ASSIGN_OR_RETURN(auto response_status_map,
                   GetZmqResponses(key_to_status_map.size(), producer));

  return UpdateResponsesAndRestoreState(key_to_status_map, response_status_map,
                                        /*app_db_table=*/nullptr,
                                        /*state_db_table=*/nullptr);
}

}  // namespace sonic
}  // namespace p4rt_app
