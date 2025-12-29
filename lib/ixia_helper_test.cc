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
#include "lib/ixia_helper.h"

#include <string>

#include "absl/log/check.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status_matchers.h"
#include "include/nlohmann/json.hpp"
#include "lib/ixia_helper.pb.h"
#include "lib/utils/json_test_utils.h"
#include "lib/utils/json_utils.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/mock_generic_testbed.h"

namespace pins_test::ixia {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::pins_test::JsonIs;

using ::testing::Eq;
using ::testing::ExplainMatchResult;
using ::testing::HasSubstr;
using ::testing::Return;
using ::testing::StartsWith;

TEST(FindIdByField, FindsId) {
  static constexpr absl::string_view kArray =
      R"json([
      {"id":1, "name":"Port"},
      {"id":2, "name":"Traffic"}
      ])json";
  EXPECT_THAT(
      FindIdByField(thinkit::HttpResponse{.response = std::string(kArray)},
                    "name", "Traffic"),
      IsOkAndHolds(2));
}

TEST(FindIdByField, FindsIdForNonstringValue) {
  static constexpr absl::string_view kArray =
      R"json([
      {"id":1, "counter":12},
      {"id":2, "counter":15}
      ])json";
  EXPECT_THAT(
      FindIdByField(thinkit::HttpResponse{.response = std::string(kArray)},
                    "counter", "12"),
      IsOkAndHolds(1));
}

TEST(FindIdByField, DoesntFindId) {
  static constexpr absl::string_view kArray =
      R"json([
      {"id":1, "name":"Port"},
      {"id":2, "name":"Traffic"}
      ])json";
  EXPECT_THAT(
      FindIdByField(thinkit::HttpResponse{.response = std::string(kArray)},
                    "name", "Flow"),
      StatusIs(absl::StatusCode::kNotFound));
}

TEST(FindIdByField, DoesntFindIdNonexistentField) {
  static constexpr absl::string_view kArray =
      R"json([
      {"id":1, "name":"Port"},
      {"id":2, "name":"Traffic"}
      ])json";
  EXPECT_THAT(
      FindIdByField(thinkit::HttpResponse{.response = std::string(kArray)},
                    "value", "Flow"),
      StatusIs(absl::StatusCode::kNotFound));
}

TEST(ParseTrafficItemStats, ParsesExampleCorrectly) {
  static constexpr absl::string_view kExample = R"json({
      "rowValues": {
        "arg1": [
          [
            "Ethernet - 001",
            "Ethernet - 003",
            "Unicast Traffic",
            "Unicast Traffic-Main Traffic - Flow Group 0001",
            "115052349",
            "115052349",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "174189256386",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "1088",
            "1081",
            "6314",
            "00:00:00.175",
            "00:00:08.885"
          ]
        ],
        "arg2": [
          [
            "Ethernet - 002",
            "Ethernet - 003",
            "Unicast Traffic #1",
            "Unicast Traffic #1-Secondary traffic - Flow Group 0001",
            "105",
            "105",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "158970",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "3711",
            "1093",
            "6306",
            "00:00:00.175",
            "00:00:00.175"
          ]
        ]
      },
      "isReady": true,
      "columnCaptions": [
        "Tx Port",
        "Rx Port",
        "Traffic Item",
        "Flow Group",
        "Tx Frames",
        "Rx Frames",
        "Frames Delta",
        "Loss %",
        "Tx Frame Rate",
        "Rx Frame Rate",
        "Tx L1 Rate (bps)",
        "Rx L1 Rate (bps)",
        "Rx Bytes",
        "Tx Rate (Bps)",
        "Rx Rate (Bps)",
        "Tx Rate (bps)",
        "Rx Rate (bps)",
        "Tx Rate (Kbps)",
        "Rx Rate (Kbps)",
        "Tx Rate (Mbps)",
        "Rx Rate (Mbps)",
        "Store-Forward Avg Latency (ns)",
        "Store-Forward Min Latency (ns)",
        "Store-Forward Max Latency (ns)",
        "First TimeStamp",
        "Last TimeStamp"
      ]
    })json";

  EXPECT_THAT(ParseTrafficItemStats(kExample), IsOkAndHolds(EqualsProto(R"pb(
                stats_by_traffic_item {
                  key: "Unicast Traffic"
                  value: {
                    tx_port: "Ethernet - 001"
                    rx_port: "Ethernet - 003"
                    traffic_item_name: "Unicast Traffic"
                    num_tx_frames: 115052349
                    num_rx_frames: 115052349
                    rx_bytes: 174189256386
                    first_time_stamp: 0.175
                    last_time_stamp: 8.885

                  }
                }

                stats_by_traffic_item {
                  key: "Unicast Traffic #1"
                  value: {
                    tx_port: "Ethernet - 002"
                    rx_port: "Ethernet - 003"
                    traffic_item_name: "Unicast Traffic #1"
                    num_tx_frames: 105
                    num_rx_frames: 105
                    rx_bytes: 158970
                    first_time_stamp: 0.175
                    last_time_stamp: 0.175
                  }
                }
              )pb")));
}

TEST(ParseTrafficItemStats, ParsesTrafficItemStats) {
  static constexpr absl::string_view kExample = R"json({
      "rowValues": {
        "arg1": [
          [
            "Unicast Traffic",
            "115052349",
            "115052349",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "174189256386",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "1088",
            "1081",
            "6314",
            "00:00:00.175",
            "00:00:08.885"
          ]
        ],
        "arg2": [
          [
            "Unicast Traffic #1",
            "105",
            "105",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "158970",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "3711",
            "1093",
            "6306",
            "00:00:00.175",
            "00:00:00.175"
          ]
        ]
      },
      "isReady": true,
      "columnCaptions": [
        "Traffic Item",
        "Tx Frames",
        "Rx Frames",
        "Frames Delta",
        "Loss %",
        "Tx Frame Rate",
        "Rx Frame Rate",
        "Tx L1 Rate (bps)",
        "Rx L1 Rate (bps)",
        "Rx Bytes",
        "Tx Rate (Bps)",
        "Rx Rate (Bps)",
        "Tx Rate (bps)",
        "Rx Rate (bps)",
        "Tx Rate (Kbps)",
        "Rx Rate (Kbps)",
        "Tx Rate (Mbps)",
        "Rx Rate (Mbps)",
        "Store-Forward Avg Latency (ns)",
        "Store-Forward Min Latency (ns)",
        "Store-Forward Max Latency (ns)",
        "First TimeStamp",
        "Last TimeStamp"
      ]
    })json";

  EXPECT_THAT(ParseTrafficItemStats(kExample), IsOkAndHolds(EqualsProto(R"pb(
                stats_by_traffic_item {
                  key: "Unicast Traffic"
                  value: {
                    traffic_item_name: "Unicast Traffic"
                    num_tx_frames: 115052349
                    num_rx_frames: 115052349
                    rx_bytes: 174189256386
                    first_time_stamp: 0.175
                    last_time_stamp: 8.885

                  }
                }

                stats_by_traffic_item {
                  key: "Unicast Traffic #1"
                  value: {
                    traffic_item_name: "Unicast Traffic #1"
                    num_tx_frames: 105
                    num_rx_frames: 105
                    rx_bytes: 158970
                    first_time_stamp: 0.175
                    last_time_stamp: 0.175
                  }
                }
              )pb")));
}

TEST(ParseFlowStats, ParsesMultipleFlowsPerTrafficItem) {
  static constexpr absl::string_view kExample = R"json({
      "rowValues": {
        "arg1": [
          [
            "Ethernet - 001",
            "Ethernet - 003",
            "Unicast Traffic",
            "Unicast Traffic-Main Traffic - Flow Group 0001",
            "115052349",
            "115052349",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "174189256386",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "1088",
            "1081",
            "6314",
            "00:00:00.175",
            "00:00:08.885"
          ]
        ],
        "arg2": [
          [
            "Ethernet - 002",
            "Ethernet - 003",
            "Unicast Traffic",
            "Unicast Traffic-Main Traffic - Flow Group 0002",
            "115052349",
            "115052349",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "174189256386",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "1088",
            "1081",
            "6314",
            "00:00:00.175",
            "00:00:08.885"
          ]
        ],
        "arg3": [
          [
            "Ethernet - 002",
            "Ethernet - 003",
            "Unicast Traffic #1",
            "Unicast Traffic #1-Secondary traffic - Flow Group 0001",
            "105",
            "105",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "158970",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "3711",
            "1093",
            "6306",
            "00:00:00.175",
            "00:00:00.175"
          ]
        ]
      },
      "isReady": true,
      "columnCaptions": [
        "Tx Port",
        "Rx Port",
        "Traffic Item",
        "Flow Group",
        "Tx Frames",
        "Rx Frames",
        "Frames Delta",
        "Loss %",
        "Tx Frame Rate",
        "Rx Frame Rate",
        "Tx L1 Rate (bps)",
        "Rx L1 Rate (bps)",
        "Rx Bytes",
        "Tx Rate (Bps)",
        "Rx Rate (Bps)",
        "Tx Rate (bps)",
        "Rx Rate (bps)",
        "Tx Rate (Kbps)",
        "Rx Rate (Kbps)",
        "Tx Rate (Mbps)",
        "Rx Rate (Mbps)",
        "Store-Forward Avg Latency (ns)",
        "Store-Forward Min Latency (ns)",
        "Store-Forward Max Latency (ns)",
        "First TimeStamp",
        "Last TimeStamp"
      ]
    })json";

  EXPECT_THAT(ParseFlowStats(kExample), IsOkAndHolds(EqualsProto(R"pb(
                stats_by_traffic_item {
                  key: "Unicast Traffic"
                  value {
                    flow_stats {
                      tx_port: "Ethernet - 001"
                      rx_port: "Ethernet - 003"
                      traffic_item_name: "Unicast Traffic"
                      num_tx_frames: 115052349
                      num_rx_frames: 115052349
                      rx_bytes: 174189256386
                      first_time_stamp: 0.175
                      last_time_stamp: 8.885
                    }
                    flow_stats {
                      tx_port: "Ethernet - 002"
                      rx_port: "Ethernet - 003"
                      traffic_item_name: "Unicast Traffic"
                      num_tx_frames: 115052349
                      num_rx_frames: 115052349
                      rx_bytes: 174189256386
                      first_time_stamp: 0.175
                      last_time_stamp: 8.885
                    }
                  }
                }

                stats_by_traffic_item {
                  key: "Unicast Traffic #1"
                  value {
                    flow_stats {
                      tx_port: "Ethernet - 002"
                      rx_port: "Ethernet - 003"
                      traffic_item_name: "Unicast Traffic #1"
                      num_tx_frames: 105
                      num_rx_frames: 105
                      rx_bytes: 158970
                      first_time_stamp: 0.175
                      last_time_stamp: 0.175
                    }
                  }
                }
              )pb")));
}

TEST(IxiaHelper, ParseMissingTimestamps) {
  static constexpr absl::string_view kExample = R"json({
      "rowValues": {
        "arg1": [
          [
            "Ethernet - 001",
            "Ethernet - 003",
            "Unicast Traffic",
            "Unicast Traffic-Main Traffic - Flow Group 0001",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "1088",
            "1081",
            "6314",
            "",
            ""
          ]
        ]
      },
      "isReady": true,
      "columnCaptions": [
        "Tx Port",
        "Rx Port",
        "Traffic Item",
        "Flow Group",
        "Tx Frames",
        "Rx Frames",
        "Frames Delta",
        "Loss %",
        "Tx Frame Rate",
        "Rx Frame Rate",
        "Tx L1 Rate (bps)",
        "Rx L1 Rate (bps)",
        "Rx Bytes",
        "Tx Rate (Bps)",
        "Rx Rate (Bps)",
        "Tx Rate (bps)",
        "Rx Rate (bps)",
        "Tx Rate (Kbps)",
        "Rx Rate (Kbps)",
        "Tx Rate (Mbps)",
        "Rx Rate (Mbps)",
        "Store-Forward Avg Latency (ns)",
        "Store-Forward Min Latency (ns)",
        "Store-Forward Max Latency (ns)",
        "First TimeStamp",
        "Last TimeStamp"
      ]
    })json";

  EXPECT_THAT(ParseTrafficItemStats(kExample), IsOkAndHolds(EqualsProto(R"pb(
                stats_by_traffic_item {
                  key: "Unicast Traffic"
                  value: {
                    tx_port: "Ethernet - 001"
                    rx_port: "Ethernet - 003"
                    traffic_item_name: "Unicast Traffic"
                    num_tx_frames: 0
                    num_rx_frames: 0
                    rx_bytes: 0
                    first_time_stamp: 0.0
                    last_time_stamp: 0.0
                  }
                }
              )pb")));
}

TEST(IxiaHelper, NoTimestampIsZeroRate) {
  EXPECT_THAT(
      BytesPerSecondReceived(*gutil::ParseTextProto<TrafficItemStats>(R"pb(
        tx_port: "Ethernet - 001"
        rx_port: "Ethernet - 003"
        traffic_item_name: "Unicast Traffic"
        num_tx_frames: 0
        num_rx_frames: 0
        rx_bytes: 0
        first_time_stamp: 0.0
        last_time_stamp: 0.0
      )pb")),
      Eq(0.0));
}

TEST(IxiaHelper, SendAndWaitForCompleteImmediateSuccess) {
  thinkit::MockGenericTestbed mock_generic_testbed;
  EXPECT_CALL(
      mock_generic_testbed,
      SendRestRequestToIxia(thinkit::RequestType::kPost,
                            "/ixnetwork/traffic/operations/apply", "payload"))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 200}));
  EXPECT_OK(SendAndWaitForComplete("/ixnetwork/traffic/operations/apply",
                                   "payload", mock_generic_testbed));
}

TEST(IxiaHelper, SendAndWaitForCompleteImmediateSuccess2) {
  thinkit::MockGenericTestbed mock_generic_testbed;
  EXPECT_CALL(
      mock_generic_testbed,
      SendRestRequestToIxia(thinkit::RequestType::kPost,
                            "/ixnetwork/traffic/operations/apply", "payload"))
      .WillOnce(Return(thinkit::HttpResponse{
          .response_code = 202, .response = R"json({"state":"SUCCESS"})json"}));
  EXPECT_OK(SendAndWaitForComplete("/ixnetwork/traffic/operations/apply",
                                   "payload", mock_generic_testbed));
}

TEST(IxiaHelper, SendAndWaitForCompleteOtherError) {
  thinkit::MockGenericTestbed mock_generic_testbed;
  EXPECT_CALL(
      mock_generic_testbed,
      SendRestRequestToIxia(thinkit::RequestType::kPost,
                            "/ixnetwork/traffic/operations/apply", "payload"))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 503}));
  EXPECT_THAT(SendAndWaitForComplete("/ixnetwork/traffic/operations/apply",
                                     "payload", mock_generic_testbed),
              StatusIs(absl::StatusCode::kInternal));
}

TEST(IxiaHelper, SendAndWaitForCompletePollSuccess) {
  thinkit::MockGenericTestbed mock_generic_testbed;
  EXPECT_CALL(
      mock_generic_testbed,
      SendRestRequestToIxia(thinkit::RequestType::kPost,
                            "/ixnetwork/traffic/operations/apply", "payload"))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 202,
                                             .response =
                                                 R"json({"state":"IN_PROGRESS",
              "url":"/ixnetwork/traffic/operations/1"})json"}));
  EXPECT_CALL(mock_generic_testbed,
              SendRestRequestToIxia(thinkit::RequestType::kGet,
                                    "/ixnetwork/traffic/operations/1", ""))
      .WillOnce(Return(thinkit::HttpResponse{
          .response_code = 200,
          .response = R"json({"state":"IN_PROGRESS"})json"}))
      .WillOnce(Return(thinkit::HttpResponse{
          .response_code = 200, .response = R"json({"state":"SUCCESS"})json"}));
  EXPECT_OK(SendAndWaitForComplete("/ixnetwork/traffic/operations/apply",
                                   "payload", mock_generic_testbed));
}

TEST(IxiaHelper, SendAndWaitForCompleteOperationFailed) {
  thinkit::MockGenericTestbed mock_generic_testbed;
  EXPECT_CALL(
      mock_generic_testbed,
      SendRestRequestToIxia(thinkit::RequestType::kPost,
                            "/ixnetwork/traffic/operations/apply", "payload"))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 202,
                                             .response =
                                                 R"json({"state":"EXCEPTION",
              "result":"Failed to start traffic"})json"}));
  EXPECT_THAT(SendAndWaitForComplete("/ixnetwork/traffic/operations/apply",
                                     "payload", mock_generic_testbed),
              StatusIs(absl::StatusCode::kInternal,
                       HasSubstr("Failed to start traffic")));
}

TEST(IxiaHelper, SetFieldSingleValue) {
  thinkit::MockGenericTestbed mock_generic_testbed;
  // Ethernet is the first header, and source MAC is field 1.
  EXPECT_CALL(
      mock_generic_testbed,
      SendRestRequestToIxia(
          thinkit::RequestType::kPatch,
          "/ixnetwork/traffic/trafficItem/1/configElement/1/stack/1/field/1",
          JsonIs(R"json(
{
  "auto": false,
  "valueType": "singleValue",
  "singleValue": "00:00:00:00:00:01"
})json")))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 200}));
  EXPECT_OK(SetFieldSingleValue("/ixnetwork/traffic/trafficItem/1",
                                /*stack_index=*/1, /*field_index=*/1,
                                "00:00:00:00:00:01", mock_generic_testbed));
}

TEST(IxiaHelper, SetFieldSingleValueFails) {
  thinkit::MockGenericTestbed mock_generic_testbed;
  // IP would be the second header, and field 28 is the destination IP,
  EXPECT_CALL(
      mock_generic_testbed,
      SendRestRequestToIxia(
          thinkit::RequestType::kPatch,
          "/ixnetwork/traffic/trafficItem/1/configElement/1/stack/2/field/28",
          JsonIs(R"json(
{
  "auto": false,
  "valueType": "singleValue",
  "singleValue": "10.0.0.1"
})json")))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 400}));
  EXPECT_THAT(SetFieldSingleValue("/ixnetwork/traffic/trafficItem/1",
                                  /*stack_index=*/2, /*field_index=*/28,
                                  "10.0.0.1", mock_generic_testbed),
              StatusIs(absl::StatusCode::kInternal));
}

TEST(IxiaHelper, SetFieldValueList) {
  thinkit::MockGenericTestbed mock_generic_testbed;
  // Ethernet is the first header, and source MAC is field 1.
  EXPECT_CALL(
      mock_generic_testbed,
      SendRestRequestToIxia(
          thinkit::RequestType::kPatch,
          "/ixnetwork/traffic/trafficItem/1/configElement/1/stack/1/field/1",
          JsonIs(R"json(
{
  "auto": false,
  "valueType": "valueList",
  "valueList": [
    "00:00:00:00:00:01",
    "00:00:00:00:00:02"
  ]
})json")))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 200}));
  EXPECT_OK(SetFieldValueList("/ixnetwork/traffic/trafficItem/1",
                              /*stack_index=*/1, /*field_index=*/1,
                              {"00:00:00:00:00:01", "00:00:00:00:00:02"},
                              mock_generic_testbed));
}

TEST(IxiaHelper, SetFieldValueListFails) {
  thinkit::MockGenericTestbed mock_generic_testbed;
  // UDP is likely the third header, and destination port is field 2.
  EXPECT_CALL(
      mock_generic_testbed,
      SendRestRequestToIxia(
          thinkit::RequestType::kPatch,
          "/ixnetwork/traffic/trafficItem/1/configElement/1/stack/3/field/2",
          JsonIs(R"json(
{
  "auto": false,
  "valueType": "valueList",
  "valueList": [
    "100",
    "200"
  ]
})json")))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 400}));
  EXPECT_THAT(SetFieldValueList("/ixnetwork/traffic/trafficItem/1",
                                /*stack_index=*/3, /*field_index=*/2,
                                {"100", "200"}, mock_generic_testbed),
              StatusIs(absl::StatusCode::kInternal));
}

TEST(IxiaHelper, SetFieldRandomRange) {
  thinkit::MockGenericTestbed mock_generic_testbed;
  // UDP is likely the third header, and destination port is field 2.
  EXPECT_CALL(
      mock_generic_testbed,
      SendRestRequestToIxia(
          thinkit::RequestType::kPatch,
          "/ixnetwork/traffic/trafficItem/1/configElement/1/stack/3/field/2",
          JsonIs(R"json(
{
  "auto": false,
  "valueType": "repeatableRandomRange",
  "minValue": "100",
  "maxValue": "1000",
  "stepValue": "10",
  "seed": 123,
  "countValue": 100
})json")))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 200}));
  EXPECT_OK(SetFieldRandomRange("/ixnetwork/traffic/trafficItem/1",
                                /*stack_index=*/3, /*field_index=*/2,
                                /*min_value=*/"100", /*max_value=*/"1000",
                                /*step_value=*/"10", /*seed=*/123,
                                /*count=*/100, mock_generic_testbed));
}

TEST(IxiaHelper, GenerateAndApplyTrafficItems) {
  thinkit::MockGenericTestbed mock_generic_testbed;
  EXPECT_CALL(
      mock_generic_testbed,
      SendRestRequestToIxia(
          thinkit::RequestType::kPost,
          "/ixnetwork/traffic/trafficItem/operations/generate", JsonIs(R"json(
{
  "arg1": [
    "/ixnetwork/traffic/trafficItem/1",
    "/ixnetwork/traffic/trafficItem/2"
  ]
})json")))
      .WillOnce(Return(thinkit::HttpResponse{
          .response_code = 200, .response = R"json({"state":"SUCCESS"})json"}));
  EXPECT_CALL(mock_generic_testbed,
              SendRestRequestToIxia(thinkit::RequestType::kPost,
                                    "/ixnetwork/traffic/operations/apply",
                                    JsonIs(R"json({"arg1": "/traffic"})json")))
      .WillOnce(Return(thinkit::HttpResponse{
          .response_code = 200, .response = R"json({"state":"SUCCESS"})json"}));
  EXPECT_OK(GenerateAndApplyTrafficItems(
      {"/ixnetwork/traffic/trafficItem/1", "/ixnetwork/traffic/trafficItem/2"},
      mock_generic_testbed));
}

TEST(IxiaHelper, SetUpTrafficItemMultipleSrcsAndDsts) {
  thinkit::MockGenericTestbed mock_generic_testbed;
  EXPECT_CALL(mock_generic_testbed,
              SendRestRequestToIxia(
                  thinkit::RequestType::kPost, "/ixnetwork/traffic/trafficItem",
                  JsonIs(R"json([{"name": "Traffic Item 1"}])json")))
      .WillOnce(Return(thinkit::HttpResponse{
          .response_code = 201,
          .response =
              R"json({"links":[{"href":"/api/v1/sessions/1/ixnetwork/traffic/trafficItem/1"}]})json"}));
  EXPECT_CALL(
      mock_generic_testbed,
      SendRestRequestToIxia(
          thinkit::RequestType::kPost,
          "/api/v1/sessions/1/ixnetwork/traffic/trafficItem/1/endpointSet",
          JsonIs(R"json(
[{
  "sources": ["/vport/1/protocols", "/vport/2/protocols"],
  "destinations": ["/vport/3/protocols", "/vport/4/protocols"]
}])json")))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 201}));
  EXPECT_CALL(mock_generic_testbed,
              SendRestRequestToIxia(
                  thinkit::RequestType::kPatch,
                  "/api/v1/sessions/1/ixnetwork/traffic/trafficItem/1/tracking",
                  JsonIs(R"json({"trackBy": ["flowGroup0"]})json")))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 200}));
  EXPECT_OK(SetUpTrafficItemWithMultipleSrcsAndDsts(
      /*sources=*/{"/vport/1", "/vport/2"},
      /*destinations=*/{"/vport/3", "/vport/4"}, "Traffic Item 1",
      mock_generic_testbed, /*is_raw_pkt=*/false));
}

TEST(IxiaHelper, SetUpTrafficItemMultipleSrcsAndDstsRaw) {
  thinkit::MockGenericTestbed mock_generic_testbed;
  EXPECT_CALL(
      mock_generic_testbed,
      SendRestRequestToIxia(
          thinkit::RequestType::kPost, "/ixnetwork/traffic/trafficItem",
          JsonIs(
              R"json([{"name": "Traffic Item 1", "trafficType": "raw"}])json")))
      .WillOnce(Return(thinkit::HttpResponse{
          .response_code = 201,
          .response =
              R"json({"links":[{"href":"/api/v1/sessions/1/ixnetwork/traffic/trafficItem/1"}]})json"}));
  EXPECT_CALL(
      mock_generic_testbed,
      SendRestRequestToIxia(
          thinkit::RequestType::kPost,
          "/api/v1/sessions/1/ixnetwork/traffic/trafficItem/1/endpointSet",
          JsonIs(R"json(
[{
  "sources": ["/vport/1/protocols", "/vport/2/protocols"],
  "destinations": ["/vport/3/protocols", "/vport/4/protocols"]
}])json")))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 201}));
  EXPECT_CALL(mock_generic_testbed,
              SendRestRequestToIxia(
                  thinkit::RequestType::kPatch,
                  "/api/v1/sessions/1/ixnetwork/traffic/trafficItem/1/tracking",
                  JsonIs(R"json({"trackBy": ["flowGroup0"]})json")))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 200}));
  EXPECT_OK(SetUpTrafficItemWithMultipleSrcsAndDsts(
      /*sources=*/{"/vport/1", "/vport/2"},
      /*destinations=*/{"/vport/3", "/vport/4"}, "Traffic Item 1",
      mock_generic_testbed, /*is_raw_pkt=*/true));
}

TEST(IxiaHelper, SetUpTrafficItem) {
  thinkit::MockGenericTestbed mock_generic_testbed;
  EXPECT_CALL(mock_generic_testbed,
              SendRestRequestToIxia(
                  thinkit::RequestType::kPost, "/ixnetwork/traffic/trafficItem",
                  JsonIs(R"json([{"name": "Traffic Item 1"}])json")))
      .WillOnce(Return(thinkit::HttpResponse{
          .response_code = 201,
          .response =
              R"json({"links":[{"href":"/api/v1/sessions/1/ixnetwork/traffic/trafficItem/1"}]})json"}));
  EXPECT_CALL(
      mock_generic_testbed,
      SendRestRequestToIxia(
          thinkit::RequestType::kPost,
          "/api/v1/sessions/1/ixnetwork/traffic/trafficItem/1/endpointSet",
          JsonIs(R"json(
[{
  "sources": ["/vport/1/protocols"],
  "destinations": ["/vport/2/protocols"]
}])json")))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 201}));
  EXPECT_CALL(mock_generic_testbed,
              SendRestRequestToIxia(
                  thinkit::RequestType::kPatch,
                  "/api/v1/sessions/1/ixnetwork/traffic/trafficItem/1/tracking",
                  JsonIs(R"json({"trackBy": ["flowGroup0"]})json")))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 200}));
  EXPECT_OK(SetUpTrafficItem(/*vref_src=*/"/vport/1", /*vref_dst=*/"/vport/2",
                             "Traffic Item 1", mock_generic_testbed));
}

// This matcher is used to check that the payload for the traffic item POST has
// a name that starts with the given prefix.
MATCHER_P(JsonNameStartsWith, prefix, "") {
  absl::StatusOr<nlohmann::json> json = json_yang::ParseJson(arg);
  if (!json.ok()) {
    *result_listener << "Failed to parse JSON: " << arg;
    return false;
  }
  if (!json->is_array()) {
    *result_listener << "JSON is not an array: " << json_yang::DumpJson(*json);
    return false;
  }
  if (json->size() != 1) {
    *result_listener << "JSON is not a single element array: "
                     << json_yang::DumpJson(*json);
    return false;
  }
  return ExplainMatchResult(StartsWith(prefix), (*json)[0]["name"],
                            result_listener);
}

TEST(IxiaHelper, SetUpTrafficItemGeneratedName) {
  thinkit::MockGenericTestbed mock_generic_testbed;
  // Because the name is generated, it appends a random suffix to the name.
  // We can only match the prefix.
  EXPECT_CALL(mock_generic_testbed,
              SendRestRequestToIxia(thinkit::RequestType::kPost,
                                    "/ixnetwork/traffic/trafficItem",
                                    JsonNameStartsWith("/vport/1 -> /vport/2")))
      .WillOnce(Return(thinkit::HttpResponse{
          .response_code = 201,
          .response =
              R"json({"links":[{"href":"/api/v1/sessions/1/ixnetwork/traffic/trafficItem/1"}]})json"}));
  EXPECT_CALL(
      mock_generic_testbed,
      SendRestRequestToIxia(
          thinkit::RequestType::kPost,
          "/api/v1/sessions/1/ixnetwork/traffic/trafficItem/1/endpointSet",
          JsonIs(R"json(
[{
  "sources": ["/vport/1/protocols"],
  "destinations": ["/vport/2/protocols"]
}])json")))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 201}));
  EXPECT_CALL(mock_generic_testbed,
              SendRestRequestToIxia(
                  thinkit::RequestType::kPatch,
                  "/api/v1/sessions/1/ixnetwork/traffic/trafficItem/1/tracking",
                  JsonIs(R"json({"trackBy": ["flowGroup0"]})json")))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 200}));
  EXPECT_OK(SetUpTrafficItem(/*vref_src=*/"/vport/1", /*vref_dst=*/"/vport/2",
                             mock_generic_testbed));
}

TEST(IxiaHelper, StartTrafficItem) {
  thinkit::MockGenericTestbed mock_generic_testbed;
  EXPECT_CALL(
      mock_generic_testbed,
      SendRestRequestToIxia(
          thinkit::RequestType::kPost,
          "/ixnetwork/traffic/trafficItem/operations/"
          "startstatelesstrafficblocking",
          JsonIs(R"json({"arg1": ["/ixnetwork/traffic/trafficItem/1"]})json")))
      .WillOnce(Return(thinkit::HttpResponse{
          .response_code = 200, .response = R"json({"state":"SUCCESS"})json"}));
  EXPECT_OK(StartTrafficItem("/ixnetwork/traffic/trafficItem/1",
                             mock_generic_testbed));
}

}  // namespace
}  // namespace pins_test::ixia
