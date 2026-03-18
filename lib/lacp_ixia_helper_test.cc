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
#include "lib/lacp_ixia_helper.h"

#include <string>
#include <string_view>
#include <vector>

#include "absl/strings/str_cat.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "lib/ixia_helper.h"
#include "lib/utils/json_test_utils.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/mock_generic_testbed.h"

namespace pins_test::ixia {
namespace {

using ::gutil::IsOkAndHolds;
using ::pins_test::JsonIs;
using ::testing::_;
using ::testing::InSequence;
using ::testing::Return;
using ::testing::StartsWith;

TEST(LacpIxiahHelperTest, CreateLacpTrafficItem) {
  thinkit::MockGenericTestbed testbed;
  // Check that the traffic item is created.
  EXPECT_CALL(testbed,
              SendRestRequestToIxia(thinkit::RequestType::kPost,
                                    "/ixnetwork/traffic/trafficItem", _))
      .WillOnce(Return(thinkit::HttpResponse{
          .response_code = 201,
          .response =
              R"json({"links": [{"href": "/api/v1/sessions/1/ixnetwork/traffic/trafficItem/1"}]})json"}));
  EXPECT_CALL(
      testbed,
      SendRestRequestToIxia(
          thinkit::RequestType::kPost,
          "/api/v1/sessions/1/ixnetwork/traffic/trafficItem/1/endpointSet",
          JsonIs(R"json([{"sources": ["vport/protocols"]}])json")))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 201}));

  // Check that the item options are configured.
  LacpTrafficItemOptions options{.packets_per_second = 0.1f, .packet_count = 3};
  EXPECT_CALL(
      testbed,
      SendRestRequestToIxia(
          thinkit::RequestType::kPatch,
          "/api/v1/sessions/1/ixnetwork/traffic/trafficItem/1/"
          "configElement/1/transmissionControl",
          JsonIs(R"json({"type": "fixedFrameCount", "frameCount": "3"})json")))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 200}));
  EXPECT_CALL(
      testbed,
      SendRestRequestToIxia(
          thinkit::RequestType::kPatch,
          "/api/v1/sessions/1/ixnetwork/traffic/trafficItem/1/"
          "configElement/1/frameRate",
          JsonIs(R"json({"type": "framesPerSecond", "rate": 0.1})json")))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 200}));

  // Check that the MAC addresses are set.
  LacpInfo lacp_info{.source_mac = "00:00:00:00:00:01"};
  // Field 1 is the destination MAC address which is fixed for LACP.
  EXPECT_CALL(testbed,
              SendRestRequestToIxia(
                  thinkit::RequestType::kPatch,
                  "/api/v1/sessions/1/ixnetwork/traffic/trafficItem/1/"
                  "configElement/1/stack/1/field/1",
                  JsonIs(R"json({"singleValue": "01:80:c2:00:00:02"})json")))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 200}));
  // Field 2 is the source MAC address.
  EXPECT_CALL(testbed,
              SendRestRequestToIxia(
                  thinkit::RequestType::kPatch,
                  "/api/v1/sessions/1/ixnetwork/traffic/trafficItem/1/"
                  "configElement/1/stack/1/field/2",
                  JsonIs(R"json({"singleValue": "00:00:00:00:00:01"})json")))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 200}));

  // For the new headers LACP and Ethernet II without FCS, the returned protocol
  // templates will have their IDs.
  EXPECT_CALL(testbed,
              SendRestRequestToIxia(
                  thinkit::RequestType::kGet,
                  StartsWith("/ixnetwork/traffic/protocolTemplate"), _))
      .WillRepeatedly(Return(
          thinkit::HttpResponse{.response_code = 200, .response = R"json([
          {"displayName":"LACP", 
           "links":[{"href":"/api/v1/sessions/1/ixnetwork/traffic/protocolTemplate/1/field"}]},
          {"displayName":"Ethernet II without FCS", 
           "links":[{"href":"/api/v1/sessions/1/ixnetwork/traffic/protocolTemplate/2/field"}]},
          ])json"}));

  // Expect that the default Ethernet protocol is removed and the Ethernet
  // without FCS is added. Because we can't leave the stack empty, the order is
  // import (add then remove).
  {
    InSequence add_then_remove;
    EXPECT_CALL(testbed,
                SendRestRequestToIxia(
                    thinkit::RequestType::kPost,
                    "/ixnetwork/traffic/trafficItem/configElement/stack/"
                    "operations/appendprotocol",
                    JsonIs(R"json({
      "arg1": "/api/v1/sessions/1/ixnetwork/traffic/trafficItem/1/configElement/1/stack/1",
      "arg2": "/api/v1/sessions/1/ixnetwork/traffic/protocolTemplate/2"
                           })json")))
        .WillOnce(Return(thinkit::HttpResponse{.response_code = 200}));
    EXPECT_CALL(testbed,
                SendRestRequestToIxia(
                    thinkit::RequestType::kPost,
                    "/ixnetwork/traffic/trafficItem/configElement/stack/"
                    "operations/remove",
                    JsonIs(R"json({
      "arg1": "/api/v1/sessions/1/ixnetwork/traffic/trafficItem/1/configElement/1/stack/1"
                           })json")))
        .WillOnce(Return(thinkit::HttpResponse{.response_code = 200}));
  }

  // Expect the LACP protocol to be added.
  EXPECT_CALL(testbed, SendRestRequestToIxia(
                           thinkit::RequestType::kPost,
                           "/ixnetwork/traffic/trafficItem/configElement/stack/"
                           "operations/appendprotocol",
                           JsonIs(R"json({
      "arg1": "/api/v1/sessions/1/ixnetwork/traffic/trafficItem/1/configElement/1/stack/1",
      "arg2": "/api/v1/sessions/1/ixnetwork/traffic/protocolTemplate/1"
                           })json")))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 200}));

  // Expect actor information to be set.
  AgentInfo actor_info = {
      .system_priority = "0x100",
      .system_id = "0x021a71b4050a",
      .key = "0xff",
      .port_priority = "0xff",
      .port_id = "0x2",
      .state =
          std::vector<std::string>{
              ToHex(ixia::LacpState::kAggregation | ixia::LacpState::kExpired),
              ToHex(ixia::LacpState::kActivity | ixia::LacpState::kAggregation |
                    ixia::LacpState::kExpired)},
  };
  lacp_info.actor = actor_info;
  // The LACP header is the second in the stack, hence stack/2.
  EXPECT_CALL(
      testbed,
      SendRestRequestToIxia(
          thinkit::RequestType::kPatch,
          absl::StrCat("/api/v1/sessions/1/ixnetwork/traffic/"
                       "trafficItem/1/configElement/1/stack/2/field/",
                       LacpField::kActorSystemPriority),
          JsonIs(
              R"json({"auto": false, "valueType": "singleValue", "singleValue": "0x100"})json")))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 200}));
  EXPECT_CALL(
      testbed,
      SendRestRequestToIxia(
          thinkit::RequestType::kPatch,
          absl::StrCat("/api/v1/sessions/1/ixnetwork/traffic/"
                       "trafficItem/1/configElement/1/stack/2/field/",
                       LacpField::kActorSystemId),
          JsonIs(
              R"json({"auto": false, "valueType": "singleValue", "singleValue": "0x021a71b4050a"})json")))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 200}));
  EXPECT_CALL(
      testbed,
      SendRestRequestToIxia(
          thinkit::RequestType::kPatch,
          absl::StrCat("/api/v1/sessions/1/ixnetwork/traffic/"
                       "trafficItem/1/configElement/1/stack/2/field/",
                       LacpField::kActorKey),
          JsonIs(
              R"json({"auto": false, "valueType": "singleValue", "singleValue": "0xff"})json")))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 200}));
  EXPECT_CALL(
      testbed,
      SendRestRequestToIxia(
          thinkit::RequestType::kPatch,
          absl::StrCat("/api/v1/sessions/1/ixnetwork/traffic/"
                       "trafficItem/1/configElement/1/stack/2/field/",
                       LacpField::kActorPortPriority),
          JsonIs(
              R"json({"auto": false, "valueType": "singleValue", "singleValue": "0xff"})json")))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 200}));
  EXPECT_CALL(
      testbed,
      SendRestRequestToIxia(
          thinkit::RequestType::kPatch,
          absl::StrCat("/api/v1/sessions/1/ixnetwork/traffic/"
                       "trafficItem/1/configElement/1/stack/2/field/",
                       LacpField::kActorPortId),
          JsonIs(
              R"json({"auto": false, "valueType": "singleValue", "singleValue": "0x2"})json")))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 200}));
  EXPECT_CALL(
      testbed,
      SendRestRequestToIxia(
          thinkit::RequestType::kPatch,
          absl::StrCat("/api/v1/sessions/1/ixnetwork/traffic/"
                       "trafficItem/1/configElement/1/stack/2/field/",
                       LacpField::kActorState),
          JsonIs(
              R"json({"auto": false, "valueType": "valueList", "valueList": ["84", "85"]})json")))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 200}));

  // Expect partner information to be set.
  AgentInfo partner_info = {
      .system_priority = "0x100",
      .system_id = std::vector<std::string>{"0x0", "0x021a71b4050a"},
      .key = "0xff",
      .port_priority = "0xff",
      .port_id = "0x2",
      .state = ixia::ToHex(ixia::LacpState::kTimeout),
  };
  lacp_info.partner = partner_info;
  EXPECT_CALL(
      testbed,
      SendRestRequestToIxia(
          thinkit::RequestType::kPatch,
          absl::StrCat("/api/v1/sessions/1/ixnetwork/traffic/"
                       "trafficItem/1/configElement/1/stack/2/field/",
                       LacpField::kPartnerSystemPriority),
          JsonIs(
              R"json({"auto": false, "valueType": "singleValue", "singleValue": "0x100"})json")))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 200}));
  EXPECT_CALL(
      testbed,
      SendRestRequestToIxia(
          thinkit::RequestType::kPatch,
          absl::StrCat("/api/v1/sessions/1/ixnetwork/traffic/"
                       "trafficItem/1/configElement/1/stack/2/field/",
                       LacpField::kPartnerSystemId),
          JsonIs(
              R"json({"auto": false, "valueType": "valueList", "valueList": ["0x0", "0x021a71b4050a"]})json")))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 200}));
  EXPECT_CALL(
      testbed,
      SendRestRequestToIxia(
          thinkit::RequestType::kPatch,
          absl::StrCat("/api/v1/sessions/1/ixnetwork/traffic/"
                       "trafficItem/1/configElement/1/stack/2/field/",
                       LacpField::kPartnerKey),
          JsonIs(
              R"json({"auto": false, "valueType": "singleValue", "singleValue": "0xff"})json")))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 200}));
  EXPECT_CALL(
      testbed,
      SendRestRequestToIxia(
          thinkit::RequestType::kPatch,
          absl::StrCat("/api/v1/sessions/1/ixnetwork/traffic/"
                       "trafficItem/1/configElement/1/stack/2/field/",
                       LacpField::kPartnerPortPriority),
          JsonIs(
              R"json({"auto": false, "valueType": "singleValue", "singleValue": "0xff"})json")))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 200}));
  EXPECT_CALL(
      testbed,
      SendRestRequestToIxia(
          thinkit::RequestType::kPatch,
          absl::StrCat("/api/v1/sessions/1/ixnetwork/traffic/"
                       "trafficItem/1/configElement/1/stack/2/field/",
                       LacpField::kPartnerPortId),
          JsonIs(
              R"json({"auto": false, "valueType": "singleValue", "singleValue": "0x2"})json")))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 200}));
  EXPECT_CALL(
      testbed,
      SendRestRequestToIxia(
          thinkit::RequestType::kPatch,
          absl::StrCat("/api/v1/sessions/1/ixnetwork/traffic/"
                       "trafficItem/1/configElement/1/stack/2/field/",
                       LacpField::kPartnerState),
          JsonIs(
              R"json({"auto": false, "valueType": "singleValue", "singleValue": "2"})json")))
      .WillOnce(Return(thinkit::HttpResponse{.response_code = 200}));

  EXPECT_THAT(
      CreateLacpTrafficItem("vport", lacp_info, options, testbed),
      IsOkAndHolds("/api/v1/sessions/1/ixnetwork/traffic/trafficItem/1"));
}

}  // namespace
}  // namespace pins_test::ixia
