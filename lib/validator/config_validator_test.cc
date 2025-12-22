#include "lib/validator/config_validator.h"

#include <memory>
#include <string>
#include <utility>

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "grpcpp/support/status.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "include/nlohmann/json.hpp"
#include "proto/gnmi/gnmi_mock.grpc.pb.h"
#include "thinkit/mock_switch.h"
#include "thinkit/mock_test_environment.h"

namespace pins_test {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::gutil::ParseProtoOrDie;
using ::gutil::StatusIs;
using ::testing::_;
using ::testing::ByMove;
using ::testing::DoAll;
using ::testing::HasSubstr;
using ::testing::Pair;
using ::testing::Return;
using ::testing::ReturnRefOfCopy;
using ::testing::SetArgPointee;
using ::testing::UnorderedElementsAre;

TEST(ConfigValidator, FlattenOpenconfigJsonToMap) {
  EXPECT_THAT(FlattenOpenconfigJsonToMap(nlohmann::json::parse(R"json(
    {
      "outer": {
        "list": [
          {
            "key": "value1",
            "config": {
              "height": 100
            }
          },
          {
            "key": "value2",
            "config": {
              "height": 200
            }
          }
        ]
      }
    })json")),
              IsOkAndHolds(UnorderedElementsAre(
                  Pair("/outer/list[key='value1']/config/height", "100"),
                  Pair("/outer/list[key='value2']/config/height", "200"),
                  Pair("/outer/list[key='value1']/key", "value1"),
                  Pair("/outer/list[key='value2']/key", "value2"))));
}

TEST(ConfigValidator, FlattenOpenconfigJsonToMapOrderDoesntMatter) {
  EXPECT_THAT(
      FlattenOpenconfigJsonToMap(nlohmann::json::parse(R"json(
    {
      "outer": {
        "list": [
          {
            "key": "value1",
            "key2": "other_value1",
            "config": {
              "height": 100
            }
          },
          {
            "key2": "other_value2",
            "key": "value2",
            "config": {
              "height": 200
            }
          }
        ]
      }
    })json")),
      IsOkAndHolds(UnorderedElementsAre(
          Pair("/outer/list[key='value1'][key2='other_value1']/config/height",
               "100"),
          Pair("/outer/list[key='value2'][key2='other_value2']/config/height",
               "200"),
          Pair("/outer/list[key='value1'][key2='other_value1']/key", "value1"),
          Pair("/outer/list[key='value2'][key2='other_value2']/key", "value2"),
          Pair("/outer/list[key='value1'][key2='other_value1']/key2",
               "other_value1"),
          Pair("/outer/list[key='value2'][key2='other_value2']/key2",
               "other_value2"))));
}

class ConfigValidatorTest : public ::testing::Test {
 protected:
  void SetUp() override {
    auto mock_gnmi_stub = std::make_unique<gnmi::MockgNMIStub>();
    mock_gnmi_stub_ = mock_gnmi_stub.get();
    ON_CALL(mock_switch_, ChassisName())
        .WillByDefault(ReturnRefOfCopy(std::string("chassis")));
    EXPECT_CALL(mock_switch_, CreateGnmiStub())
        .WillOnce(Return(ByMove(std::move(mock_gnmi_stub))));
  }

  thinkit::MockSwitch mock_switch_;
  gnmi::MockgNMIStub* mock_gnmi_stub_;
};

constexpr absl::string_view kStateGetRequest = R"pb(
  prefix { origin: "openconfig" target: "chassis" }
  path { elem { name: "sampling" } }
  type: STATE
  encoding: JSON_IETF
)pb";

constexpr absl::string_view kSamplingConfig = R"json(
  {
    "openconfig-sampling:sampling": {
      "sflow": {
        "config": {
          "enabled":false
        }
      }
    }
  })json";

TEST_F(ConfigValidatorTest, ConfigConvergedParseConfigFailure) {
  EXPECT_THAT(ConfigConverged(mock_switch_, "{]"),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_F(ConfigValidatorTest, TestVerifyConfigPushGnmiGetStateError) {
  auto state_req = ParseProtoOrDie<gnmi::GetRequest>(kStateGetRequest);
  gnmi::GetResponse state_resp;
  EXPECT_CALL(*mock_gnmi_stub_, Get(_, EqualsProto(state_req), _))
      .WillOnce(Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  EXPECT_THAT(ConfigConverged(mock_switch_, kSamplingConfig),
              StatusIs(absl::StatusCode::kDeadlineExceeded));
}

TEST_F(ConfigValidatorTest, TestVerifyConfigPushEmptyGnmiStateResponse) {
  auto state_req = ParseProtoOrDie<gnmi::GetRequest>(kStateGetRequest);
  gnmi::GetResponse state_resp;
  EXPECT_CALL(*mock_gnmi_stub_, Get(_, EqualsProto(state_req), _))
      .WillOnce(DoAll(SetArgPointee<2>(state_resp), Return(grpc::Status::OK)));
  EXPECT_THAT(ConfigConverged(mock_switch_, kSamplingConfig),
              StatusIs(absl::StatusCode::kInternal));
}

TEST_F(ConfigValidatorTest, TestVerifyConfigPushParseStateFailure) {
  auto state_req = ParseProtoOrDie<gnmi::GetRequest>(kStateGetRequest);
  auto state_resp = ParseProtoOrDie<gnmi::GetResponse>(
      R"pb(notification {
             timestamp: 1619721040593669829
             prefix { origin: "openconfig" target: "chassis" }
             update {
               path { elem { name: "sampling" } }
               val { json_ietf_val: "{}" }
             }
           })pb");
  EXPECT_CALL(*mock_gnmi_stub_, Get(_, EqualsProto(state_req), _))
      .WillOnce(DoAll(SetArgPointee<2>(state_resp), Return(grpc::Status::OK)));
  EXPECT_THAT(ConfigConverged(mock_switch_, kSamplingConfig),
              StatusIs(absl::StatusCode::kInternal));
}

TEST_F(ConfigValidatorTest, TestVerifyConfigPushConfigMismatchFailure) {
  auto state_req = ParseProtoOrDie<gnmi::GetRequest>(kStateGetRequest);
  auto state_resp = ParseProtoOrDie<gnmi::GetResponse>(
      R"pb(notification {
             timestamp: 1619721040593669829
             prefix { origin: "openconfig" target: "chassis" }
             update {
               path { elem { name: "sampling" } }
               val {
                 json_ietf_val: "{\"openconfig-sampling:sampling\":{\"sflow\":{\"state\":{\"enabled\":true}}}}"
               }
             }
           })pb");
  EXPECT_CALL(*mock_gnmi_stub_, Get(_, EqualsProto(state_req), _))
      .WillOnce(DoAll(SetArgPointee<2>(state_resp), Return(grpc::Status::OK)));
  EXPECT_THAT(ConfigConverged(mock_switch_, kSamplingConfig),
              StatusIs(absl::StatusCode::kInternal,
                       HasSubstr("Config verification failed for: ")));
}

TEST_F(ConfigValidatorTest, TestVerifyConfigPushConfigSkipped) {
  // Since the only path is skipped, no gNMI calls are made.
  EXPECT_OK(ConfigConverged(mock_switch_, kSamplingConfig,
                            /*paths_to_skip=*/{"sampling"}));
}

TEST_F(ConfigValidatorTest, TestVerifyConfigPushConfigMismatchDumpsArtifacts) {
  auto state_req = ParseProtoOrDie<gnmi::GetRequest>(kStateGetRequest);
  auto state_resp = ParseProtoOrDie<gnmi::GetResponse>(
      R"pb(notification {
             timestamp: 1619721040593669829
             prefix { origin: "openconfig" target: "chassis" }
             update {
               path { elem { name: "sampling" } }
               val {
                 json_ietf_val: "{\"openconfig-sampling:sampling\":{\"sflow\":{\"state\":{\"enabled\":true}}}}"
               }
             }
           })pb");
  EXPECT_CALL(*mock_gnmi_stub_, Get(_, EqualsProto(state_req), _))
      .WillOnce(DoAll(SetArgPointee<2>(state_resp), Return(grpc::Status::OK)));

  // When there is a mismatch and a test environment is provided, artifacts are
  // dumped.
  thinkit::MockTestEnvironment test_environment;
  EXPECT_CALL(test_environment, StoreTestArtifact(_, _))
      .WillRepeatedly(Return(absl::OkStatus()));
  EXPECT_THAT(ConfigConverged(mock_switch_, kSamplingConfig,
                              /*paths_to_skip=*/{}, &test_environment),
              StatusIs(absl::StatusCode::kInternal,
                       HasSubstr("Config verification failed for: ")));
}

TEST_F(ConfigValidatorTest, TestVerifyConfigPushOk) {
  auto state_req = ParseProtoOrDie<gnmi::GetRequest>(kStateGetRequest);
  auto state_resp = ParseProtoOrDie<gnmi::GetResponse>(
      R"pb(notification {
             timestamp: 1619721040593669829
             prefix { origin: "openconfig" target: "chassis" }
             update {
               path { elem { name: "sampling" } }
               val {
                 json_ietf_val: "{\"openconfig-sampling:sampling\":{\"sflow\":{\"state\":{\"enabled\":false}}}}"
               }
             }
           })pb");
  EXPECT_CALL(*mock_gnmi_stub_, Get(_, EqualsProto(state_req), _))
      .WillOnce(DoAll(SetArgPointee<2>(state_resp), Return(grpc::Status::OK)));
  EXPECT_OK(ConfigConverged(mock_switch_, kSamplingConfig));
}

}  // namespace
}  // namespace pins_test

