// Copyright (c) 2024, Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "lib/gnmi/gnmi_helper.h"

#include <string>
#include <tuple>
#include <type_traits>

#include "absl/status/status.h"
#include "absl/strings/escaping.h"
#include "absl/strings/substitute.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "proto/gnmi/gnmi.pb.h"
#include "proto/gnmi/gnmi_mock.grpc.pb.h"

namespace pins_test {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::testing::_;
using ::testing::DoAll;
using ::testing::IsEmpty;
using ::testing::Return;
using ::testing::SetArgPointee;
using ::testing::UnorderedElementsAre;

static constexpr char kAlarmsJson[] = R"([
    {
      "id":"linkqual:linkqual",
      "state":{
        "id":"linkqual:linkqual_1611693908000999999",
        "resource":"linkqual:linkqual",
        "severity":"openconfig-alarm-types:WARNING",
        "text":"INACTIVE: Unknown",
        "time-created":"1611693908000999999",
        "type-id":"Software Error"
      }
    },
    {
      "id":"p4rt:p4rt",
      "state":{
        "id":"p4rt:p4rt_1611693908000000000",
        "resource":"p4rt:p4rt",
        "severity":"openconfig-alarm-types:CRITICAL",
        "text":"INACTIVE: SAI error in route programming",
        "time-created":"1611693908000000000",
        "type-id":"Software Error"
      }
    },
    {
      "id":"swss:orchagent",
      "state":{
        "id":"swss:orchagent_1611693908000007777",
        "resource":"swss:orchagent",
        "text":"INITIALIZING: ",
        "time-created":"1611693908000007777",
        "type-id":"Software Error"
      }
    },
    {
      "id":"telemetry:telemetry",
      "state":{
        "id":"telemetry:telemetry_1611693908000044444",
        "resource":"telemetry:telemetry",
        "severity":"openconfig-alarm-types:CRITICAL",
        "text":"ERROR: Go Panic",
        "time-created":"1611693908000044444",
        "type-id":"Software Error"
      }
    }
  ])";

TEST(OCStringToPath, OCStringToPathTestCase1) {
  EXPECT_THAT(
      ConvertOCStringToPath("interfaces/interface[name=ethernet0]/config/mtu"),
      EqualsProto(R"pb(
        elem { name: "interfaces" }
        elem {
          name: "interface"
          key { key: "name" value: "ethernet0" }
        }
        elem { name: "config" }
        elem { name: "mtu" }
      )pb"));
}

TEST(OCStringToPath, OCStringToPathTestCase2) {
  EXPECT_THAT(
      ConvertOCStringToPath("components/component[name=1/1]/state/name"),
      EqualsProto(R"pb(
        elem { name: "components" }
        elem {
          name: "component"
          key { key: "name" value: "1/1" }
        }
        elem { name: "state" }
        elem { name: "name" }
      )pb"));
}

TEST(OCStringToPath, OCStringToPathTestCase3) {
  EXPECT_THAT(
      ConvertOCStringToPath(
          "interfaces/interface[name=ethernet0]/config/mtu/ic[name=1/1]/value"),
      EqualsProto(R"pb(
        elem { name: "interfaces" }
        elem {
          name: "interface"
          key { key: "name" value: "ethernet0" }
        }
        elem { name: "config" }
        elem { name: "mtu" }
        elem {
          name: "ic"
          key { key: "name" value: "1/1" }
        }
        elem { name: "value" }
      )pb"));
}

TEST(ParseAlarms, NoAlarms) {
  EXPECT_THAT(ParseAlarms("[]"), IsOkAndHolds(IsEmpty()));
}

TEST(ParseAlarms, SomeAlarms) {
  EXPECT_THAT(
      ParseAlarms(kAlarmsJson),
      IsOkAndHolds(UnorderedElementsAre(
          "[linkqual:linkqual WARNING] Software Error INACTIVE: Unknown",
          "[p4rt:p4rt CRITICAL] Software Error INACTIVE: SAI error in route "
          "programming",
          "[swss:orchagent ] Software Error INITIALIZING: ",
          "[telemetry:telemetry CRITICAL] Software Error ERROR: Go Panic")));
}

TEST(ParseAlarms, InvalidInput) {
  // ParseAlarms expects an array of alarms.
  EXPECT_THAT(ParseAlarms(R"({"something":[]})"),
              StatusIs(absl::StatusCode::kInvalidArgument));

  // ParseAlarms expects the alarms to have a state field.
  EXPECT_THAT(ParseAlarms(R"([{"id":"a"}])"),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(GetAlarms, FailedRPCReturnsError) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get(_,
                        EqualsProto(gutil::ParseProtoOrDie<gnmi::GetRequest>(
                            R"pb(prefix { origin: "openconfig" }
                                 path {
                                   elem { name: "system" }
                                   elem { name: "alarms" }
                                 }
                                 type: STATE)pb")),
                        _))
      .WillOnce(Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  EXPECT_THAT(GetAlarms(stub), StatusIs(absl::StatusCode::kDeadlineExceeded));
}

TEST(GetAlarms, InvalidResponsesFail) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get(_,
                        EqualsProto(gutil::ParseProtoOrDie<gnmi::GetRequest>(
                            R"pb(prefix { origin: "openconfig" }
                                 path {
                                   elem { name: "system" }
                                   elem { name: "alarms" }
                                 }
                                 type: STATE)pb")),
                        _))
      // More than one notification.
      .WillOnce(
          DoAll(SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
                    R"pb(notification {
                           timestamp: 1619721040593669829
                           prefix { origin: "openconfig" }
                           update {
                             path {
                               elem { name: "system" }
                               elem { name: "alarms" }
                             }
                             val { json_ietf_val: "{}" }
                           }
                         }
                         notification {})pb")),
                Return(grpc::Status::OK)))
      // More than one update.
      .WillOnce(
          DoAll(SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
                    R"pb(notification {
                           timestamp: 1619721040593669829
                           prefix { origin: "openconfig" }
                           update {
                             path {
                               elem { name: "system" }
                               elem { name: "alarms" }
                             }
                             val { json_ietf_val: "{}" }
                           }
                           update {}
                         })pb")),
                Return(grpc::Status::OK)));
  EXPECT_THAT(GetAlarms(stub), StatusIs(absl::StatusCode::kInternal));
  EXPECT_THAT(GetAlarms(stub), StatusIs(absl::StatusCode::kInternal));
}

TEST(GetAlarms, EmptySubtreeReturnsNoAlarms) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get(_,
                        EqualsProto(gutil::ParseProtoOrDie<gnmi::GetRequest>(
                            R"pb(prefix { origin: "openconfig" }
                                 path {
                                   elem { name: "system" }
                                   elem { name: "alarms" }
                                 }
                                 type: STATE)pb")),
                        _))
      .WillOnce(
          DoAll(SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
                    R"pb(notification {
                           timestamp: 1619721040593669829
                           prefix { origin: "openconfig" }
                           update {
                             path {
                               elem { name: "system" }
                               elem { name: "alarms" }
                             }
                             val { json_ietf_val: "{}" }
                           }
                         })pb")),
                Return(grpc::Status::OK)));
  EXPECT_THAT(GetAlarms(stub), IsOkAndHolds(IsEmpty()));
}

TEST(GetAlarms, SemiEmptySubtreeReturnsNoAlarms) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get(_,
                        EqualsProto(gutil::ParseProtoOrDie<gnmi::GetRequest>(
                            R"pb(prefix { origin: "openconfig" }
                                 path {
                                   elem { name: "system" }
                                   elem { name: "alarms" }
                                 }
                                 type: STATE)pb")),
                        _))
      .WillOnce(DoAll(
          SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
              R"pb(notification {
                     timestamp: 1619721040593669829
                     prefix { origin: "openconfig" }
                     update {
                       path {
                         elem { name: "system" }
                         elem { name: "alarms" }
                       }
                       val {
                         json_ietf_val: "{\"openconfig-system:alarms\":{}}"
                       }
                     }
                   })pb")),
          Return(grpc::Status::OK)));
  EXPECT_THAT(GetAlarms(stub), IsOkAndHolds(IsEmpty()));
}

TEST(GetAlarms, EmptyArrayReturnsNoAlarms) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get(_,
                        EqualsProto(gutil::ParseProtoOrDie<gnmi::GetRequest>(
                            R"pb(prefix { origin: "openconfig" }
                                 path {
                                   elem { name: "system" }
                                   elem { name: "alarms" }
                                 }
                                 type: STATE)pb")),
                        _))
      .WillOnce(DoAll(
          SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
              R"pb(notification {
                     timestamp: 1619721040593669829
                     prefix { origin: "openconfig" }
                     update {
                       path {
                         elem { name: "system" }
                         elem { name: "alarms" }
                       }
                       val {
                         json_ietf_val: "{\"openconfig-system:alarms\":{\"alarm\":[]}}"
                       }
                     }
                   })pb")),
          Return(grpc::Status::OK)));
  EXPECT_THAT(GetAlarms(stub), IsOkAndHolds(IsEmpty()));
}

TEST(GetAlarms, NormalInput) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get(_,
                        EqualsProto(gutil::ParseProtoOrDie<gnmi::GetRequest>(
                            R"pb(prefix { origin: "openconfig" }
                                 path {
                                   elem { name: "system" }
                                   elem { name: "alarms" }
                                 }
                                 type: STATE)pb")),
                        _))
      .WillOnce(DoAll(
          SetArgPointee<
              2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(absl::Substitute(
              R"pb(notification {
                     timestamp: 1619721040593669829
                     prefix { origin: "openconfig" }
                     update {
                       path {
                         elem { name: "system" }
                         elem { name: "alarms" }
                       }
                       val {
                         json_ietf_val: "{\"openconfig-system:alarms\":{\"alarm\":$0}}"
                       }
                     }
                   })pb",
              absl::CEscape(kAlarmsJson)))),
          Return(grpc::Status::OK)));
  EXPECT_THAT(
      GetAlarms(stub),
      IsOkAndHolds(UnorderedElementsAre(
          "[linkqual:linkqual WARNING] Software Error INACTIVE: Unknown",
          "[p4rt:p4rt CRITICAL] Software Error INACTIVE: SAI error in route "
          "programming",
          "[swss:orchagent ] Software Error INITIALIZING: ",
          "[telemetry:telemetry CRITICAL] Software Error ERROR: Go Panic")));
}

TEST(StripQuotes, VariousInputs) {
  EXPECT_EQ(StripQuotes(R"("test")"), R"(test)");
  EXPECT_EQ(StripQuotes(R"("test)"), R"(test)");
  EXPECT_EQ(StripQuotes(R"(test)"), R"(test)");
  EXPECT_EQ(StripQuotes(R"("test"")"), R"(test")");
}

}  // namespace
}  // namespace pins_test
