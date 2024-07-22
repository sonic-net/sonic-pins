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

TEST(GetInterfaceOperStatusMap, GnmiGetRpcFails) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).WillOnce(
      Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  EXPECT_THAT(GetInterfaceToOperStatusMapOverGnmi(stub, absl::Seconds(60)),
              StatusIs(absl::StatusCode::kDeadlineExceeded));
}

TEST(GetInterfaceOperStatusMap, InvalidGnmiGetResponse) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).WillOnce(Return(grpc::Status::OK));
  EXPECT_THAT(GetInterfaceToOperStatusMapOverGnmi(stub, absl::Seconds(60)),
              StatusIs(absl::StatusCode::kInternal,
                       testing::HasSubstr("Invalid response")));
}

TEST(GetInterfaceOperStatusMap, GnmiGetResponseWithoutOpenconfigInterface) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).WillOnce(DoAll(
      SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
          R"pb(notification {
                 timestamp: 1620348032128305716
                 prefix { origin: "openconfig" }
                 update {
                   path { elem { name: "interfaces" } }
                   val { json_ietf_val: "{\"openconfig-system:alarms\":{}}" }
                 }
               })pb")),
      Return(grpc::Status::OK)));

  EXPECT_THAT(GetInterfaceToOperStatusMapOverGnmi(stub, absl::Seconds(60)),
              StatusIs(absl::StatusCode::kNotFound,
                       testing::HasSubstr(
                           "'openconfig-interfaces:interfaces' not found")));
}

TEST(GetInterfaceOperStatusMap, InterfaceNotFoundInGnmiGetResponse) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).WillOnce(DoAll(
      SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
          R"pb(notification {
                 timestamp: 1620348032128305716
                 prefix { origin: "openconfig" }
                 update {
                   path { elem { name: "interfaces" } }
                   val {
                     json_ietf_val: "{\"openconfig-interfaces:interfaces\":{}}"
                   }
                 }
               })pb")),
      Return(grpc::Status::OK)));

  EXPECT_THAT(GetInterfaceToOperStatusMapOverGnmi(stub, absl::Seconds(60)),
              StatusIs(absl::StatusCode::kNotFound,
                       testing::HasSubstr("'interface' not found")));
}

TEST(GetInterfaceOperStatusMap, InterfaceNameNotFound) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).WillOnce(DoAll(
      SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
          R"pb(notification {
                 timestamp: 1620348032128305716
                 prefix { origin: "openconfig" }
                 update {
                   path { elem { name: "interfaces" } }
                   val {
                     json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{}]}}"
                   }
                 }
               })pb")),
      Return(grpc::Status::OK)));

  EXPECT_THAT(GetInterfaceToOperStatusMapOverGnmi(stub, absl::Seconds(60)),
              StatusIs(absl::StatusCode::kNotFound,
                       testing::HasSubstr("'name' not found")));
}

TEST(GetInterfaceOperStatusMap, InterfaceStateNotFound) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).WillOnce(DoAll(
      SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
          R"pb(notification {
                 timestamp: 1620348032128305716
                 prefix { origin: "openconfig" }
                 update {
                   path { elem { name: "interfaces" } }
                   val {
                     json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet0\"}]}}"
                   }
                 }
               })pb")),
      Return(grpc::Status::OK)));

  EXPECT_THAT(GetInterfaceToOperStatusMapOverGnmi(stub, absl::Seconds(60)),
              StatusIs(absl::StatusCode::kNotFound,
                       testing::HasSubstr("'state' not found")));
}

TEST(GetInterfaceOperStatusMap, OperStatusNotFoundInState) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).WillOnce(DoAll(
      SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
          R"pb(notification {
                 timestamp: 1620348032128305716
                 prefix { origin: "openconfig" }
                 update {
                   path { elem { name: "interfaces" } }
                   val {
                     json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet0\",\"state\":{\"name\":\"Ethernet0\"}}]}}"
                   }
                 }
               })pb")),
      Return(grpc::Status::OK)));

  EXPECT_THAT(GetInterfaceToOperStatusMapOverGnmi(stub, absl::Seconds(60)),
              StatusIs(absl::StatusCode::kNotFound,
                       testing::HasSubstr("'oper-status' not found")));
}

TEST(GetInterfaceOperStatusMap, SuccessfullyReturnsInterfaceOperStatusMap) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).WillOnce(DoAll(
      SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
          R"pb(notification {
                 timestamp: 1620348032128305716
                 prefix { origin: "openconfig" }
                 update {
                   path { elem { name: "interfaces" } }
                   val {
                     json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Cpu0\"},{\"name\":\"Ethernet0\",\"state\":{\"oper-status\":\"DOWN\"}}]}}"
                   }
                 }
               })pb")),
      Return(grpc::Status::OK)));

  auto statusor = GetInterfaceToOperStatusMapOverGnmi(stub, absl::Seconds(60));
  ASSERT_OK(statusor);
  const absl::flat_hash_map<std::string, std::string> expected_map = {
      {"Ethernet0", "DOWN"}};
  EXPECT_THAT(*statusor,
              ::testing::UnorderedPointwise(::testing::Eq(), expected_map));
}

TEST(CheckAllInterfaceOperState, FailsToGetInterfaceOperStatusMap) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).WillOnce(
      Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  EXPECT_THAT(
      CheckAllInterfaceOperStateOverGnmi(stub, /*interface_oper_state=*/"UP"),
      StatusIs(absl::StatusCode::kDeadlineExceeded));
}

TEST(CheckAllInterfaceOperState, InterfaceNotUp) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).WillOnce(DoAll(
      SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
          R"pb(notification {
                 timestamp: 1620348032128305716
                 prefix { origin: "openconfig" }
                 update {
                   path { elem { name: "interfaces" } }
                   val {
                     json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet0\",\"state\":{\"oper-status\":\"DOWN\"}}]}}"
                   }
                 }
               })pb")),
      Return(grpc::Status::OK)));

  EXPECT_THAT(
      CheckAllInterfaceOperStateOverGnmi(stub, /*interface_oper_state=*/"UP"),
      StatusIs(absl::StatusCode::kUnavailable,
               testing::HasSubstr("Interfaces are not ready")));
}

TEST(CheckAllInterfaceOperState, InterfaceNotDown) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).WillOnce(DoAll(
      SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
          R"pb(notification {
                 timestamp: 1620348032128305716
                 prefix { origin: "openconfig" }
                 update {
                   path { elem { name: "interfaces" } }
                   val {
                     json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet0\",\"state\":{\"oper-status\":\"TESTING\"}}]}}"
                   }
                 }
               })pb")),
      Return(grpc::Status::OK)));

  EXPECT_THAT(
      CheckAllInterfaceOperStateOverGnmi(stub, /*interface_oper_state=*/"DOWN"),
      StatusIs(absl::StatusCode::kUnavailable,
               testing::HasSubstr("Interfaces are not ready")));
}

TEST(CheckAllInterfaceOperState, AllInterfacesUp) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).WillOnce(DoAll(
      SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
          R"pb(notification {
                 timestamp: 1620348032128305716
                 prefix { origin: "openconfig" }
                 update {
                   path { elem { name: "interfaces" } }
                   val {
                     json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet1\",\"state\":{\"oper-status\":\"UP\"}}]}}"
                   }
                 }
               })pb")),
      Return(grpc::Status::OK)));

  ASSERT_OK(
      CheckAllInterfaceOperStateOverGnmi(stub, /*interface_oper_state=*/"UP"));
}

TEST(GetUpInterfaces, FailsToGetInterfaceOperStatusMap) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).WillOnce(
      Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  EXPECT_THAT(GetUpInterfacesOverGnmi(stub),
              StatusIs(absl::StatusCode::kDeadlineExceeded));
}

TEST(GetUpInterfaces, SuccessfullyGetsUpInterface) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).WillOnce(DoAll(
      SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
          R"pb(notification {
                 timestamp: 1620348032128305716
                 prefix { origin: "openconfig" }
                 update {
                   path { elem { name: "interfaces" } }
                   val {
                     json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"bond0\",\"state\":{\"oper-status\":\"UP\"}},{\"name\":\"Ethernet0\",\"state\":{\"oper-status\":\"UP\"}}]}}"
                   }
                 }
               })pb")),
      Return(grpc::Status::OK)));

  auto statusor = GetUpInterfacesOverGnmi(stub);
  ASSERT_OK(statusor);
  EXPECT_THAT(*statusor,
              testing::ContainerEq(std::vector<std::string>{"Ethernet0"}));
}

}  // namespace
}  // namespace pins_test
