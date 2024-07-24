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
using ::testing::Eq;
using ::testing::HasSubstr;
using ::testing::IsEmpty;
using ::testing::Return;
using ::testing::SetArgPointee;
using ::testing::UnorderedElementsAre;
using ::testing::UnorderedPointwise;

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
  EXPECT_THAT(
      GetInterfaceToOperStatusMapOverGnmi(stub, absl::Seconds(60)),
      StatusIs(absl::StatusCode::kInternal, HasSubstr("Invalid response")));
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

  EXPECT_THAT(
      GetInterfaceToOperStatusMapOverGnmi(stub, absl::Seconds(60)),
      StatusIs(absl::StatusCode::kNotFound,
               HasSubstr("'openconfig-interfaces:interfaces' not found")));
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
                       HasSubstr("'interface' not found")));
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

  EXPECT_THAT(
      GetInterfaceToOperStatusMapOverGnmi(stub, absl::Seconds(60)),
      StatusIs(absl::StatusCode::kNotFound, HasSubstr("'name' not found")));
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

  EXPECT_THAT(
      GetInterfaceToOperStatusMapOverGnmi(stub, absl::Seconds(60)),
      StatusIs(absl::StatusCode::kNotFound, HasSubstr("'state' not found")));
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
                       HasSubstr("'oper-status' not found")));
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
                     json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"CPU\"},{\"name\":\"Ethernet0\",\"state\":{\"oper-status\":\"DOWN\"}}]}}"
                   }
                 }
               })pb")),
      Return(grpc::Status::OK)));

  auto statusor = GetInterfaceToOperStatusMapOverGnmi(stub, absl::Seconds(60));
  ASSERT_OK(statusor);
  const absl::flat_hash_map<std::string, std::string> expected_map = {
      {"Ethernet0", "DOWN"}};
  EXPECT_THAT(*statusor, UnorderedPointwise(Eq(), expected_map));
}

TEST(GetInterfacePortIdMap, SuccessfullyReturnsInterfacePortIdMap) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).WillOnce(DoAll(
      SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
          R"pb(notification {
                 timestamp: 1620348032128305716
                 prefix { origin: "openconfig" }
                 update {
                   path { elem { name: "interfaces" } }
                   val {
                     json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet0\",\"state\":{\"openconfig-p4rt:id\":1}}]}}"
                   }
                 }
               })pb")),
      Return(grpc::Status::OK)));

  auto interface_name_to_port_id = GetAllInterfaceNameToPortId(stub);
  ASSERT_OK(interface_name_to_port_id);
  const absl::flat_hash_map<std::string, std::string> expected_map = {
      {"Ethernet0", "1"}};
  EXPECT_THAT(*interface_name_to_port_id,
              UnorderedPointwise(Eq(), expected_map));
}

TEST(GetInterfacePortIdMap, PortIdNotFoundInState) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).WillOnce(DoAll(
      SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
          R"pb(notification {
                 timestamp: 1620348032128305716
                 prefix { origin: "openconfig" }
                 update {
                   path { elem { name: "interfaces" } }
                   val {
                     json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"CPU\"},{\"name\":\"Ethernet0\",\"state\":{\"name\":\"Ethernet0\"}}]}}"
                   }
                 }
               })pb")),
      Return(grpc::Status::OK)));

  EXPECT_THAT(GetAllInterfaceNameToPortId(stub),
              StatusIs(absl::StatusCode::kNotFound,
                       HasSubstr("'openconfig-p4rt:id' not found")));
}

TEST(GetInterfacePortIdMap, InterfaceStateNotFound) {
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

  EXPECT_THAT(
      GetAllInterfaceNameToPortId(stub),
      StatusIs(absl::StatusCode::kNotFound, HasSubstr("'state' not found")));
}

TEST(GetInterfacePortIdMap, InterfaceNameNotFound) {
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

  EXPECT_THAT(
      GetAllInterfaceNameToPortId(stub),
      StatusIs(absl::StatusCode::kNotFound, HasSubstr("'name' not found")));
}

TEST(GetInterfacePortIdMap, InterfaceNotFoundInGnmiGetResponse) {
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

  EXPECT_THAT(GetAllInterfaceNameToPortId(stub),
              StatusIs(absl::StatusCode::kNotFound,
                       HasSubstr("'interface' not found")));
}

TEST(GetInterfacePortIdMap, GnmiGetResponseWithoutOpenconfigInterface) {
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

  EXPECT_THAT(
      GetAllInterfaceNameToPortId(stub),
      StatusIs(absl::StatusCode::kNotFound,
               HasSubstr("'openconfig-interfaces:interfaces' not found")));
}

TEST(GetInterfacePortIdMap, InvalidGnmiGetResponse) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).WillOnce(Return(grpc::Status::OK));
  EXPECT_THAT(
      GetAllInterfaceNameToPortId(stub),
      StatusIs(absl::StatusCode::kInternal, HasSubstr("Invalid response")));
}

TEST(GetInterfaceOperStatusOverGnmi, RpcFails) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub,
              Get(_, EqualsProto(R"pb(type: STATE
                                      prefix { origin: "openconfig" }
                                      path {
                                        elem { name: "interfaces" }
                                        elem {
                                          name: "interface"
                                          key { key: "name" value: "Ethernet0" }
                                        }
                                        elem { name: "state" }
                                        elem { name: "oper-status" }
                                      }
                  )pb"),
                  _))
      .WillOnce(Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  EXPECT_THAT(GetInterfaceOperStatusOverGnmi(stub, "Ethernet0"),
              StatusIs(absl::StatusCode::kDeadlineExceeded));
}

TEST(GetInterfaceOperStatusOverGnmi, InvalidResponse) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub,
              Get(_, EqualsProto(R"pb(type: STATE
                                      prefix { origin: "openconfig" }
                                      path {
                                        elem { name: "interfaces" }
                                        elem {
                                          name: "interface"
                                          key { key: "name" value: "Ethernet0" }
                                        }
                                        elem { name: "state" }
                                        elem { name: "oper-status" }
                                      }
                  )pb"),
                  _))
      .WillOnce(
          DoAll(SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
                    R"pb(notification {})pb")),
                Return(grpc::Status::OK)));
  EXPECT_THAT(GetInterfaceOperStatusOverGnmi(stub, "Ethernet0"),
              StatusIs(absl::StatusCode::kInternal));
}

TEST(GetInterfaceOperStatusOverGnmi, OperStatusUp) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub,
              Get(_, EqualsProto(R"pb(type: STATE
                                      prefix { origin: "openconfig" }
                                      path {
                                        elem { name: "interfaces" }
                                        elem {
                                          name: "interface"
                                          key { key: "name" value: "Ethernet0" }
                                        }
                                        elem { name: "state" }
                                        elem { name: "oper-status" }
                                      }
                  )pb"),
                  _))
      .WillOnce(DoAll(
          SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
              R"pb(notification {
                     timestamp: 1620348032128305716
                     prefix { origin: "openconfig" }
                     update {
                       path {
                         elem { name: "interfaces" }
                         elem {
                           name: "interface"
                           key { key: "name" value: "Ethernet0" }
                         }
                         elem { name: "state" }
                         elem { name: "oper-status" }
                       }
                       val {
                         json_ietf_val: "{\"openconfig-interfaces:oper-status\":{\"oper-status\":\"UP\"}}"
                       }
                     }
                   })pb")),
          Return(grpc::Status::OK)));
  EXPECT_THAT(GetInterfaceOperStatusOverGnmi(stub, "Ethernet0"),
              IsOkAndHolds(OperStatus::kUp));
}

TEST(GetInterfaceOperStatusOverGnmi, OperStatusDown) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub,
              Get(_, EqualsProto(R"pb(type: STATE
                                      prefix { origin: "openconfig" }
                                      path {
                                        elem { name: "interfaces" }
                                        elem {
                                          name: "interface"
                                          key { key: "name" value: "Ethernet0" }
                                        }
                                        elem { name: "state" }
                                        elem { name: "oper-status" }
                                      }
                  )pb"),
                  _))
      .WillOnce(DoAll(
          SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
              R"pb(notification {
                     timestamp: 1620348032128305716
                     prefix { origin: "openconfig" }
                     update {
                       path {
                         elem { name: "interfaces" }
                         elem {
                           name: "interface"
                           key { key: "name" value: "Ethernet0" }
                         }
                         elem { name: "state" }
                         elem { name: "oper-status" }
                       }
                       val {
                         json_ietf_val: "{\"openconfig-interfaces:oper-status\":{\"oper-status\":\"DOWN\"}}"
                       }
                     }
                   })pb")),
          Return(grpc::Status::OK)));
  EXPECT_THAT(GetInterfaceOperStatusOverGnmi(stub, "Ethernet0"),
              IsOkAndHolds(OperStatus::kDown));
}

TEST(GetInterfaceOperStatusOverGnmi, OperStatusTesting) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub,
              Get(_, EqualsProto(R"pb(type: STATE
                                      prefix { origin: "openconfig" }
                                      path {
                                        elem { name: "interfaces" }
                                        elem {
                                          name: "interface"
                                          key { key: "name" value: "Ethernet0" }
                                        }
                                        elem { name: "state" }
                                        elem { name: "oper-status" }
                                      }
                  )pb"),
                  _))
      .WillOnce(DoAll(
          SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
              R"pb(notification {
                     timestamp: 1620348032128305716
                     prefix { origin: "openconfig" }
                     update {
                       path {
                         elem { name: "interfaces" }
                         elem {
                           name: "interface"
                           key { key: "name" value: "Ethernet0" }
                         }
                         elem { name: "state" }
                         elem { name: "oper-status" }
                       }
                       val {
                         json_ietf_val: "{\"openconfig-interfaces:oper-status\":{\"oper-status\":\"TESTING\"}}"
                       }
                     }
                   })pb")),
          Return(grpc::Status::OK)));
  EXPECT_THAT(GetInterfaceOperStatusOverGnmi(stub, "Ethernet0"),
              IsOkAndHolds(OperStatus::kTesting));
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
               HasSubstr("Interfaces are not ready")));
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
               HasSubstr("Interfaces are not ready")));
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

TEST(CheckInterfaceOperState, FailsToGetInterfaceOperStatusMap) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).WillOnce(
      Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  EXPECT_THAT(CheckInterfaceOperStateOverGnmi(
                  stub, /*interface_oper_state=*/"UP", {"Ethernet0"}),
              StatusIs(absl::StatusCode::kDeadlineExceeded));
}

TEST(CheckInterfaceOperState, InterfaceNotUp) {
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
      CheckInterfaceOperStateOverGnmi(stub, /*interface_oper_state=*/"UP",
                                      {"Ethernet0"}),
      StatusIs(absl::StatusCode::kUnavailable,
               HasSubstr("Some interfaces are not in the expected state")));
}

TEST(CheckInterfaceOperState, InterfaceNotDown) {
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
      CheckInterfaceOperStateOverGnmi(stub, /*interface_oper_state=*/"DOWN",
                                      {"Ethernet0"}),
      StatusIs(absl::StatusCode::kUnavailable,
               HasSubstr("Some interfaces are not in the expected state")));
}

TEST(CheckInterfaceOperState, InterfaceDownUp) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).WillOnce(DoAll(
      SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
          R"pb(notification {
                 timestamp: 1620348032128305716
                 prefix { origin: "openconfig" }
                 update {
                   path { elem { name: "interfaces" } }
                   val {
                     json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet0\",\"state\":{\"oper-status\":\"UP\"}},{\"name\":\"Ethernet4\",\"state\":{\"oper-status\":\"DOWN\"}}]}}"
                   }
                 }
               })pb")),
      Return(grpc::Status::OK)));

  EXPECT_THAT(
      CheckInterfaceOperStateOverGnmi(stub, /*interface_oper_state=*/"UP",
                                      {"Ethernet0", "Ethernet4"}),
      StatusIs(absl::StatusCode::kUnavailable,
               HasSubstr("Some interfaces are not in the expected state")));
}

TEST(CheckInterfaceOperState, AllInterfacesUp) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).WillOnce(DoAll(
      SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
          R"pb(notification {
                 timestamp: 1620348032128305716
                 prefix { origin: "openconfig" }
                 update {
                   path { elem { name: "interfaces" } }
                   val {
                     json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"Ethernet0\",\"state\":{\"oper-status\":\"UP\"}}]}}"
                   }
                 }
               })pb")),
      Return(grpc::Status::OK)));

  ASSERT_OK(CheckInterfaceOperStateOverGnmi(stub, /*interface_oper_state=*/"UP",
                                            {"Ethernet0"}));
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

TEST(CheckParseGnmiGetResponse, FailDuetoResponseSize) {
  gnmi::GetResponse response;
  for (int i = 0; i < 2; i++) {
    gnmi::Notification *notification = response.add_notification();
    notification->set_timestamp(1620348032128305716);
  }
  EXPECT_THAT(
      ParseGnmiGetResponse(response, "openconfig-interfaces:oper-status"),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr("Unexpected size in response")));
}

TEST(CheckParseGnmiGetResponse, FailDuetoUpdateSize) {
  gnmi::GetResponse response;
  gnmi::Notification *notification = response.add_notification();

  for (int i = 0; i < 2; i++) {
    notification->add_update();
  }
  EXPECT_THAT(
      ParseGnmiGetResponse(response, "openconfig-interfaces:oper-status"),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr("Unexpected update size in response")));
}

TEST(CheckParseGnmiGetResponse, UnexpectedDataFormat) {
  gnmi::GetResponse response;
  constexpr char kOperstatus[] = "UP";
  gnmi::Notification *notification = response.add_notification();
  gnmi::Update *update = notification->add_update();

  *update->mutable_path() = ConvertOCStringToPath(
      "interfaces/interface[name=Ethernet8]/state/oper-status");
  update->mutable_val()->set_ascii_val(kOperstatus);
  LOG(INFO) << "response: " << response.DebugString();
  EXPECT_THAT(
      ParseGnmiGetResponse(response, "openconfig-interfaces:oper-status"),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr("Unexpected data type:")));
}
TEST(CheckParseGnmiGetResponse, FailDuetoMissingTag) {
  gnmi::GetResponse response;
  constexpr char kOperstatus[] =
      R"({"openconfig-interfaces:status":"TESTING"})";
  gnmi::Notification *notification = response.add_notification();
  gnmi::Update *update = notification->add_update();
  *update->mutable_path() =
      ConvertOCStringToPath("interfaces/interface[name=Ethernet8]/state");
  update->mutable_val()->set_json_ietf_val(kOperstatus);
  LOG(INFO) << "response: " << response.DebugString();
  EXPECT_THAT(
      ParseGnmiGetResponse(response, "openconfig-interfaces:oper-status"),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr("not present in JSON response")));
}
TEST(CheckParseGnmiGetResponse, FailDuetoWrongResponse) {
  gnmi::GetResponse response;
  constexpr char kOperstatus[] =
      R"({"openconfig-interfaces:oper-status":"TESTING"})";
  gnmi::Notification *notification = response.add_notification();
  gnmi::Update *update = notification->add_update();

  *update->mutable_path() = ConvertOCStringToPath(
      "interfaces/interface[name=Ethernet8]/state/oper-status");
  update->mutable_val()->set_json_ietf_val(kOperstatus);
  LOG(INFO) << "response: " << response.DebugString();
  EXPECT_THAT(
      ParseGnmiGetResponse(response, "openconfig-interfaces:oper-status"),
      IsOkAndHolds(Not(HasSubstr("UP"))));
}

TEST(CheckParseGnmiGetResponse, JsonIetfResponseSuccess) {
  gnmi::GetResponse response;
  constexpr char kOperstatus[] =
      R"({"openconfig-interfaces:oper-status":"UP"})";
  gnmi::Notification *notification = response.add_notification();
  gnmi::Update *update = notification->add_update();

  *update->mutable_path() = ConvertOCStringToPath(
      "interfaces/interface[name=Ethernet8]/state/oper-status");
  update->mutable_val()->set_json_ietf_val(kOperstatus);
  LOG(INFO) << "response: " << response.DebugString();
  EXPECT_THAT(
      ParseGnmiGetResponse(response, "openconfig-interfaces:oper-status"),
      IsOkAndHolds(HasSubstr("UP")));
}

TEST(CheckParseGnmiGetResponse, JsonResponseSuccess) {
  gnmi::GetResponse response;
  constexpr char kOperstatus[] =
      R"({"openconfig-interfaces:oper-status":"UP"})";
  gnmi::Notification *notification = response.add_notification();
  gnmi::Update *update = notification->add_update();

  *update->mutable_path() = ConvertOCStringToPath(
      "interfaces/interface[name=Ethernet8]/state/oper-status");
  update->mutable_val()->set_json_val(kOperstatus);
  LOG(INFO) << "response: " << response.DebugString();
  EXPECT_THAT(
      ParseGnmiGetResponse(response, "openconfig-interfaces:oper-status"),
      IsOkAndHolds(HasSubstr("UP")));
}

TEST(CheckParseGnmiGetResponse, StringResponseSuccess) {
  gnmi::GetResponse response;
  constexpr char kOperstatus[] = "UP";
  gnmi::Notification *notification = response.add_notification();
  gnmi::Update *update = notification->add_update();

  *update->mutable_path() = ConvertOCStringToPath(
      "interfaces/interface[name=Ethernet8]/state/oper-status");
  update->mutable_val()->set_string_val(kOperstatus);
  LOG(INFO) << "response: " << response.DebugString();
  EXPECT_THAT(
      ParseGnmiGetResponse(response, "openconfig-interfaces:oper-status"),
      IsOkAndHolds(HasSubstr("UP")));
}
}  // namespace
}  // namespace pins_test
