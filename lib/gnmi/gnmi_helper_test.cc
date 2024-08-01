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
#include <utility>
#include <vector>

#include "absl/container/btree_set.h"
#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/escaping.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "github.com/openconfig/gnoi/types/types.pb.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "include/nlohmann/json.hpp"
#include "proto/gnmi/gnmi.pb.h"
#include "proto/gnmi/gnmi_mock.grpc.pb.h"

namespace pins_test {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::testing::_;
using ::testing::DoAll;
using ::testing::ElementsAre;
using ::testing::Eq;
using ::testing::HasSubstr;
using ::testing::IsEmpty;
using ::testing::Return;
using ::testing::SetArgPointee;
using ::testing::StrEq;
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

TEST(ConvertOCStringToPath, RegressionTest20220401) {
  EXPECT_THAT(ConvertOCStringToPath(
                  "openconfig-qos:qos/scheduler-policies/"
                  "scheduler-policy[name=\"foo\"]/schedulers/"
                  "scheduler[sequence=12]/two-rate-three-color/config/pir"),
              EqualsProto(R"pb(
                elem { name: "openconfig-qos:qos" }
                elem { name: "scheduler-policies" }
                elem {
                  name: "scheduler-policy"
                  key { key: "name" value: "\"foo\"" }
                }
                elem { name: "schedulers" }
                elem {
                  name: "scheduler"
                  key { key: "sequence" value: "12" }
                }
                elem { name: "two-rate-three-color" }
                elem { name: "config" }
                elem { name: "pir" }
              )pb"));
}

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

TEST(GnmiToGnoiPath, ConversionWorks) {
  EXPECT_THAT(GnmiToGnoiPath(
                  ConvertOCStringToPath("interfaces/interface[name=ethernet0]/"
                                        "config/mtu/ic[name=1/1]/value")),
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

// Constructs a standard gNMI response using the `oc_path` to construct a
// path and the `gnmi_config` as the response value.
gnmi::GetResponse ConstructResponse(absl::string_view oc_path,
                                    absl::string_view gnmi_config) {
  std::string response = absl::Substitute(
      R"pb(notification {
             timestamp: 1620348032128305716
             prefix { origin: "openconfig" }
             update {
               path { $0 }
               val { json_ietf_val: "$1" }
             }
           })pb",
      ConvertOCStringToPath(oc_path).DebugString(), absl::CEscape(gnmi_config));
  return gutil::ParseProtoOrDie<gnmi::GetResponse>(response);
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

TEST(GetAllSystemProcesses, FailedRPCReturnsError) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get(_,
                        EqualsProto(gutil::ParseProtoOrDie<gnmi::GetRequest>(
                            R"pb(prefix { origin: "openconfig" }
                                 path {
                                   elem { name: "system" }
                                   elem { name: "processes" }
                                 }
                                 type: STATE)pb")),
                        _))
      .WillOnce(Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  EXPECT_THAT(GetAllSystemProcesses(stub),
              StatusIs(absl::StatusCode::kDeadlineExceeded));
}

TEST(GetSystemMemory, FailedRPCReturnsError) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get(_,
                        EqualsProto(gutil::ParseProtoOrDie<gnmi::GetRequest>(
                            R"pb(prefix { origin: "openconfig" }
                                 path {
                                   elem { name: "system" }
                                   elem { name: "memory" }
                                 }
                                 type: STATE)pb")),
                        _))
      .WillOnce(Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  EXPECT_THAT(GetSystemMemory(stub),
              StatusIs(absl::StatusCode::kDeadlineExceeded));
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

TEST(ConstructedOpenConfig, NoInterfacesIsEmptyConfig) {
  ASSERT_EQ(OpenConfigWithInterfaces(GnmiFieldType::kConfig, /*interfaces=*/{}),
            EmptyOpenConfig());
}

TEST(ConstructedOpenConfig, CreatesACorrectConfig) {
  std::string reference_config_with_two_interfaces =
      R"({"openconfig-interfaces:interfaces":{"interface":[
      {
            "name" : "Ethernet0",
            "config" : {
              "openconfig-p4rt:id" : 2
            }
          }, {
            "name" : "Ethernet1",
            "config" : {
              "openconfig-p4rt:id" : 3
            }
          }
          ]}}
  )";

  ASSERT_EQ(nlohmann::json::parse(OpenConfigWithInterfaces(
                GnmiFieldType::kConfig,
                /*interfaces=*/{{.port_name = "Ethernet0", .port_id = 2},
                                {.port_name = "Ethernet1", .port_id = 3}})),
            nlohmann::json::parse(reference_config_with_two_interfaces));
}

TEST(GetInterfacePortIdMap, StubSuccessfullyReturnsInterfacePortIdMap) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).WillOnce(
      DoAll(SetArgPointee<2>(ConstructResponse(
                /*oc_path=*/"interfaces",
                /*gnmi_config=*/OpenConfigWithInterfaces(
                    GnmiFieldType::kState,
                    {{.port_name = "Ethernet0", .port_id = 1}}))),
            Return(grpc::Status::OK)));

  auto interface_name_to_port_id = GetAllInterfaceNameToPortId(stub);
  ASSERT_OK(interface_name_to_port_id);
  const absl::flat_hash_map<std::string, std::string> expected_map = {
      {"Ethernet0", "1"}};
  EXPECT_THAT(*interface_name_to_port_id,
              UnorderedPointwise(Eq(), expected_map));
}

TEST(GetInterfacePortIdMap, ConfigSuccessfullyReturnsInterfacePortIdMap) {
  auto interface_name_to_port_id =
      GetAllInterfaceNameToPortId(/*gnmi_config=*/OpenConfigWithInterfaces(
          GnmiFieldType::kConfig, {{.port_name = "Ethernet0", .port_id = 1}}));

  ASSERT_OK(interface_name_to_port_id);
  const absl::flat_hash_map<std::string, std::string> expected_map = {
      {"Ethernet0", "1"}};
  EXPECT_THAT(*interface_name_to_port_id,
              UnorderedPointwise(Eq(), expected_map));
}

TEST(GetAllPortIds, StubSuccessfullyReturnsPortIds) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).WillOnce(
      DoAll(SetArgPointee<2>(ConstructResponse(
                /*oc_path=*/"interfaces",
                /*gnmi_config=*/OpenConfigWithInterfaces(
                    GnmiFieldType::kState,
                    {{.port_name = "Ethernet0", .port_id = 1}}))),
            Return(grpc::Status::OK)));

  ASSERT_OK_AND_ASSIGN(auto port_ids, GetAllPortIds(stub));
  EXPECT_THAT(port_ids, ElementsAre("1"));
}

TEST(GetAllPortIds, ConfigSuccessfullyReturnsPortIds) {
  ASSERT_OK_AND_ASSIGN(
      auto port_ids,
      GetAllPortIds(/*gnmi_config=*/OpenConfigWithInterfaces(
          GnmiFieldType::kConfig, {
                                      {.port_name = "Ethernet1", .port_id = 2},
                                      {.port_name = "Ethernet0", .port_id = 1},
                                  })));

  EXPECT_THAT(port_ids, ElementsAre("1", "2"));
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
                     json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"CPU\",\"state\":{\"name\":\"CPU\"}},{\"name\":\"Ethernet0\",\"state\":{\"name\":\"Ethernet0\"}}]}}"
                   }
                 }
               })pb")),
      Return(grpc::Status::OK)));

  EXPECT_THAT(GetAllInterfaceNameToPortId(stub), IsOkAndHolds(IsEmpty()));
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
      CheckInterfaceOperStateOverGnmi(stub, /*interface_oper_state=*/"UP"),
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
      CheckInterfaceOperStateOverGnmi(stub, /*interface_oper_state=*/"UP"),
      StatusIs(absl::StatusCode::kUnavailable,
               HasSubstr("Some interfaces are not in the expected state UP")));
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
      CheckInterfaceOperStateOverGnmi(stub, /*interface_oper_state=*/"DOWN"),
      StatusIs(
          absl::StatusCode::kUnavailable,
          HasSubstr("Some interfaces are not in the expected state DOWN")));
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
      CheckInterfaceOperStateOverGnmi(stub, /*interface_oper_state=*/"UP"));
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

TEST(WaitForGnmiPortIdConvergenceTest, SwitchConvergesSuccessfully) {
  gnmi::MockgNMIStub mock_stub;

  // gNMI will report the state as mapping from Ethernet0 -> 1.
  gnmi::GetResponse response;
  *response.add_notification()
       ->add_update()
       ->mutable_val()
       ->mutable_json_ietf_val() = OpenConfigWithInterfaces(
      GnmiFieldType::kState, {{.port_name = "Ethernet0", .port_id = 1}});
  EXPECT_CALL(mock_stub, Get)
      .WillOnce(DoAll(SetArgPointee<2>(response), Return(grpc::Status::OK)));

  // Push the config with Ethernet0 -> 1.
  EXPECT_OK(WaitForGnmiPortIdConvergence(
      mock_stub,
      OpenConfigWithInterfaces(GnmiFieldType::kConfig,
                               {{.port_name = "Ethernet0", .port_id = 1}}),
      absl::Seconds(1)));
}

TEST(WaitForGnmiPortIdConvergenceTest, SwitchDoesNotCoverge) {
  gnmi::MockgNMIStub mock_stub;

  // gNMI will report the state as mapping from Ethernet0 -> 2.
  gnmi::GetResponse response;
  *response.add_notification()
       ->add_update()
       ->mutable_val()
       ->mutable_json_ietf_val() = OpenConfigWithInterfaces(
      GnmiFieldType::kState, {{.port_name = "Ethernet0", .port_id = 2}});
  EXPECT_CALL(mock_stub, Get)
      .WillRepeatedly(
          DoAll(SetArgPointee<2>(response), Return(grpc::Status::OK)));

  // Since we push a config with Ethernet0 -> 1 the switch should never
  // converge, and it should timetout.
  EXPECT_THAT(
      WaitForGnmiPortIdConvergence(
          mock_stub,
          OpenConfigWithInterfaces(GnmiFieldType::kConfig,
                                   {{.port_name = "Ethernet0", .port_id = 1}}),
          absl::Seconds(1)),
      StatusIs(absl::StatusCode::kFailedPrecondition));
}

TEST(WaitForGnmiPortIdConvergenceTest, ConfigDoesNotHavePortId) {
  gnmi::MockgNMIStub mock_stub;

  // gNMI will report the state, but it's missing the P4RT ID for Ethernet0.
  gnmi::GetResponse response;
  *response.add_notification()
       ->add_update()
       ->mutable_val()
       ->mutable_json_ietf_val() = R"(
    {
      "openconfig-interfaces:interfaces":{
        "interface" : [
          {
            "name" : "Ethernet0",
            "state" : {}
          }
        ]
      }
    })";
  EXPECT_CALL(mock_stub, Get)
      .WillRepeatedly(
          DoAll(SetArgPointee<2>(response), Return(grpc::Status::OK)));

  // Since we push a config with Ethernet0 -> 1 the switch should never
  // converge, and it should timetout.
  EXPECT_THAT(
      WaitForGnmiPortIdConvergence(
          mock_stub,
          OpenConfigWithInterfaces(GnmiFieldType::kConfig,
                                   {{.port_name = "Ethernet0", .port_id = 1}}),
          absl::Seconds(1)),
      StatusIs(absl::StatusCode::kFailedPrecondition));
}

TEST(WaitForGnmiPortIdConvergenceTest, ConfigDoesNotHaveAResponse) {
  gnmi::MockgNMIStub mock_stub;

  // gNMI will not report back any notification.
  gnmi::GetResponse response;
  EXPECT_CALL(mock_stub, Get)
      .WillRepeatedly(
          DoAll(SetArgPointee<2>(response), Return(grpc::Status::OK)));

  // Since the switch doesn't actually provide a notification it's misbehaving,
  // and we should return an internal error.
  EXPECT_THAT(
      WaitForGnmiPortIdConvergence(
          mock_stub,
          OpenConfigWithInterfaces(GnmiFieldType::kConfig,
                                   {{.port_name = "Ethernet0", .port_id = 1}}),
          absl::Seconds(1)),
      StatusIs(absl::StatusCode::kInternal));
}

TEST(InterfaceToTransceiver, WorksProperly) {
  gnmi::GetResponse response;
  *response.add_notification()
       ->add_update()
       ->mutable_val()
       ->mutable_json_ietf_val() = R"(
    {
      "openconfig-interfaces:interfaces": {
        "interface": [
          {
            "name": "CPU"
          },
          {
            "name": "Ethernet0",
            "state": {
              "openconfig-platform-transceiver:transceiver": "Ethernet1"
            }
          }
        ]
      }
    })";
  gnmi::MockgNMIStub mock_stub;
  EXPECT_CALL(mock_stub, Get)
      .WillRepeatedly(
          DoAll(SetArgPointee<2>(response), Return(grpc::Status::OK)));
  absl::flat_hash_map<std::string, std::string> expected_map{
      {"Ethernet0", "Ethernet1"}};
  EXPECT_THAT(GetInterfaceToTransceiverMap(mock_stub),
              IsOkAndHolds(UnorderedPointwise(Eq(), expected_map)));
}

TEST(TransceiverPartInformation, WorksProperly) {
  gnmi::GetResponse response;
  *response.add_notification()
       ->add_update()
       ->mutable_val()
       ->mutable_json_ietf_val() = R"(
    {
      "openconfig-platform:components": {
        "component": [
          {
            "name": "1/1"
          },
          {
            "name": "Ethernet1",
            "state": {
              "empty": false,
              "openconfig-platform-ext:vendor-name": "Vendor",
              "part-no": "123"
            }
          }
        ]
      }
    })";
  gnmi::MockgNMIStub mock_stub;
  EXPECT_CALL(mock_stub, Get)
      .WillRepeatedly(
          DoAll(SetArgPointee<2>(response), Return(grpc::Status::OK)));
  absl::flat_hash_map<std::string, TransceiverPart> expected_map{
      {"Ethernet1", TransceiverPart{.vendor = "Vendor", .part_number = "123"}}};
  EXPECT_THAT(GetTransceiverPartInformation(mock_stub),
              IsOkAndHolds(UnorderedPointwise(Eq(), expected_map)));
}

TEST(TransceiverPartInformation, EmptyTransceiver) {
  gnmi::GetResponse response;
  *response.add_notification()
       ->add_update()
       ->mutable_val()
       ->mutable_json_ietf_val() = R"(
    {
      "openconfig-platform:components": {
        "component": [
          {
            "name": "1/1"
          },
          {
            "name": "Ethernet1",
            "state": {
              "empty": true
            }
          }
        ]
      }
    })";
  gnmi::MockgNMIStub mock_stub;
  EXPECT_CALL(mock_stub, Get)
      .WillRepeatedly(
          DoAll(SetArgPointee<2>(response), Return(grpc::Status::OK)));
  EXPECT_THAT(GetTransceiverPartInformation(mock_stub),
              IsOkAndHolds(IsEmpty()));
}

TEST(TransceiverEthernetPmdType, WorksProperly) {
  gnmi::GetResponse response;
  *response.add_notification()
       ->add_update()
       ->mutable_val()
       ->mutable_json_ietf_val() = R"(
    {
      "openconfig-platform:components": {
        "component": [
          {
            "name": "1/1"
          },
          {
            "name": "Ethernet1",
            "state": {
              "empty": false
            },
            "openconfig-platform-transceiver:transceiver": {
              "state": {
                "ethernet-pmd": "openconfig-transport-types:ETH_10GBASE_LR"
              }
            }
          }
        ]
      }
    })";
  gnmi::MockgNMIStub mock_stub;
  EXPECT_CALL(mock_stub, Get)
      .WillRepeatedly(
          DoAll(SetArgPointee<2>(response), Return(grpc::Status::OK)));
  absl::flat_hash_map<std::string, std::string> expected_map{
      {"Ethernet1", "openconfig-transport-types:ETH_10GBASE_LR"}};
  EXPECT_THAT(GetTransceiverToEthernetPmdMap(mock_stub),
              IsOkAndHolds(UnorderedPointwise(Eq(), expected_map)));
}

TEST(InterfaceToSpeed, WorksProperly) {
  gnmi::GetResponse response;
  *response.add_notification()
       ->add_update()
       ->mutable_val()
       ->mutable_json_ietf_val() = R"(
    {
      "openconfig-interfaces:interfaces": {
        "interface": [
          {
            "name": "CPU"
          },
          {
            "name": "Ethernet1/1/1",
            "state": {
              "openconfig-platform-transceiver:physical-channel": [0,1,2,3]
            },
            "openconfig-if-ethernet:ethernet": {
              "state": {
                "port-speed": "openconfig-if-ethernet:SPEED_10GB"
              }
            }
          },
          {
            "name": "Ethernet1/2/1",
            "state": {
              "openconfig-platform-transceiver:physical-channel": []
            },
            "openconfig-if-ethernet:ethernet": {
              "state": {
                "port-speed": "openconfig-if-ethernet:SPEED_10GB"
              }
            }
          },
          {
            "name": "Ethernet1/3/1",
            "state": {
              "openconfig-platform-transceiver:physical-channel": [7]
            },
            "openconfig-if-ethernet:ethernet": {
              "state": {
                "port-speed": "openconfig-if-ethernet:SPEED_100GB"
              }
            }
          }
        ]
      }
    })";
  gnmi::MockgNMIStub mock_stub;
  EXPECT_CALL(mock_stub, Get)
      .WillRepeatedly(
          DoAll(SetArgPointee<2>(response), Return(grpc::Status::OK)));
  absl::flat_hash_map<std::string, int> expected_map{
      {"Ethernet1/1/1", 10'000'000 / 4}, {"Ethernet1/3/1", 100'000'000}};
  EXPECT_THAT(GetInterfaceToLaneSpeedMap(mock_stub),
              IsOkAndHolds(UnorderedPointwise(Eq(), expected_map)));
}

}  // namespace
}  // namespace pins_test
