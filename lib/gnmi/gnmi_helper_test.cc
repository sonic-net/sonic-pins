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
#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/escaping.h"
#include "absl/strings/match.h"
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
#include "lib/gnmi/openconfig.pb.h"
#include "proto/gnmi/gnmi.pb.h"
#include "proto/gnmi/gnmi_mock.grpc.pb.h"

namespace pins_test {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOk;
using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::testing::_;
using ::testing::AllOf;
using ::testing::ContainerEq;
using ::testing::DoAll;
using ::testing::ElementsAre;
using ::testing::Eq;
using ::testing::HasSubstr;
using ::testing::InSequence;
using ::testing::IsEmpty;
using ::testing::IsSubsetOf;
using ::testing::Not;
using ::testing::Return;
using ::testing::SetArgPointee;
using ::testing::SizeIs;
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

// Used by UpdateDeviceId tests as a canonical config with device ID 123456.
// Notice that there are no spaces. This is because the json.dump() call does
// not include any.
static constexpr char kDeviceIdIs123456[] =
    R"({"openconfig-platform:components":{"component":[{"integrated-circuit":{"config":{"openconfig-p4rt:node-id":"123456"}},"name":"integrated_circuit0"}]}})";

static constexpr char kBreakoutSample[] = R"(
    {
      "openconfig-platform:components": {
        "component":[
          {
            "config" : {
               "name" : "1/1"
            },
            "name" : "1/1",
            "port" : {
               "config" : {
                  "openconfig-pins-platform-port:port-id" : 1
               },
               "openconfig-platform-port:breakout-mode" : {
                  "groups" : {
                     "group" : [
                        {
                           "config" : {
                              "breakout-speed" : "openconfig-if-ethernet:SPEED_400GB",
                              "index" : 0,
                              "num-breakouts" : 2,
                              "num-physical-channels" : 4
                           },
                           "index" : 0
                        }
                     ]
                  }
               }
            }
         },
         {
            "config" : {
               "name" : "1/2"
            },
            "name" : "1/2",
            "port" : {
               "config" : {
                  "openconfig-pins-platform-port:port-id" : 2
               },
               "openconfig-platform-port:breakout-mode" : {
                  "groups" : {
                     "group" : [
                        {
                           "config" : {
                              "breakout-speed" : "openconfig-if-ethernet:SPEED_400GB",
                              "index" : 0,
                              "num-breakouts" : 1,
                              "num-physical-channels" : 4
                           },
                           "index" : 0
                        },
                        {
                           "config" : {
                              "breakout-speed" : "openconfig-if-ethernet:SPEED_200GB",
                              "index" : 1,
                              "num-breakouts" : 2,
                              "num-physical-channels" : 2
                           },
                           "index" : 1
                        }
                     ]
                  }
               }
            }
         },
         {
            "config" : {
               "name" : "1/10"
            },
            "name" : "1/10",
            "port" : {
               "config" : {
                  "openconfig-pins-platform-port:port-id" : 10
               },
               "openconfig-platform-port:breakout-mode" : {
                  "groups" : {
                     "group" : [
                        {
                           "config" : {
                              "breakout-speed" : "openconfig-if-ethernet:SPEED_200GB",
                              "index" : 0,
                              "num-breakouts" : 2,
                              "num-physical-channels" : 2
                           },
                           "index" : 0
                        },
                        {
                           "config" : {
                              "breakout-speed" : "openconfig-if-ethernet:SPEED_400GB",
                              "index" : 1,
                              "num-breakouts" : 1,
                              "num-physical-channels" : 4
                           },
                           "index" : 1
                        }
                     ]
                  }
               }
            }
         },
         {
            "config" : {
               "name" : "1/14"
            },
            "name" : "1/14",
            "port" : {
               "config" : {
                  "openconfig-pins-platform-port:port-id" : 14
               },
               "openconfig-platform-port:breakout-mode" : {
                  "groups" : {
                     "group" : [
                        {
                           "config" : {
                              "breakout-speed" : "openconfig-if-ethernet:SPEED_200GB",
                              "index" : 0,
                              "num-breakouts" : 4,
                              "num-physical-channels" : 2
                           },
                           "index" : 0
                        }
                     ]
                  }
               }
            }
         }
        ]
      }
    }
  )";

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

TEST(OCStringToPath, OCStringToPathMultipleKeyTestCase) {
  EXPECT_THAT(ConvertOCStringToPath(
                  "/sampling/sflow/collectors/"
                  "collector[address=127.0.0.1][port=6343]/state/address"),
              EqualsProto(R"pb(
                elem { name: "sampling" }
                elem { name: "sflow" }
                elem { name: "collectors" }
                elem {
                  name: "collector"
                  key { key: "address" value: "127.0.0.1" }
                  key { key: "port" value: "6343" }
                }
                elem { name: "state" }
                elem { name: "address" }
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

bool IsEnabledEthernetInterface(
    const openconfig::Interfaces::Interface &interface) {
  return interface.config().enabled() &&
         absl::StartsWith(interface.name(), /*prefix=*/"Ethernet");
}

TEST(MapP4rtIdsToMatchingInterfaces, FailsOnTooFewMatchingInterfaces) {
  gnmi::MockgNMIStub stub;
  std::string reference_config =
      R"json({
      "openconfig-interfaces:interfaces":{
        "interface":[
          {
            "name":"Loopback0",
            "config":{
              "enabled":true,
              "openconfig-p4rt:id":1
            }
          },
          {
            "name":"EthernetEnabled0",
            "config":{
              "enabled":true,
              "openconfig-p4rt:id":2
            }
          },
          {
            "name":"EthernetDisabled0",
            "config":{
              "enabled":false,
              "openconfig-p4rt:id":3
            }
          }
        ]
      }
    })json";

  EXPECT_CALL(stub, Get).WillOnce(DoAll(SetArgPointee<2>(ConstructResponse(
                                            /*oc_path=*/"interfaces",
                                            /*gnmi_config=*/reference_config)),
                                        Return(grpc::Status::OK)));

  ASSERT_THAT(
      MapP4rtIdsToMatchingInterfaces(stub, /*desired_p4rt_port_ids=*/{4, 5},
                                     /*predicate=*/IsEnabledEthernetInterface),
      Not(IsOk()));
}

TEST(GetInterfacePortIdMap, ReturnsOnlyEnabledInterfaces) {
  gnmi::MockgNMIStub stub;
  std::string reference_config =
      R"json({
      "openconfig-interfaces:interfaces":{
        "interface":[
          {
            "name":"Ethernet0",
            "config":{
              "enabled":true,
              "openconfig-p4rt:id":1
            }
          },
          {
            "name":"Ethernet1",
            "config":{
              "enabled":false,
              "openconfig-p4rt:id":2
            }
          },
          {
            "name":"Ethernet2",
            "config":{
              "enabled":true,
              "openconfig-p4rt:id":3
            }
          }
        ]
      }
    })json";
  EXPECT_CALL(stub, Get).WillOnce(DoAll(SetArgPointee<2>(ConstructResponse(
                                            /*oc_path=*/"interfaces",
                                            /*gnmi_config=*/reference_config)),
                                        Return(grpc::Status::OK)));

  const absl::flat_hash_map<std::string, std::string> expected_map = {
      {"Ethernet0", "1"}, {"Ethernet2", "3"}};
  EXPECT_THAT(GetAllEnabledInterfaceNameToPortId(stub),
              IsOkAndHolds(UnorderedPointwise(Eq(), expected_map)));
}

TEST(GetInterfacePortIdMap, ReturnsOnlyUpInterfacesWithIDs) {
  std::string interface_state = R"json({
    "openconfig-interfaces:interfaces":{
      "interface":[
        {
          "name":"bond0",
          "state":{"oper-status":"UP","openconfig-p4rt:id":1}
        },
        {
          "name":"Ethernet1/1/1",
          "state":{"oper-status":"UP","openconfig-p4rt:id":2}
        },
        {
          "name":"Ethernet1/2/1",
          "state":{"oper-status":"DOWN","openconfig-p4rt:id":3}
        },
        {
          "name":"Ethernet1/3/1",
          "state":{"oper-status":"UP"}
        },
        {
          "name":"Ethernet1/4/1",
          "state":{"oper-status":"UP","openconfig-p4rt:id":4}
        }
      ]
    }
  })json";

  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).Times(2).WillRepeatedly(
      DoAll(SetArgPointee<2>(ConstructResponse(
                /*oc_path=*/"interfaces",
                /*gnmi_config=*/interface_state)),
            Return(grpc::Status::OK)));

  EXPECT_THAT(GetAllUpInterfacePortIdsByName(stub),
              IsOkAndHolds(UnorderedPointwise(
                  Eq(), absl::flat_hash_map<std::string, std::string>{
                            {"Ethernet1/1/1", "2"},
                            {"Ethernet1/4/1", "4"},
                        })));
}

TEST(GetUpInterfacePortIDs, CanGetNUpInterfaces) {
  std::string interface_state = R"json({
    "openconfig-interfaces:interfaces":{
      "interface":[
        {
          "name":"bond0",
          "state":{"oper-status":"UP","openconfig-p4rt:id":1}
        },
        {
          "name":"Ethernet1/1/1",
          "state":{"oper-status":"UP","openconfig-p4rt:id":2}
        },
        {
          "name":"Ethernet1/2/1",
          "state":{"oper-status":"DOWN","openconfig-p4rt:id":3}
        },
        {
          "name":"Ethernet1/3/1",
          "state":{"oper-status":"UP"}
        },
        {
          "name":"Ethernet1/4/1",
          "state":{"oper-status":"UP","openconfig-p4rt:id":4}
        },
        {
          "name":"Ethernet1/5/1",
          "state":{"oper-status":"UP","openconfig-p4rt:id":5}
        }
      ]
    }
  })json";

  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).Times(2).WillRepeatedly(
      DoAll(SetArgPointee<2>(ConstructResponse(
                /*oc_path=*/"interfaces",
                /*gnmi_config=*/interface_state)),
            Return(grpc::Status::OK)));

  // There are 3 valid ports, but we only choose 2. So we expect the result to
  // be a subset of the valid ports.
  EXPECT_THAT(GetNUpInterfacePortIds(stub, 2),
              IsOkAndHolds(IsSubsetOf({"2", "4", "5"})));
}

TEST(GetUpInterfacePortIDs, GetNFailsWhenNotEnoughInterfacesAreUpWithAPortId) {
  std::string interface_state = R"json({
    "openconfig-interfaces:interfaces":{
      "interface":[
        {
          "name":"bond0",
          "state":{"oper-status":"UP","openconfig-p4rt:id":1}
        },
        {
          "name":"Ethernet1/1/1",
          "state":{"oper-status":"UP","openconfig-p4rt:id":2}
        },
        {
          "name":"Ethernet1/2/1",
          "state":{"oper-status":"DOWN","openconfig-p4rt:id":3}
        },
        {
          "name":"Ethernet1/3/1",
          "state":{"oper-status":"UP"}
        },
        {
          "name":"Ethernet1/4/1",
          "state":{"oper-status":"UP","openconfig-p4rt:id":4}
        }
      ]
    }
  })json";

  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).Times(2).WillRepeatedly(
      DoAll(SetArgPointee<2>(ConstructResponse(
                /*oc_path=*/"interfaces",
                /*gnmi_config=*/interface_state)),
            Return(grpc::Status::OK)));

  EXPECT_THAT(GetNUpInterfacePortIds(stub, 3),
              StatusIs(absl::StatusCode::kFailedPrecondition));
}

TEST(GetUpInterfacePortIDs, CanGetAnyInterfaceThatIsUpWithAPortId) {
  std::string interface_state = R"json({
    "openconfig-interfaces:interfaces":{
      "interface":[
        {
          "name":"bond0",
          "state":{"oper-status":"UP","openconfig-p4rt:id":1}
        },
        {
          "name":"Ethernet1/1/1",
          "state":{"oper-status":"UP","openconfig-p4rt:id":2}
        },
        {
          "name":"Ethernet1/2/1",
          "state":{"oper-status":"DOWN","openconfig-p4rt:id":3}
        },
        {
          "name":"Ethernet1/3/1",
          "state":{"oper-status":"UP"}
        },
        {
          "name":"Ethernet1/4/1",
          "state":{"oper-status":"UP","openconfig-p4rt:id":4}
        }
      ]
    }
  })json";

  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).Times(2).WillRepeatedly(
      DoAll(SetArgPointee<2>(ConstructResponse(
                /*oc_path=*/"interfaces",
                /*gnmi_config=*/interface_state)),
            Return(grpc::Status::OK)));

  // There are 2 valid ports, but only one will be chosen. So we wrap the result
  // in a vector which we expect to be a subset of the valid ports.
  ASSERT_OK_AND_ASSIGN(std::string id, GetAnyUpInterfacePortId(stub));
  EXPECT_THAT(std::vector<std::string>{id}, IsSubsetOf({"2", "4"}));
}

TEST(GetUpInterfacePortIDs, GetAnyFailsWhenNoInterfacesAreUpOrHaveAPortId) {
  std::string interface_state = R"json({
    "openconfig-interfaces:interfaces":{
      "interface":[
        {
          "name":"bond0",
          "state":{"oper-status":"UP","openconfig-p4rt:id":1}
        },
        {
          "name":"Ethernet1/1/1",
          "state":{"oper-status":"UP"}
        },
        {
          "name":"Ethernet1/2/1",
          "state":{"oper-status":"DOWN","openconfig-p4rt:id":3}
        }
      ]
    }
  })json";

  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).Times(2).WillRepeatedly(
      DoAll(SetArgPointee<2>(ConstructResponse(
                /*oc_path=*/"interfaces",
                /*gnmi_config=*/interface_state)),
            Return(grpc::Status::OK)));

  EXPECT_THAT(GetAnyUpInterfacePortId(stub),
              StatusIs(absl::StatusCode::kFailedPrecondition));
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
  EXPECT_THAT(*statusor, ContainerEq(std::vector<std::string>{"Ethernet0"}));
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
              "part-no": "123",
              "mfg-name": "manufactuer",
              "serial-no": "serial",
              "firmware-version": "ab"
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
      {"Ethernet1", TransceiverPart{.vendor = "Vendor",
                                    .part_number = "123",
                                    .manufacturer_name = "manufactuer",
                                    .serial_number = "serial",
                                    .rev = "ab"}}};
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

TEST(UpdateDeviceId, WhenValueAlreadyExists) {
  std::string gnmi_config = R"({
    "openconfig-platform:components" : {
       "component" : [
          {
             "integrated-circuit" : {
                "config" : {
                   "openconfig-p4rt:node-id" : "3232235555"
                }
             },
             "name" : "integrated_circuit0"
          }
       ]
    }})";
  EXPECT_THAT(UpdateDeviceIdInJsonConfig(gnmi_config, "123456"),
              StrEq(kDeviceIdIs123456));
}

TEST(UpdateDeviceId, WithEmptyConfig) {
  // Test with null config.
  EXPECT_THAT(UpdateDeviceIdInJsonConfig("", "123456"),
              StrEq(kDeviceIdIs123456));

  // And with empty json object.
  EXPECT_THAT(UpdateDeviceIdInJsonConfig("{}", "123456"),
              StrEq(kDeviceIdIs123456));
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

TEST(TransceiverFormFactor, WorksProperly) {
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
                "form-factor": "openconfig-transport-types:OSFP"
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
      {"Ethernet1", "openconfig-transport-types:OSFP"}};
  EXPECT_THAT(GetTransceiverToFormFactorMap(mock_stub),
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
          },
          {
            "name": "Ethernet1/33/1",
            "state": {
            },
            "openconfig-if-ethernet:ethernet": {
              "state": {
                "port-speed": "openconfig-if-ethernet:SPEED_10GB"
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
  absl::flat_hash_set<std::string> interface_names{"Ethernet1/1/1",
                                                   "Ethernet1/3/1"};
  EXPECT_THAT(GetInterfaceToLaneSpeedMap(mock_stub, interface_names),
              IsOkAndHolds(UnorderedPointwise(Eq(), expected_map)));
}

TEST(GetGnmiStatePathAndTimestamp, VerifyValue) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).WillOnce(DoAll(
      SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
          R"pb(notification {
                 timestamp: 1656026017779182564
                 prefix { origin: "openconfig" }
                 update {
                   path {
                     elem { name: "interfaces" }
                     elem {
                       name: "interface"
                       key { key: "name" value: "Ethernet1/4/1" }
                     }
                     elem { name: "state" }
                     elem { name: "counters" }
                     elem { name: "in-pkts" }
                   }
                   val {
                     json_ietf_val: "{\"openconfig-interfaces:in-pkts\":\"723563785\"}"
                   }
                 }
               })pb")),
      Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(
      auto result,
      GetGnmiStatePathAndTimestamp(
          &stub, "interfaces/interface[name=\"Ethernet1/4/1\"]/state/counters",
          "openconfig-interfaces:in-pkts"));
  EXPECT_EQ(result.timestamp, 1656026017779182564);
  EXPECT_EQ(result.response, "723563785");
}

TEST(GetGnmiStatePathAndTimestamp, MissingAttribute) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).WillOnce(DoAll(
      SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
          R"pb(notification {
                 timestamp: 1656026017779182564
                 prefix { origin: "openconfig" }
                 update {
                   path {
                     elem { name: "interfaces" }
                     elem {
                       name: "interface"
                       key { key: "name" value: "Ethernet1/4/1" }
                     }
                     elem { name: "state" }
                     elem { name: "counters" }
                     elem { name: "out-pkts" }
                   }
                   val {
                     json_ietf_val: "{\"openconfig-interfaces:out-pkts\":\"723563785\"}"
                   }
                 }
               })pb")),
      Return(grpc::Status::OK)));
  EXPECT_THAT(
      GetGnmiStatePathAndTimestamp(
          &stub, "interfaces/interface[name=\"Ethernet1/4/1\"]/state/counters",
          "openconfig-interfaces:in-pkts"),
      StatusIs(absl::StatusCode::kInternal));
}

TEST(GetGnmiStatePathAndTimestamp, EmptyNotification) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).WillOnce(DoAll(
      SetArgPointee<2>(
          gutil::ParseProtoOrDie<gnmi::GetResponse>(R"pb(notification {})pb")),
      Return(grpc::Status::OK)));
  EXPECT_THAT(
      GetGnmiStatePathAndTimestamp(
          &stub, "interfaces/interface[name=\"Ethernet1/4/1\"]/state/counters",
          "openconfig-interfaces:in-pkts"),
      StatusIs(absl::StatusCode::kInternal));
}

TEST(BreakoutModeMatchTest, LocalFileTestDataTest) {
  EXPECT_THAT(
      FindPortWithBreakoutMode(kBreakoutSample, {BreakoutSpeed::k400GB}),
      StatusIs(absl::StatusCode::kNotFound,
               HasSubstr("Couldn't find the breakout mode")));
  EXPECT_THAT(
      FindPortWithBreakoutMode(kBreakoutSample,
                               {BreakoutSpeed::k400GB, BreakoutSpeed::k400GB}),
      IsOkAndHolds(1));
  EXPECT_THAT(
      FindPortWithBreakoutMode(kBreakoutSample,
                               {BreakoutSpeed::k400GB, BreakoutSpeed::k400GB},
                               /*ignore_ports=*/{1}),
      StatusIs(absl::StatusCode::kNotFound,
               HasSubstr("Couldn't find the breakout mode")));
  EXPECT_THAT(
      FindPortWithBreakoutMode(kBreakoutSample,
                               {BreakoutSpeed::k200GB, BreakoutSpeed::k200GB,
                                BreakoutSpeed::k200GB, BreakoutSpeed::k200GB}),
      IsOkAndHolds(14));

  EXPECT_THAT(
      FindPortWithBreakoutMode(kBreakoutSample,
                               {BreakoutSpeed::k400GB, BreakoutSpeed::k200GB}),
      StatusIs(absl::StatusCode::kNotFound,
               HasSubstr("Couldn't find the breakout mode")));
  EXPECT_THAT(
      FindPortWithBreakoutMode(kBreakoutSample,
                               {BreakoutSpeed::k400GB, BreakoutSpeed::k200GB,
                                BreakoutSpeed::k200GB}),
      IsOkAndHolds(2));

  EXPECT_THAT(
      FindPortWithBreakoutMode(kBreakoutSample,
                               {BreakoutSpeed::k200GB, BreakoutSpeed::k200GB,
                                BreakoutSpeed::k400GB}),
      IsOkAndHolds(10));
}

TEST(SflowconfigTest, AppendSflowConfigSuccess) {
  const std::string kOpenConfig = R"({
    "openconfig-interfaces:interfaces":{
      "interface":[
        {
          "name":"bond0",
          "state":{"oper-status":"UP","openconfig-p4rt:id":1}
        }
      ]
    }
  })";
  const std::string kSflowConfig = R"({
    "openconfig-interfaces:interfaces":{
      "interface":[
        {
          "name":"bond0",
          "state":{"oper-status":"UP","openconfig-p4rt:id":1}
        }
      ]
    },
     "openconfig-sampling:sampling" : {
        "openconfig-sampling-sflow:sflow" : {
           "collectors" : {
              "collector" : [
                 {
                    "address" : "2001:4860:f802::be",
                    "config" : {
                       "address" : "2001:4860:f802::be",
                       "port" : 6343
                    },
                    "port" : 6343
                 }
              ]
           },
           "config" : {
              "agent-id-ipv6" : "8002:12::aab0",
              "enabled" : true,
              "polling-interval" : 0,
              "sample-size" : 128
           },
           "interfaces" : {
              "interface" : [
                 {
                    "config" : {
                       "enabled" : true,
                       "name" : "Ethernet1",
                       "ingress-sampling-rate" : 1000
                    },
                    "name" : "Ethernet1"
                 },
                 {
                    "config" : {
                       "enabled" : true,
                       "name" : "Ethernet2",
                       "ingress-sampling-rate" : 1000
                    },
                    "name" : "Ethernet2"
                 }
             ]
           }
        }
     }
  })";
  ASSERT_OK_AND_ASSIGN(
      auto json_str,
      AppendSflowConfigIfNotPresent(
          kOpenConfig,
          /*agent_addr_ipv6=*/"8002:12::aab0",
          /*collector_address_to_port=*/{{"2001:4860:f802::be", 6343}},
          /*sflow_enabled_interfaces=*/{"Ethernet1", "Ethernet2"},
          /*sampling_rate=*/1000,
          /*sampling_header_size=*/128));
  ASSERT_EQ(::nlohmann::json::parse(json_str),
            ::nlohmann::json::parse(kSflowConfig));
}

TEST(SflowconfigTest, AppendSflowConfigNoopIfPresent) {
  const std::string kGnmiConfig = R"({
    "openconfig-interfaces:interfaces":{
      "interface":[
        {
          "name":"bond0",
          "state":{"oper-status":"UP","openconfig-p4rt:id":1}
        }
      ]
    },
     "openconfig-sampling:sampling" : {
        "openconfig-sampling-sflow:sflow" : {
           "collectors" : {
              "collector" : [
                 {
                    "address" : "2001:4860:f802::be",
                    "config" : {
                       "address" : "2001:4860:f802::be",
                       "port" : 6343
                    },
                    "port" : 6343
                 }
              ]
           },
           "config" : {
              "agent-id-ipv6" : "8002:12::aab0",
              "enabled" : true,
              "polling-interval" : 0,
              "sample-size" : 128
           },
           "interfaces" : {
              "interface" : [
                 {
                    "config" : {
                       "enabled" : true,
                       "name" : "Ethernet1",
                       "ingress-sampling-rate" : 1000
                    },
                    "name" : "Ethernet1"
                 },
                 {
                    "config" : {
                       "enabled" : true,
                       "name" : "Ethernet2",
                       "ingress-sampling-rate" : 1000
                    },
                    "name" : "Ethernet2"
                 }
             ]
           }
        }
     }
  })";
  ASSERT_OK_AND_ASSIGN(
      auto json_str,
      AppendSflowConfigIfNotPresent(
          kGnmiConfig,
          /*agent_addr_ipv6=*/"8002:12::aab0",
          /*collector_address_to_port=*/{{"12:34:56::78", 6343}},
          /*sflow_enabled_interfaces=*/{"Ethernet3", "Ethernet4"},
          /*sampling_rate=*/100,
          /*sampling_header_size=*/12));
  ASSERT_EQ(::nlohmann::json::parse(json_str),
            ::nlohmann::json::parse(kGnmiConfig));
}

TEST(SflowconfigTest, AppendSflowConfigWrongParameterFail) {
  EXPECT_THAT(
      AppendSflowConfigIfNotPresent(
          /*gnmi_config=*/"",
          /*agent_addr_ipv6=*/"",
          /*collector_address_to_port=*/{{"2001:4860:f802::be", 6343}},
          /*sflow_enabled_interfaces=*/{"Ethernet1", "Ethernet2"},
          /*sampling_rate=*/1000,
          /*sampling_header_size=*/128),
      StatusIs(absl::StatusCode::kFailedPrecondition,
               HasSubstr("loopback_address parameter cannot be empty.")));
  EXPECT_THAT(
      AppendSflowConfigIfNotPresent(
          /*gnmi_config=*/"",
          /*agent_addr_ipv6=*/"8002:12::aab0",
          /*collector_address_to_port=*/{{"2001:4860:f802::be", 6343}},
          /*sflow_enabled_interfaces=*/{},
          /*sampling_rate=*/1000,
          /*sampling_header_size=*/128),
      StatusIs(
          absl::StatusCode::kFailedPrecondition,
          HasSubstr("sflow_enabled_interfaces parameter cannot be empty.")));
}

TEST(GetAllInterfaceCounters, Works) {
  static constexpr absl::string_view kInterfaceJson = R"(
{
   "openconfig-interfaces:interface":[
      {
         "name":"CPU",
         "state":{
            "counters":{
               "in-broadcast-pkts":"0",
               "in-discards":"134",
               "in-errors":"0",
               "in-fcs-errors":"0",
               "in-multicast-pkts":"0",
               "in-octets":"0",
               "in-pkts":"0",
               "in-unicast-pkts":"0",
               "in-unknown-protos":"0",
               "last-clear":"0",
               "out-broadcast-pkts":"0",
               "out-discards":"0",
               "out-errors":"0",
               "out-multicast-pkts":"0",
               "out-octets":"0",
               "out-pkts":"0",
               "out-unicast-pkts":"0"
            }
         },
         "subinterfaces":{
            "subinterface":[
               {
                  "index":0,
                  "openconfig-if-ip:ipv4":{
                     "state":{
                        "enabled":false
                     }
                  },
                  "openconfig-if-ip:ipv6":{
                     "state":{
                        "enabled":false
                     }
                  },
                  "state":{
                     "index":0
                  }
               }
            ]
         }
      },
      {
         "name":"Ethernet1/1/1",
         "openconfig-if-ethernet:ethernet":{
            "state":{
               "counters":{
                  "in-maxsize-exceeded":"1001"
               }
            }
         },
         "state":{
            "counters":{
               "carrier-transitions":"1",
               "google-pins-interfaces:in-buffer-discards":"1002",
               "in-broadcast-pkts":"1003",
               "in-discards":"132",
               "in-errors":"1004",
               "in-fcs-errors":"1005",
               "in-multicast-pkts":"132",
               "in-octets":"9828",
               "in-pkts":"132",
               "in-unicast-pkts":"1006",
               "in-unknown-protos":"0",
               "last-clear":"0",
               "out-broadcast-pkts":"1007",
               "out-discards":"1008",
               "out-errors":"1009",
               "out-multicast-pkts":"134",
               "out-octets":"9996",
               "out-pkts":"134",
               "out-unicast-pkts":"1010"
            }
         },
         "subinterfaces":{
            "subinterface":[
               {
                  "index":0,
                  "openconfig-if-ip:ipv4":{
                     "state":{
                        "counters":{
                           "in-pkts":"1011",
                           "out-pkts":"1012"
                        }
                     }
                  },
                  "openconfig-if-ip:ipv6":{
                     "state":{
                        "counters":{
                           "in-discarded-pkts":"1013",
                           "in-pkts":"1014",
                           "out-discarded-pkts":"1015",
                           "out-pkts":"1016"
                        }
                     }
                  }
               }
            ]
         }
      }
   ]
})";
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get(_,
                        EqualsProto(gutil::ParseProtoOrDie<gnmi::GetRequest>(
                            R"pb(prefix { origin: "openconfig" }
                                 path {
                                   elem { name: "interfaces" }
                                   elem { name: "interface" }
                                 }
                                 type: STATE)pb")),
                        _))
      .WillOnce(DoAll(
          SetArgPointee<2>(ConstructResponse(
              "elem { name: \"interfaces\" } elem { name: \"interface\" }",
              kInterfaceJson)),
          Return(grpc::Status::OK)));

  ASSERT_OK_AND_ASSIGN(auto interface_to_counters,
                       GetAllInterfaceCounters(stub));
  EXPECT_THAT(interface_to_counters, SizeIs(1));
  Counters counters = interface_to_counters["Ethernet1/1/1"];
  EXPECT_EQ(counters.in_pkts, 132);
  EXPECT_EQ(counters.out_pkts, 134);
  EXPECT_EQ(counters.in_octets, 9828);
  EXPECT_EQ(counters.out_octets, 9996);
  EXPECT_EQ(counters.in_unicast_pkts, 1006);
  EXPECT_EQ(counters.out_unicast_pkts, 1010);
  EXPECT_EQ(counters.in_multicast_pkts, 132);
  EXPECT_EQ(counters.out_multicast_pkts, 134);
  EXPECT_EQ(counters.in_broadcast_pkts, 1003);
  EXPECT_EQ(counters.out_broadcast_pkts, 1007);
  EXPECT_EQ(counters.in_errors, 1004);
  EXPECT_EQ(counters.out_errors, 1009);
  EXPECT_EQ(counters.in_discards, 132);
  EXPECT_EQ(counters.out_discards, 1008);
  EXPECT_EQ(counters.in_buffer_discards, 1002);
  EXPECT_EQ(counters.in_maxsize_exceeded, 1001);
  EXPECT_EQ(counters.in_fcs_errors, 1005);
  EXPECT_EQ(counters.in_ipv4_pkts, 1011);
  EXPECT_EQ(counters.out_ipv4_pkts, 1012);
  EXPECT_EQ(counters.in_ipv6_pkts, 1014);
  EXPECT_EQ(counters.out_ipv6_pkts, 1016);
  EXPECT_EQ(counters.in_ipv6_discarded_pkts, 1013);
  EXPECT_EQ(counters.out_ipv6_discarded_pkts, 1015);
  EXPECT_EQ(counters.timestamp_ns, 1620348032128305716);
}

}  // namespace
}  // namespace pins_test
