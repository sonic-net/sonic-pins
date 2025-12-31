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

#include <cstdint>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "absl/container/btree_map.h"
#include "absl/container/btree_set.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/escaping.h"
#include "absl/strings/match.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "gmock/gmock.h"
#include "google/protobuf/text_format.h"
#include "grpcpp/support/status.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
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
using ::testing::Pair;
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

grpc::Status GrpcUnknownError(absl::string_view message) {
  return grpc::Status(grpc::StatusCode::UNKNOWN, std::string(message));
}

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
  std::string path_textproto;
  google::protobuf::TextFormat::PrintToString(ConvertOCStringToPath(oc_path),
                                              &path_textproto);
  std::string response = absl::Substitute(
      R"pb(notification {
             timestamp: 1620348032128305716
             prefix { origin: "openconfig" target: "chassis" }
             update {
               path { $0 }
               val { json_ietf_val: "$1" }
             }
           })pb",
      path_textproto, absl::CEscape(gnmi_config));
  return gutil::ParseProtoOrDie<gnmi::GetResponse>(response);
}

TEST(GetAlarms, FailedRPCReturnsError) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "system" }
                                elem { name: "alarms" }
                              }
                              type: STATE
                              encoding: JSON_IETF)pb"),
          _))
      .WillOnce(Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  EXPECT_THAT(GetAlarms(stub), StatusIs(absl::StatusCode::kDeadlineExceeded));
}

TEST(GetAlarms, InvalidResponsesFail) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub,
              Get(_,
                  EqualsProto(
                      R"pb(prefix { origin: "openconfig" target: "chassis" }
                           path {
                             elem { name: "system" }
                             elem { name: "alarms" }
                           }
                           type: STATE
                           encoding: JSON_IETF)pb"),
                  _))
      // More than one notification.
      .WillOnce(
          DoAll(SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
                    R"pb(notification {
                           timestamp: 1619721040593669829
                           prefix { origin: "openconfig" target: "chassis" }
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
                           prefix { origin: "openconfig" target: "chassis" }
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
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "system" }
                                elem { name: "alarms" }
                              }
                              type: STATE
                              encoding: JSON_IETF)pb"),
          _))
      .WillOnce(
          DoAll(SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
                    R"pb(notification {
                           timestamp: 1619721040593669829
                           prefix { origin: "openconfig" target: "chassis" }
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
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "system" }
                                elem { name: "alarms" }
                              }
                              type: STATE
                              encoding: JSON_IETF)pb"),
          _))
      .WillOnce(DoAll(
          SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
              R"pb(notification {
                     timestamp: 1619721040593669829
                     prefix { origin: "openconfig" target: "chassis" }
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
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "system" }
                                elem { name: "alarms" }
                              }
                              type: STATE
                              encoding: JSON_IETF)pb"),
          _))
      .WillOnce(DoAll(
          SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
              R"pb(notification {
                     timestamp: 1619721040593669829
                     prefix { origin: "openconfig" target: "chassis" }
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
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "system" }
                                elem { name: "alarms" }
                              }
                              type: STATE
                              encoding: JSON_IETF)pb"),
          _))
      .WillOnce(DoAll(
          SetArgPointee<
              2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(absl::Substitute(
              R"pb(notification {
                     timestamp: 1619721040593669829
                     prefix { origin: "openconfig" target: "chassis" }
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
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "system" }
                                elem { name: "processes" }
                              }
                              type: STATE
                              encoding: JSON_IETF)pb"),
          _))
      .WillOnce(Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  EXPECT_THAT(GetAllSystemProcesses(stub),
              StatusIs(absl::StatusCode::kDeadlineExceeded));
}

TEST(GetSystemMemory, FailedRPCReturnsError) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "system" }
                                elem { name: "memory" }
                              }
                              type: STATE
                              encoding: JSON_IETF)pb"),
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
                 prefix { origin: "openconfig" target: "chassis" }
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
                 prefix { origin: "openconfig" target: "chassis" }
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
                 prefix { origin: "openconfig" target: "chassis" }
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
                 prefix { origin: "openconfig" target: "chassis" }
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
                 prefix { origin: "openconfig" target: "chassis" }
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
                 prefix { origin: "openconfig" target: "chassis" }
                 update {
                   path { elem { name: "interfaces" } }
                   val {
                     json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"CPU\"},{\"name\":\"Ethernet0\",\"state\":{\"oper-status\":\"DOWN\"}}]}}"
                   }
                 }
               })pb")),
      Return(grpc::Status::OK)));

  const absl::flat_hash_map<std::string, std::string> expected_map = {
      {"Ethernet0", "DOWN"}};

  ASSERT_THAT(GetInterfaceToOperStatusMapOverGnmi(stub, absl::Seconds(60)),
              IsOkAndHolds(UnorderedPointwise(Eq(), expected_map)));
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

TEST(SetInterfaceP4rtIds, FailsOnNonExistentInterfaceNames) {
  gnmi::MockgNMIStub stub;
  auto interfaces_to_attempt_to_set =
      gutil::ParseProtoOrDie<openconfig::Interfaces>(
          R"pb(interfaces {
                 name: "Ethernet0"
                 config { enabled: true p4rt_id: 1 }
               }
               interfaces {
                 name: "ThisIsNotARealInterface"
                 config { enabled: false p4rt_id: 2 }
               }
          )pb");

  // We expect a config where one P4RT id needs to be deleted since Ethernet0
  // remains the same.
  std::string switch_config =
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
        ]
      }
    })json";
  EXPECT_CALL(stub, Get).WillOnce(DoAll(SetArgPointee<2>(ConstructResponse(
                                            /*oc_path=*/"interfaces",
                                            /*gnmi_config=*/switch_config)),
                                        Return(grpc::Status::OK)));

  EXPECT_THAT(SetInterfaceP4rtIds(stub, interfaces_to_attempt_to_set),
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
          "state":
            {
              "oper-status":"UP",
              "openconfig-p4rt:id":1,
              "management":true
            }
        },
        {
          "name":"Ethernet1/1/1",
          "state":
            {
              "oper-status":"UP",
              "openconfig-p4rt:id":2,
              "type":"ethernetCsmacd"
            }
        },
        {
          "name":"Ethernet1/2/1",
          "state":
            {
              "oper-status":"DOWN",
              "openconfig-p4rt:id":3,
              "type":"ethernetCsmacd"
            }
        },
        {
          "name":"Ethernet1/3/1",
          "state":{"oper-status":"UP","type":"ethernetCsmacd"}
        },
        {
          "name":"Ethernet1/4/1",
          "state":
            {
              "oper-status":"UP",
              "openconfig-p4rt:id":4,
              "type":"ethernetCsmacd"
            }
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

TEST(GetUpInterfacePortIDs, ReturnsSingletonsByDefault) {
  std::string interface_state = R"json({
    "openconfig-interfaces:interfaces":{
      "interface":[
        {
          "name":"loopback0",
          "state":
            {
              "oper-status":"UP",
              "openconfig-p4rt:id":1,
              "type":"softwareLoopback"
            }
        },
        {
          "name":"Ethernet1/1/1",
          "state":
            {
              "oper-status":"UP",
              "openconfig-p4rt:id":2,
              "type":"ethernetCsmacd"
            }
        },
        {
          "name":"PortChannel3",
          "state":
            {
              "oper-status":"UP",
              "openconfig-p4rt:id":3,
              "type":"ieee8023adLag"
            }
        },
        {
          "name":"Ethernet1/4/1",
          "state":
            {
              "oper-status":"UP",
              "openconfig-p4rt:id":4,
              "type":"ethernetCsmacd"
            }
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
          "state":
            {
              "oper-status":"UP",
              "openconfig-p4rt:id":1,
              "management":true
            }
        },
        {
          "name":"Ethernet1/1/1",
          "state":
            {
              "oper-status":"UP",
              "openconfig-p4rt:id":2,
              "type":"ethernetCsmacd"
            }
        },
        {
          "name":"Ethernet1/2/1",
          "state":
            {
              "oper-status":"DOWN",
              "openconfig-p4rt:id":3,
              "type":"ethernetCsmacd"
            }
        },
        {
          "name":"Ethernet1/3/1",
          "state":{"oper-status":"UP","type":"ethernetCsmacd"}
        },
        {
          "name":"Ethernet1/4/1",
          "state":
            {
              "oper-status":"UP",
              "openconfig-p4rt:id":4,
              "type":"ethernetCsmacd"
            }
        },
        {
          "name":"Ethernet1/5/1",
          "state":
            {
              "oper-status":"UP",
              "openconfig-p4rt:id":5,
              "type":"ethernetCsmacd"
            }
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
          "state":
            {
              "oper-status":"UP",
              "openconfig-p4rt:id":1,
              "management":true
            }
        },
        {
          "name":"Ethernet1/1/1",
          "state":
            {
              "oper-status":"UP",
              "openconfig-p4rt:id":2,
              "type":"ethernetCsmacd"
            }
        },
        {
          "name":"Ethernet1/2/1",
          "state":
            {
              "oper-status":"DOWN",
              "openconfig-p4rt:id":3,
              "type":"ethernetCsmacd"
            }
        },
        {
          "name":"Ethernet1/3/1",
          "state":
            {
              "oper-status":"UP",
              "type":"ethernetCsmacd"
            }
        },
        {
          "name":"Ethernet1/4/1",
          "state":
            {
              "oper-status":"UP",
              "openconfig-p4rt:id":4,
              "type":"ethernetCsmacd"
            }
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
          "state":
            {
              "oper-status":"UP",
              "openconfig-p4rt:id":1,
              "management":true
            }
        },
        {
          "name":"Ethernet1/1/1",
          "state":
            {
              "oper-status":"UP",
              "openconfig-p4rt:id":2,
              "type":"ethernetCsmacd"
            }
        },
        {
          "name":"Ethernet1/2/1",
          "state":
            {
              "oper-status":"DOWN",
              "openconfig-p4rt:id":3,
              "type":"ethernetCsmacd"
            }
        },
        {
          "name":"Ethernet1/3/1",
          "state":{"oper-status":"UP","type":"ethernetCsmacd"}
        },
        {
          "name":"Ethernet1/4/1",
          "state":
            {
              "oper-status":"UP",
              "openconfig-p4rt:id":4,
              "type":"ethernetCsmacd"
            }
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
          "state":
            {
              "oper-status":"UP",
              "openconfig-p4rt:id":1,
              "management":true
            }
        },
        {
          "name":"Ethernet1/1/1",
          "state":{"oper-status":"UP","type":"ethernetCsmacd"}
        },
        {
          "name":"Ethernet1/2/1",
          "state":
            {
              "oper-status":"DOWN",
              "openconfig-p4rt:id":3,
              "type":"ethernetCsmacd"
            }
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

TEST(GetEthernetInterfacePortIDs, CanGetNEthernetInterfaces) {
  std::string interface_state = R"json({
    "openconfig-interfaces:interfaces":{
      "interface":[
        {
          "name":"bond0",
          "state":
            {
              "oper-status":"UP",
              "openconfig-p4rt:id":1,
              "management":true
            }
        },
        {
          "name":"Ethernet1/1/1",
          "state":
            {
              "oper-status":"UP",
              "openconfig-p4rt:id":2,
              "type":"ethernetCsmacd"
            }
        },
        {
          "name":"Ethernet1/2/1",
          "state":
            {
              "oper-status":"DOWN",
              "openconfig-p4rt:id":3,
              "type":"ethernetCsmacd"
            }
        },
        {
          "name":"Ethernet1/3/1",
          "state":{"oper-status":"UP","type":"ethernetCsmacd"}
        },
        {
          "name":"PortChannel1234",
          "state":
            {
              "oper-status":"UP",
              "openconfig-p4rt:id":1234,
              "type":"ieee8023adLag"
            }
        },
        {
          "name":"Ethernet1/4/1",
          "state":
            {
              "oper-status":"UP",
              "openconfig-p4rt:id":4,
              "type":"ethernetCsmacd"
            }
        },
        {
          "name":"Ethernet1/5/1",
          "state":
            {
              "oper-status":"UP",
              "openconfig-p4rt:id":5,
              "type":"ethernetCsmacd"
            }
        }
      ]
    }
  })json";

  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).Times(1).WillRepeatedly(
      DoAll(SetArgPointee<2>(ConstructResponse(
                /*oc_path=*/"interfaces",
                /*gnmi_config=*/interface_state)),
            Return(grpc::Status::OK)));

  // There are 3 valid ports, but we only choose 2. So we expect the result to
  // be a subset of the valid ports.
  EXPECT_THAT(GetNEthernetInterfacePortIds(stub, 2),
              IsOkAndHolds(IsSubsetOf({"2", "3", "4", "5"})));
}

TEST(GetEthernetInterfacePortIDs,
     GetNFailsWhenNotEnoughEthernetInterfacesAreAvailableWithAPortId) {
  std::string interface_state = R"json({
    "openconfig-interfaces:interfaces":{
      "interface":[
        {
          "name":"bond0",
          "state":
            {
              "oper-status":"UP",
              "openconfig-p4rt:id":1,
              "management":true
            }
        },
        {
          "name":"Ethernet1/1/1",
          "state":
            {
              "oper-status":"UP",
              "openconfig-p4rt:id":2,
              "type":"ethernetCsmacd"
            }
        },
        {
          "name":"Ethernet1/2/1",
          "state":
            {
              "oper-status":"DOWN",
              "openconfig-p4rt:id":3,
              "type":"ethernetCsmacd"
            }
        },
        {
          "name":"Ethernet1/3/1",
          "state":
            {
              "oper-status":"UP",
              "type":"ethernetCsmacd"
            }
        },
        {
          "name":"PortChannel1234",
          "state":
            {
              "oper-status":"UP",
              "openconfig-p4rt:id":1234,
              "type":"ieee8023adLag"
            }
        },
        {
          "name":"Ethernet1/4/1",
          "state":
            {
              "oper-status":"UP",
              "openconfig-p4rt:id":4,
              "type":"ethernetCsmacd"
            }
        }
      ]
    }
  })json";

  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).Times(1).WillRepeatedly(
      DoAll(SetArgPointee<2>(ConstructResponse(
                /*oc_path=*/"interfaces",
                /*gnmi_config=*/interface_state)),
            Return(grpc::Status::OK)));

  EXPECT_THAT(GetNEthernetInterfacePortIds(stub, 5),
              StatusIs(absl::StatusCode::kFailedPrecondition));
}

TEST(GetInterfaceNamesForGivenPortId, StubSuccessfullyReturnsInterfaceNames) {
  gnmi::GetResponse response;
  *response.add_notification()
       ->add_update()
       ->mutable_val()
       ->mutable_json_ietf_val() = R"(
    {
      "openconfig-interfaces:interfaces": {
        "interface": [
          {
            "name": "Ethernet1/1/1"
          },
          {
            "name": "Ethernet1/2/1"
          },
          {
            "name": "Ethernet1/1/2"
          },
          {
            "name": "Ethernet1/14/2"
          },
          {
            "name": "Ethernet1/10/2"
          }
        ]
      }
    })";
  gnmi::MockgNMIStub mock_stub;
  EXPECT_CALL(mock_stub, Get)
      .WillRepeatedly(
          DoAll(SetArgPointee<2>(response), Return(grpc::Status::OK)));

  ASSERT_OK_AND_ASSIGN(
      std::vector<std::string> interface_names_for_given_port_number,
      GetInterfaceNamesForGivenPortNumber(mock_stub, "1"));
  const std::vector<std::string> expected_interface_names = {"Ethernet1/1/1",
                                                             "Ethernet1/1/2"};
  EXPECT_THAT(interface_names_for_given_port_number,
              UnorderedPointwise(Eq(), expected_interface_names));
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
                 prefix { origin: "openconfig" target: "chassis" }
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
                 prefix { origin: "openconfig" target: "chassis" }
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
                 prefix { origin: "openconfig" target: "chassis" }
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
                 prefix { origin: "openconfig" target: "chassis" }
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
                 prefix { origin: "openconfig" target: "chassis" }
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

TEST(GetConfigDisabledInterfaces, RpcFails) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).WillOnce(
      Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  EXPECT_THAT(GetConfigDisabledInterfaces(stub),
              StatusIs(absl::StatusCode::kDeadlineExceeded));
}

TEST(GetConfigDisabledInterfaces, RpcSucceeds) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).WillOnce(DoAll(
      SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
          R"pb(notification {
                 prefix { origin: "openconfig" target: "chassis" }
                 update {
                   path { elem { name: "interfaces" } }
                   val {
                     json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"config\":{\"name\":\"CPU\",\"openconfig-p4rt:id\":4294967293,\"type\":\"iana-if-type:ethernetCsmacd\"},\"name\":\"CPU\",\"subinterfaces\":{\"subinterface\":[{\"config\":{\"index\":0},\"index\":0,\"openconfig-if-ip:ipv4\":{\"config\":{\"enabled\":false}},\"openconfig-if-ip:ipv6\":{\"config\":{\"enabled\":false}}}]}},{\"config\":{\"description\":\"ju1u1m2.sqs11.net.google.com:Ethernet1/1/1 [(not a trunk member)]\",\"enabled\":true,\"pins-interfaces:ecmp-hash-algorithm\":\"CRC_32LO\",\"pins-interfaces:ecmp-hash-offset\":\"8\",\"pins-interfaces:fully-qualified-interface-name\":\"ju1u1m1.sqs11.net.google.com:Ethernet1/1/1\",\"mtu\":9216,\"name\":\"Ethernet1/1/1\",\"openconfig-p4rt:id\":1,\"openconfig-pins-interfaces:health-indicator\":\"GOOD\",\"type\":\"iana-if-type:ethernetCsmacd\"},\"hold-time\":{\"config\":{\"down\":0,\"up\":8000}},\"name\":\"Ethernet1/1/1\",\"openconfig-if-ethernet:ethernet\":{\"config\":{\"fec-mode\":\"openconfig-if-ethernet:FEC_RS544_2X_INTERLEAVE\",\"port-speed\":\"openconfig-if-ethernet:SPEED_400GB\"}},\"subinterfaces\":{\"subinterface\":[{\"config\":{\"enabled\":true,\"index\":0},\"index\":0,\"openconfig-if-ip:ipv4\":{\"config\":{\"enabled\":false}},\"openconfig-if-ip:ipv6\":{\"config\":{\"enabled\":false},\"unnumbered\":{\"config\":{\"enabled\":true}}}}]}}]}}"
                   }
                 }
               })pb")),
      Return(grpc::Status::OK)));
  EXPECT_THAT(GetConfigDisabledInterfaces(stub),
              IsOkAndHolds(UnorderedElementsAre("CPU")));
}

TEST(GetConfigEnabledInterfaces, RpcFails) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).WillOnce(
      Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  EXPECT_THAT(GetConfigEnabledInterfaces(stub),
              StatusIs(absl::StatusCode::kDeadlineExceeded));
}

TEST(GetConfigEnabledInterfaces, RpcSucceeds) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).WillOnce(DoAll(
      SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
          R"pb(notification {
                 prefix { origin: "openconfig" target: "chassis" }
                 update {
                   path { elem { name: "interfaces" } }
                   val {
                     json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"config\":{\"name\":\"CPU\",\"openconfig-p4rt:id\":4294967293,\"type\":\"iana-if-type:ethernetCsmacd\"},\"name\":\"CPU\",\"subinterfaces\":{\"subinterface\":[{\"config\":{\"index\":0},\"index\":0,\"openconfig-if-ip:ipv4\":{\"config\":{\"enabled\":false}},\"openconfig-if-ip:ipv6\":{\"config\":{\"enabled\":false}}}]}},{\"config\":{\"description\":\"ju1u1m2.sqs11.net.google.com:Ethernet1/1/1 [(not a trunk member)]\",\"enabled\":true,\"pins-interfaces:ecmp-hash-algorithm\":\"CRC_32LO\",\"pins-interfaces:ecmp-hash-offset\":\"8\",\"pins-interfaces:fully-qualified-interface-name\":\"ju1u1m1.sqs11.net.google.com:Ethernet1/1/1\",\"mtu\":9216,\"name\":\"Ethernet1/1/1\",\"openconfig-p4rt:id\":1,\"openconfig-pins-interfaces:health-indicator\":\"GOOD\",\"type\":\"iana-if-type:ethernetCsmacd\"},\"hold-time\":{\"config\":{\"down\":0,\"up\":8000}},\"name\":\"Ethernet1/1/1\",\"openconfig-if-ethernet:ethernet\":{\"config\":{\"fec-mode\":\"openconfig-if-ethernet:FEC_RS544_2X_INTERLEAVE\",\"port-speed\":\"openconfig-if-ethernet:SPEED_400GB\"}},\"subinterfaces\":{\"subinterface\":[{\"config\":{\"enabled\":true,\"index\":0},\"index\":0,\"openconfig-if-ip:ipv4\":{\"config\":{\"enabled\":false}},\"openconfig-if-ip:ipv6\":{\"config\":{\"enabled\":false},\"unnumbered\":{\"config\":{\"enabled\":true}}}}]}}]}}"
                   }
                 }
               })pb")),
      Return(grpc::Status::OK)));
  EXPECT_THAT(GetConfigEnabledInterfaces(stub),
              IsOkAndHolds(UnorderedElementsAre("Ethernet1/1/1")));
}

TEST(GetInterfaceOperStatusOverGnmi, RpcFails) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(type: STATE
                              prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "interfaces" }
                                elem {
                                  name: "interface"
                                  key { key: "name" value: "Ethernet0" }
                                }
                                elem { name: "state" }
                                elem { name: "oper-status" }
                              }
                              encoding: JSON_IETF
          )pb"),
          _))
      .WillOnce(Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  EXPECT_THAT(GetInterfaceOperStatusOverGnmi(stub, "Ethernet0"),
              StatusIs(absl::StatusCode::kDeadlineExceeded));
}

TEST(GetInterfaceOperStatusOverGnmi, InvalidResponse) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(type: STATE
                              prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "interfaces" }
                                elem {
                                  name: "interface"
                                  key { key: "name" value: "Ethernet0" }
                                }
                                elem { name: "state" }
                                elem { name: "oper-status" }
                              }
                              encoding: JSON_IETF
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
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(type: STATE
                              prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "interfaces" }
                                elem {
                                  name: "interface"
                                  key { key: "name" value: "Ethernet0" }
                                }
                                elem { name: "state" }
                                elem { name: "oper-status" }
                              }
                              encoding: JSON_IETF
          )pb"),
          _))
      .WillOnce(DoAll(
          SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
              R"pb(notification {
                     timestamp: 1620348032128305716
                     prefix { origin: "openconfig" target: "chassis" }
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
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(type: STATE
                              prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "interfaces" }
                                elem {
                                  name: "interface"
                                  key { key: "name" value: "Ethernet0" }
                                }
                                elem { name: "state" }
                                elem { name: "oper-status" }
                              }
                              encoding: JSON_IETF
          )pb"),
          _))
      .WillOnce(DoAll(
          SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
              R"pb(notification {
                     timestamp: 1620348032128305716
                     prefix { origin: "openconfig" target: "chassis" }
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

TEST(GetInterfaceOperStatusOverGnmi, OperStatusNotPresent) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(type: STATE
                              prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "interfaces" }
                                elem {
                                  name: "interface"
                                  key { key: "name" value: "Ethernet0" }
                                }
                                elem { name: "state" }
                                elem { name: "oper-status" }
                              }
                              encoding: JSON_IETF
          )pb"),
          _))
      .WillOnce(DoAll(
          SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
              R"pb(notification {
                     timestamp: 1620348032128305716
                     prefix { origin: "openconfig" target: "chassis" }
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
                         json_ietf_val: "{\"openconfig-interfaces:oper-status\":{\"oper-status\":\"NOT_PRESENT\"}}"
                       }
                     }
                   })pb")),
          Return(grpc::Status::OK)));
  EXPECT_THAT(GetInterfaceOperStatusOverGnmi(stub, "Ethernet0"),
              IsOkAndHolds(OperStatus::kNotPresent));
}

TEST(GetInterfaceOperStatusOverGnmi, OperStatusTesting) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(type: STATE
                              prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "interfaces" }
                                elem {
                                  name: "interface"
                                  key { key: "name" value: "Ethernet0" }
                                }
                                elem { name: "state" }
                                elem { name: "oper-status" }
                              }
                              encoding: JSON_IETF
          )pb"),
          _))
      .WillOnce(DoAll(
          SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
              R"pb(notification {
                     timestamp: 1620348032128305716
                     prefix { origin: "openconfig" target: "chassis" }
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

TEST(GetInterfaceAdminStatusOverGnmi, RpcFails) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(type: STATE
                              prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "interfaces" }
                                elem {
                                  name: "interface"
                                  key { key: "name" value: "Ethernet0" }
                                }
                                elem { name: "state" }
                                elem { name: "admin-status" }
                              }
                              encoding: JSON_IETF
          )pb"),
          _))
      .WillOnce(Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  EXPECT_THAT(GetInterfaceAdminStatusOverGnmi(stub, "Ethernet0"),
              StatusIs(absl::StatusCode::kDeadlineExceeded));
}

TEST(GetInterfaceAdminStatusOverGnmi, InvalidResponse) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(type: STATE
                              prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "interfaces" }
                                elem {
                                  name: "interface"
                                  key { key: "name" value: "Ethernet0" }
                                }
                                elem { name: "state" }
                                elem { name: "admin-status" }
                              }
                              encoding: JSON_IETF
          )pb"),
          _))
      .WillOnce(
          DoAll(SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
                    R"pb(notification {})pb")),
                Return(grpc::Status::OK)));
  EXPECT_THAT(GetInterfaceAdminStatusOverGnmi(stub, "Ethernet0"),
              StatusIs(absl::StatusCode::kInternal));
}

TEST(GetInterfaceAdminStatusOverGnmi, AdminStatusUp) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(type: STATE
                              prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "interfaces" }
                                elem {
                                  name: "interface"
                                  key { key: "name" value: "Ethernet0" }
                                }
                                elem { name: "state" }
                                elem { name: "admin-status" }
                              }
                              encoding: JSON_IETF
          )pb"),
          _))
      .WillOnce(DoAll(
          SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
              R"pb(notification {
                     timestamp: 1620348032128305716
                     prefix { origin: "openconfig" target: "chassis" }
                     update {
                       path {
                         elem { name: "interfaces" }
                         elem {
                           name: "interface"
                           key { key: "name" value: "Ethernet0" }
                         }
                         elem { name: "state" }
                         elem { name: "admin-status" }
                       }
                       val {
                         json_ietf_val: "{\"openconfig-interfaces:admin-status\":{\"admin-status\":\"UP\"}}"
                       }
                     }
                   })pb")),
          Return(grpc::Status::OK)));
  EXPECT_THAT(GetInterfaceAdminStatusOverGnmi(stub, "Ethernet0"),
              IsOkAndHolds(AdminStatus::kUp));
}

TEST(GetInterfaceAdminStatusOverGnmi, AdminStatusDown) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(type: STATE
                              prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "interfaces" }
                                elem {
                                  name: "interface"
                                  key { key: "name" value: "Ethernet0" }
                                }
                                elem { name: "state" }
                                elem { name: "admin-status" }
                              }
                              encoding: JSON_IETF
          )pb"),
          _))
      .WillOnce(DoAll(
          SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
              R"pb(notification {
                     timestamp: 1620348032128305716
                     prefix { origin: "openconfig" target: "chassis" }
                     update {
                       path {
                         elem { name: "interfaces" }
                         elem {
                           name: "interface"
                           key { key: "name" value: "Ethernet0" }
                         }
                         elem { name: "state" }
                         elem { name: "admin-status" }
                       }
                       val {
                         json_ietf_val: "{\"openconfig-interfaces:admin-status\":{\"admin-status\":\"DOWN\"}}"
                       }
                     }
                   })pb")),
          Return(grpc::Status::OK)));
  EXPECT_THAT(GetInterfaceAdminStatusOverGnmi(stub, "Ethernet0"),
              IsOkAndHolds(AdminStatus::kDown));
}

TEST(GetInterfaceAdminStatusOverGnmi, AdminStatusTesting) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(type: STATE
                              prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "interfaces" }
                                elem {
                                  name: "interface"
                                  key { key: "name" value: "Ethernet0" }
                                }
                                elem { name: "state" }
                                elem { name: "admin-status" }
                              }
                              encoding: JSON_IETF
          )pb"),
          _))
      .WillOnce(DoAll(
          SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
              R"pb(notification {
                     timestamp: 1620348032128305716
                     prefix { origin: "openconfig" target: "chassis" }
                     update {
                       path {
                         elem { name: "interfaces" }
                         elem {
                           name: "interface"
                           key { key: "name" value: "Ethernet0" }
                         }
                         elem { name: "state" }
                         elem { name: "admin-status" }
                       }
                       val {
                         json_ietf_val: "{\"openconfig-interfaces:admin-status\":{\"admin-status\":\"TESTING\"}}"
                       }
                     }
                   })pb")),
          Return(grpc::Status::OK)));
  EXPECT_THAT(GetInterfaceAdminStatusOverGnmi(stub, "Ethernet0"),
              IsOkAndHolds(AdminStatus::kTesting));
}

TEST(GetInterfaceAdminStatusOverGnmi, AdminStatusUnknown) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(type: STATE
                              prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "interfaces" }
                                elem {
                                  name: "interface"
                                  key { key: "name" value: "Ethernet0" }
                                }
                                elem { name: "state" }
                                elem { name: "admin-status" }
                              }
                              encoding: JSON_IETF
          )pb"),
          _))
      .WillOnce(DoAll(
          SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
              R"pb(notification {
                     timestamp: 1620348032128305716
                     prefix { origin: "openconfig" target: "chassis" }
                     update {
                       path {
                         elem { name: "interfaces" }
                         elem {
                           name: "interface"
                           key { key: "name" value: "Ethernet0" }
                         }
                         elem { name: "state" }
                         elem { name: "admin-status" }
                       }
                       val {
                         json_ietf_val: "{\"openconfig-interfaces:admin-status\":{\"admin-status\":\"UNKNOWN\"}}"
                       }
                     }
                   })pb")),
          Return(grpc::Status::OK)));
  EXPECT_THAT(GetInterfaceAdminStatusOverGnmi(stub, "Ethernet0"),
              IsOkAndHolds(AdminStatus::kUnknown));
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
                 prefix { origin: "openconfig" target: "chassis" }
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
                 prefix { origin: "openconfig" target: "chassis" }
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
                 prefix { origin: "openconfig" target: "chassis" }
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
                 prefix { origin: "openconfig" target: "chassis" }
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
                 prefix { origin: "openconfig" target: "chassis" }
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
                 prefix { origin: "openconfig" target: "chassis" }
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
                 prefix { origin: "openconfig" target: "chassis" }
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
                 prefix { origin: "openconfig" target: "chassis" }
                 update {
                   path { elem { name: "interfaces" } }
                   val {
                     json_ietf_val: "{\"openconfig-interfaces:interfaces\":{\"interface\":[{\"name\":\"bond0\",\"state\":{\"oper-status\":\"UP\"}},{\"name\":\"Ethernet0\",\"state\":{\"oper-status\":\"UP\",\"openconfig-p4rt:id\":1}}]}}"
                   }
                 }
               })pb")),
      Return(grpc::Status::OK)));

  EXPECT_THAT(GetUpInterfacesOverGnmi(stub),
              IsOkAndHolds(ContainerEq(std::vector<std::string>{"Ethernet0"})));
}

TEST(GetUpInterfaces, FiltersInterfacesByType) {
  std::string interface_state = R"json({
    "openconfig-interfaces:interfaces":{
      "interface":[
        {
          "name":"loopback0",
          "state":
            {
              "oper-status":"UP",
              "openconfig-p4rt:id":1,
              "type":"softwareLoopback",
            }
        },
        {
          "name":"Ethernet1/1/1",
          "state":
            {
              "oper-status":"UP",
              "openconfig-p4rt:id":2,
              "type":"ethernetCsmacd"
            }
        },
        {
          "name":"Ethernet1/2/1",
          "state":
            {
              "oper-status":"UP",
              "openconfig-p4rt:id":3,
              "type":"ethernetCsmacd"
            }
        },
        {
          "name":"PortChannel1234",
          "state":
            {
              "oper-status":"UP",
              "openconfig-p4rt:id":1234,
              "type":"ieee8023adLag"
            }
        },
        {
          "name":"PortChannel1235",
          "state":
            {
              "oper-status":"UP",
              "openconfig-p4rt:id":1235,
              "type":"ieee8023adLag"
            }
        }
      ]
    }
  })json";

  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).WillRepeatedly(
      DoAll(SetArgPointee<2>(ConstructResponse(
                /*oc_path=*/"interfaces",
                /*gnmi_config=*/interface_state)),
            Return(grpc::Status::OK)));

  EXPECT_THAT(GetUpInterfacesOverGnmi(stub, InterfaceType::kLoopback),
              IsOkAndHolds(UnorderedElementsAre("loopback0")));
  EXPECT_THAT(
      GetUpInterfacesOverGnmi(stub, InterfaceType::kSingleton),
      IsOkAndHolds(UnorderedElementsAre("Ethernet1/1/1", "Ethernet1/2/1")));
  EXPECT_THAT(
      GetUpInterfacesOverGnmi(stub, InterfaceType::kLag),
      IsOkAndHolds(UnorderedElementsAre("PortChannel1234", "PortChannel1235")));
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
  constexpr char kOperstatusBad[] =
      R"({"openconfig-interfaces:status":"TESTING"})";
  gnmi::Notification *notification = response.add_notification();
  gnmi::Update *update = notification->add_update();
  *update->mutable_path() =
      ConvertOCStringToPath("interfaces/interface[name=Ethernet8]/state");
  update->mutable_val()->set_json_ietf_val(kOperstatusBad);
  LOG(INFO) << "response: " << response.DebugString();
  EXPECT_THAT(
      ParseGnmiGetResponse(response, "openconfig-interfaces:oper-status"),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr("not present in JSON response")));
}
TEST(CheckParseGnmiGetResponse, FailDuetoMissingTagWithTwoNotifications) {
  gnmi::GetResponse response;
  constexpr char kOperstatusBad[] =
      R"({"openconfig-interfaces:status":"TESTING"})";
  gnmi::Update *update = response.add_notification()->add_update();
  *update->mutable_path() =
      ConvertOCStringToPath("interfaces/interface[name=Ethernet8]/state");
  update->mutable_val()->set_json_ietf_val(kOperstatusBad);

  constexpr char kOperstatusGood[] =
      R"({"openconfig-interfaces:oper-status":"UP"})";
  update = response.add_notification()->add_update();
  *update->mutable_path() =
      ConvertOCStringToPath("interfaces/interface[name=Ethernet7]/state");
  update->mutable_val()->set_json_ietf_val(kOperstatusGood);

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

TEST(CheckParseGnmiGetResponse, FailDueToMultipleSamePaths) {
  gnmi::GetResponse response;
  constexpr char kOperstatus[] =
      R"({"openconfig-interfaces:oper-status":"UP"})";
  for (int i = 0; i < 2; i++) {
    gnmi::Notification *notification = response.add_notification();
    gnmi::Update *update = notification->add_update();
    *update->mutable_path() = ConvertOCStringToPath(
        "interfaces/interface[name=Ethernet8]/state/oper-status");
    update->mutable_val()->set_json_val(kOperstatus);
  }

  LOG(INFO) << "response: " << response.DebugString();
  EXPECT_THAT(
      ParseGnmiGetResponse(response, "openconfig-interfaces:oper-status"),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr("openconfig-interfaces:oper-status")));
}

TEST(CheckParseGnmiGetResponse, CombineMultipleDifferentResponses) {
  gnmi::GetResponse response;
  response.add_notification()->add_update()->mutable_val()->set_json_val(
      R"({
        "openconfig-platform:components": {
          "component": [
            {"integrated-circuit":
              {"config":
                {"openconfig-p4rt:node-id":"123456"}
              },
              "name":"integrated_circuit0"
            }
          ]
        }
      })");
  response.add_notification()->add_update()->mutable_val()->set_json_ietf_val(
      R"({
        "openconfig-interfaces:interfaces":{
          "interface":[
            {"name":"CPU"},
            {"name":"Ethernet0",
             "state": {"oper-status":"DOWN"}
            }
          ]
        }
      })");

  LOG(INFO) << "response: " << response.DebugString();
  EXPECT_THAT(ParseGnmiGetResponse(response, /*match_tag=*/"", /*indent=*/2),
              IsOkAndHolds(AllOf(HasSubstr("openconfig-interfaces:interfaces"),
                                 HasSubstr("openconfig-platform:components"))));
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

TEST(GetTransceiverQualifiedForInterface, StubSuccessfullyReturnsTrue) {
  gnmi::MockgNMIStub mock_stub;
  EXPECT_CALL(
      mock_stub,
      Get(_, EqualsProto(R"pb(type: STATE
                              prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "interfaces" }
                                elem {
                                  name: "interface"
                                  key { key: "name" value: "Ethernet1" }
                                }
                                elem { name: "ethernet" }
                                elem { name: "state" }
                                elem { name: "transceiver-qualified" }
                              }
                              encoding: JSON_IETF
          )pb"),
          _))
      .WillOnce(DoAll(
          SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
              R"pb(notification {
                     timestamp: 1620348032128305716
                     prefix { origin: "openconfig" target: "chassis" }
                     update {
                       path {
                         elem { name: "interfaces" }
                         elem {
                           name: "interface"
                           key { key: "name" value: "Ethernet1" }
                         }
                         elem { name: "state" }
                         elem { name: "transceiver-qualified" }
                       }
                       val {
                         json_ietf_val: "{\"google-pins-interfaces:transceiver-qualified\":true}"
                       }
                     }
                   })pb")),
          Return(grpc::Status::OK)));
  EXPECT_THAT(GetTransceiverQualifiedForInterface(mock_stub, "Ethernet1"),
              IsOkAndHolds(true));
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

TEST(LoopbackMode, WorksProperly) {
  gnmi::GetResponse response;
  *response.add_notification()
       ->add_update()
       ->mutable_val()
       ->mutable_json_ietf_val() = R"(
    {
      "openconfig-interfaces:interfaces": {
        "interface": [
          {
            "name":"EthernetEnabled0",
            "state":{
              "loopback-mode":"ASIC_MAC_LOCAL",
              "openconfig-p4rt:id": 2
            }
          },
          {
            "name":"EthernetEnabled1",
            "state":{
              "loopback-mode":"NOT_ASIC_MAC_LOCAL",
              "openconfig-p4rt:id": 4
            }
          },
          {
            "name":"EthernetEnabled2",
            "state":{
              "loopback-mode":"ASIC_MAC_LOCAL",
              "openconfig-p4rt:id": 5
            }
          },
          {
            "name":"EthernetEnabled3",
            "state":{
              "loopback-mode":"NONE",
              "openconfig-p4rt:id": 6
            }
          },
          {
            "name":"EthernetEnabled4",
            "state":{
              "openconfig-p4rt:id": 7
            }
          }
        ]
      }
    })";

  gnmi::MockgNMIStub mock_stub;
  EXPECT_CALL(mock_stub, Get)
      .WillRepeatedly(
          DoAll(SetArgPointee<2>(response), Return(grpc::Status::OK)));
  absl::btree_set<std::string> expected_set{"2", "5"};
  LOG(INFO) << "loopback_mode: ";
  EXPECT_THAT(GetP4rtIdOfInterfacesInAsicMacLocalLoopbackMode(mock_stub),
              IsOkAndHolds(UnorderedPointwise(Eq(), expected_set)));
}

TEST(GetModuleIsPopulatedForInterface, StubSuccessfullyReturnsTrue) {
  gnmi::MockgNMIStub mock_stub;
  EXPECT_CALL(
      mock_stub,
      Get(_, EqualsProto(R"pb(type: STATE
                              prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "components" }
                                elem {
                                  name: "component"
                                  key { key: "name" value: "1/1" }
                                }
                                elem { name: "state" }
                                elem { name: "empty" }
                              }
                              encoding: JSON_IETF
          )pb"),
          _))
      .WillOnce(DoAll(
          SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
              R"pb(notification {
                     timestamp: 1620348032128305716
                     prefix { origin: "openconfig" target: "chassis" }
                     update {
                       path {
                         elem { name: "components" }
                         elem {
                           name: "component"
                           key { key: "name" value: "1/1" }
                         }
                         elem { name: "state" }
                         elem { name: "empty" }
                       }
                       val {
                         json_ietf_val: "{\"openconfig-platform:empty\":false}"
                       }
                     }
                   })pb")),
          Return(grpc::Status::OK)));
  EXPECT_THAT(GetModuleIsPopulatedForInterface(mock_stub, "1/1"),
              IsOkAndHolds(true));
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

TEST(TransceiverPartInformation, MissingVendorName) {
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
      {"Ethernet1", TransceiverPart{.vendor = "",
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

TEST(InterfaceSupportsBert, WorksProperly) {
  constexpr int k10G = 10'000'000;
  constexpr int k25G = 25'000'000;
  constexpr int k50G = 50'000'000;
  constexpr int k100G = 100'000'000;

  const absl::flat_hash_map<std::string, int> kInterfaceToLaneSpeed = {
      {"Ethernet1/1/1", k50G},  {"Ethernet1/2/1", k25G},
      {"Ethernet1/3/1", k100G}, {"Ethernet1/4/1", k25G},
      {"Ethernet1/5/1", k50G},  {"Ethernet1/33", k10G},
      {"Ethernet1/34", k10G}};

  // BERT is supported cases.
  EXPECT_TRUE(InterfaceSupportsBert("Ethernet1/2/1", kInterfaceToLaneSpeed));
  EXPECT_TRUE(InterfaceSupportsBert("Ethernet1/4/1", kInterfaceToLaneSpeed));

  // BERT is not supported cases.
  EXPECT_FALSE(InterfaceSupportsBert("Ethernet1/1/1", kInterfaceToLaneSpeed));
  EXPECT_FALSE(InterfaceSupportsBert("Ethernet1/3/1", kInterfaceToLaneSpeed));
  EXPECT_FALSE(InterfaceSupportsBert("Ethernet1/5/1", kInterfaceToLaneSpeed));
  EXPECT_FALSE(InterfaceSupportsBert("Ethernet1/33", kInterfaceToLaneSpeed));
  EXPECT_FALSE(InterfaceSupportsBert("Ethernet1/34", kInterfaceToLaneSpeed));

  // Interface not found in interface to lane speed map.
  EXPECT_FALSE(InterfaceSupportsBert("Ethernet1/7/1", kInterfaceToLaneSpeed));
}

TEST(GetGnmiStateDeviceId, DeviceIdSuccess) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).WillOnce(DoAll(
      SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
          R"pb(notification {
                 timestamp: 1656026017779182564
                 prefix { origin: "openconfig" target: "chassis" }
                 update {
                   path {
                     elem { name: "components" }
                     elem {
                       name: "component"
                       key { key: "name" value: "integrated_circuit0" }
                     }
                     elem { name: "integrated-circuit" }
                     elem { name: "state" }
                     elem { name: "node-id" }
                   }
                   val {
                     json_ietf_val: "{\"openconfig-p4rt:node-id\":\"2795437045\"}"
                   }
                 }
               })pb")),
      Return(grpc::Status::OK)));
  ASSERT_OK(
      BuildGnmiGetRequest("components/component[name=integrated_circuit0]/"
                          "integrated-circuit/state/node-id",
                          gnmi::GetRequest::STATE));
  ASSERT_OK_AND_ASSIGN(auto device_id, GetDeviceId(stub));
  EXPECT_EQ(device_id, 2795437045);
}

TEST(GetGnmiStateDeviceId, DeviceIdFailTagNotFound) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).WillOnce(
      DoAll(SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
                R"pb(notification {
                       timestamp: 1656026017779182564
                       prefix { origin: "openconfig" target: "chassis" }
                       update {
                         path {
                           elem { name: "components" }
                           elem {
                             name: "component"
                             key { key: "name" value: "chassis" }
                           }
                           elem { name: "chassis" }
                           elem { name: "state" }
                           elem { name: "model-name" }
                         }
                         val { json_ietf_val: "{\"model\":\"BX\"}" }
                       }
                     })pb")),
            Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(
      auto result,
      BuildGnmiGetRequest("components/component[name=integrated_circuit0]/"
                          "integrated-circuit/state/node-id",
                          gnmi::GetRequest::STATE));
  EXPECT_THAT(
      GetDeviceId(stub),
      StatusIs(
          absl::StatusCode::kInternal,
          HasSubstr("openconfig-p4rt:node-id not present in JSON response")));
}

TEST(GetGnmiStatePathAndTimestamp, VerifyValue) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Get).WillOnce(DoAll(
      SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
          R"pb(notification {
                 timestamp: 1656026017779182564
                 prefix { origin: "openconfig" target: "chassis" }
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
                 prefix { origin: "openconfig" target: "chassis" }
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

TEST(InterfacesNameTest, LocalFileTestDataTest) {
  std::string interface_state = R"json({
    "openconfig-interfaces:interfaces":{
      "interface":[
        {
          "name":"Ethernet1/3/1"
        },
        {
          "name":"Ethernet1/5/1"
        },
        {
          "name":"Ethernet1/5/3"
        },
        {
          "name_missing":"NotInterfaceName"
        }
      ]
    }
  })json";
  EXPECT_THAT(GetInterfacesOnPort(interface_state, 1), IsOkAndHolds(IsEmpty()));
  EXPECT_THAT(GetInterfacesOnPort(interface_state, 3),
              IsOkAndHolds(ElementsAre("Ethernet1/3/1")));
  EXPECT_THAT(
      GetInterfacesOnPort(interface_state, 5),
      IsOkAndHolds(UnorderedElementsAre("Ethernet1/5/1", "Ethernet1/5/3")));
}

TEST(GetCongestionQueueCounters, Works) {
  static constexpr absl::string_view kInterfaceJson = R"(
{
    "openconfig-qos:interface": [
        {
            "interface-id": "CPU"
        },
        {
            "interface-id": "Ethernet1/1/1",
            "output": {
                "queues": {
                    "queue": [
                        {
                            "name": "AF3",
                            "state": {
                                "pins-qos:diag": {
                                    "dropped-packet-events": "1"
                                }
                            }
                        },
                        {
                            "name": "AF4",
                            "state": {
                                "pins-qos:diag": {
                                    "dropped-packet-events": "2"
                                }
                            }
                        }
                    ]
                }
            }
        },
        {
            "interface-id": "Ethernet1/1/3",
            "output": {
                "queues": {
                    "queue": [
                        {
                            "name": "AF3",
                            "state": {
                                "pins-qos:diag": {
                                    "dropped-packet-events": "3"
                                }
                            }
                        },
                        {
                            "name": "AF4",
                            "state": {
                                "pins-qos:diag": {
                                    "dropped-packet-events": "4"
                                }
                            }
                        }
                    ]
                }
            }
        }
    ]
})";
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "qos" }
                                elem { name: "interfaces" }
                                elem { name: "interface" }
                              }
                              type: STATE
                              encoding: JSON_IETF)pb"),
          _))
      .WillOnce(DoAll(SetArgPointee<2>(ConstructResponse(
                          "openconfig-qos:interface", kInterfaceJson)),
                      Return(grpc::Status::OK)));

  ASSERT_OK_AND_ASSIGN(auto congestion_counters,
                       GetCongestionQueueCounters(stub));
  EXPECT_THAT(congestion_counters, SizeIs(2));
  EXPECT_THAT(congestion_counters["Ethernet1/1/1"],
              UnorderedElementsAre(Pair("AF3", 1), Pair("AF4", 2)));
  EXPECT_THAT(congestion_counters["Ethernet1/1/3"],
              UnorderedElementsAre(Pair("AF3", 3), Pair("AF4", 4)));
}

TEST(GetCongestionQueueCounters, WorksEvenWhenNoDroppedPacketEvents) {
  // "pins-qos:diag" is present in interface/output/queues/queue but has
  // no "dropped-packet-events".
  static constexpr absl::string_view kInterfaceJson = R"(
{
    "openconfig-qos:interface": [
        {
            "interface-id": "Ethernet1/1/1",
            "output": {
                "queues": {
                    "queue": [
                        {
                            "name": "AF3",
                            "state": {
                                "pins-qos:diag": {
                                }
                            }
                        }
                    ]
                }
            }
        }
    ]
})";
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "qos" }
                                elem { name: "interfaces" }
                                elem { name: "interface" }
                              }
                              type: STATE
                              encoding: JSON_IETF)pb"),
          _))
      .WillOnce(DoAll(SetArgPointee<2>(ConstructResponse(
                          "openconfig-qos:interface", kInterfaceJson)),
                      Return(grpc::Status::OK)));

  // GetCongestionQueueCounters completes successfully but returns an empty map.
  ASSERT_OK_AND_ASSIGN(auto congestion_counters,
                       GetCongestionQueueCounters(stub));
  EXPECT_THAT(congestion_counters, SizeIs(0));
}

TEST(GetCongestionQueueCounters, WorksEvenWhenNoDiagField) {
  // "pins-qos:diag" is missing in interface/output/queues/queue.
  static constexpr absl::string_view kInterfaceJson = R"(
{
    "openconfig-qos:interface": [
        {
            "interface-id": "Ethernet1/1/1",
            "output": {
                "queues": {
                    "queue": [
                        {
                            "name": "AF3",
                            "state": {
                            }
                        }
                    ]
                }
            }
        }
    ]
})";
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "qos" }
                                elem { name: "interfaces" }
                                elem { name: "interface" }
                              }
                              type: STATE
                              encoding: JSON_IETF)pb"),
          _))
      .WillOnce(DoAll(SetArgPointee<2>(ConstructResponse(
                          "openconfig-qos:interface", kInterfaceJson)),
                      Return(grpc::Status::OK)));

  // GetCongestionQueueCounters completes successfully but returns an empty map.
  ASSERT_OK_AND_ASSIGN(auto congestion_counters,
                       GetCongestionQueueCounters(stub));
  EXPECT_THAT(congestion_counters, SizeIs(0));
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
               "pins-interfaces:in-buffer-discards":"1002",
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
            },
            "pins-interfaces:blackhole":{
               "in-discard-events":"1",
               "out-discard-events":"2",
               "in-error-events":"3",
               "fec-not-correctable-events":"4"
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
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "interfaces" }
                                elem { name: "interface" }
                              }
                              type: STATE
                              encoding: JSON_IETF)pb"),
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
  EXPECT_EQ(counters.carrier_transitions, 1);

  // Check the blackhole counters.
  EXPECT_TRUE(counters.blackhole_counters.has_value());
  EXPECT_EQ(counters.blackhole_counters->in_discard_events, 1);
  EXPECT_EQ(counters.blackhole_counters->out_discard_events, 2);
  EXPECT_EQ(counters.blackhole_counters->in_error_events, 3);
  EXPECT_EQ(counters.blackhole_counters->fec_not_correctable_events, 4);
}

TEST(GetAllInterfaceCounters, WorksEvenWhenMissingBlackholeField) {
  // "blackhole" is missing under interface/state.
  static constexpr absl::string_view kInterfaceJson = R"(
{
   "openconfig-interfaces:interface":[
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
               "pins-interfaces:in-buffer-discards":"1002",
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
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "interfaces" }
                                elem { name: "interface" }
                              }
                              type: STATE
                              encoding: JSON_IETF)pb"),
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

  // Since all blackhole counters were not present, the blackhole counters
  // optional is not set.
  EXPECT_FALSE(counters.blackhole_counters.has_value());
}

TEST(GetAllInterfaceCounters, WorksEvenWhenMissingBlackholeCounters) {
  // All counters under "blackhole" are missing.
  static constexpr absl::string_view kInterfaceJson = R"(
{
   "openconfig-interfaces:interface":[
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
               "pins-interfaces:in-buffer-discards":"1002",
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
            },
            "pins-interfaces:blackhole":{
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
  EXPECT_CALL(stub,
              Get(_,
                  EqualsProto(
                      R"pb(prefix { origin: "openconfig" target: "chassis" }
                           path {
                             elem { name: "interfaces" }
                             elem { name: "interface" }
                           }
                           type: STATE
                           encoding: JSON_IETF)pb"),
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

  // Since blackhole counters were not present, the blackhole counters optional
  // is not set.
  EXPECT_FALSE(counters.blackhole_counters.has_value());
}

class GetAllInterfaceCountersWithParams
    : public ::testing::Test,
      public ::testing::WithParamInterface<std::string> {
 public:
  static void SetUpTestSuite() {};
  static void TearDownTestSuite() {};
};

INSTANTIATE_TEST_SUITE_P(GetAllInterfaceCountersWithParamsSuite,
                         GetAllInterfaceCountersWithParams,
                         ::testing::Values(
                             R"("out-discard-events": "2",
           "in-error-events": "3",
           "fec-not-correctable-events": "4")",
                             R"("in-discard-events": "1",
           "in-error-events": "3",
           "fec-not-correctable-events": "4")",
                             R"("in-discard-events": "1",
           "out-discard-events": "2",
           "fec-not-correctable-events": "4")",
                             R"("in-discard-events": "1",
           "out-discard-events": "2",
           "in-error-events": "3")"));

TEST_P(GetAllInterfaceCountersWithParams,
       WorksEvenWhenMissingSomeBlackholeCounters) {
  // All counters under "blackhole" are missing.
  static constexpr absl::string_view kInterfaceJson = R"(
{
   "openconfig-interfaces:interface":[
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
               "pins-interfaces:in-buffer-discards":"1002",
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
            },
            "pins-interfaces:blackhole":{
                $0
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
  std::string param = GetParam();

  EXPECT_CALL(stub,
              Get(_,
                  EqualsProto(
                      R"pb(prefix { origin: "openconfig" target: "chassis" }
                           path {
                             elem { name: "interfaces" }
                             elem { name: "interface" }
                           }
                           type: STATE
                           encoding: JSON_IETF)pb"),
                  _))
      .WillOnce(DoAll(
          SetArgPointee<2>(ConstructResponse(
              "elem { name: \"interfaces\" } elem { name: \"interface\" }",
              absl::Substitute(kInterfaceJson, param))),
          Return(grpc::Status::OK)));

  ASSERT_OK_AND_ASSIGN(auto interface_to_counters,
                       GetAllInterfaceCounters(stub));
  EXPECT_THAT(interface_to_counters, SizeIs(1));
  Counters counters = interface_to_counters["Ethernet1/1/1"];

  // Since blackhole counters were not present, the blackhole counters optional
  // is not set.
  EXPECT_FALSE(counters.blackhole_counters.has_value());
}

TEST(GetAllInterfaceCounters, WorksWithoutOptionalValues) {
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
               "pins-interfaces:in-buffer-discards":"1002",
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
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "interfaces" }
                                elem { name: "interface" }
                              }
                              type: STATE
                              encoding: JSON_IETF)pb"),
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
  EXPECT_EQ(counters.carrier_transitions, std::nullopt);
}

TEST(GetAllInterfaceCounters, FailedWithMissingFieldAndReportsInterface) {
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
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "interfaces" }
                                elem { name: "interface" }
                              }
                              type: STATE
                              encoding: JSON_IETF)pb"),
          _))
      .WillOnce(DoAll(
          SetArgPointee<2>(ConstructResponse(
              "elem { name: \"interfaces\" } elem { name: \"interface\" }",
              kInterfaceJson)),
          Return(grpc::Status::OK)));
  EXPECT_THAT(
      GetAllInterfaceCounters(stub),
      StatusIs(
          absl::StatusCode::kNotFound,
          AllOf(
              HasSubstr("Ethernet1/1/1"),
              HasSubstr(
                  "pins-interfaces:in-buffer-discards not found in"))));
}

TEST(GetBadIntervalsCounter, Success) {
  static constexpr absl::string_view kGnmiConfigWithBadIntervals = R"json(
{
  "pins-interfaces:blackhole": {
    "bad-intervals": "1"
  }
})json";
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub,
      Get(_,
          EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                           path {
                             elem { name: "interfaces" }
                             elem {
                               name: "interface"
                               key { key: "name" value: "Ethernet1/4/1" }
                             }
                             elem { name: "state" }
                             elem { name: "pins-interfaces:blackhole" }
                           }
                           type: STATE
                           encoding: JSON_IETF)pb"),
          _))
      .WillOnce(DoAll(SetArgPointee<2>(ConstructResponse(
                          /*oc_path=*/"pins-interfaces:blackhole",
                          /*gnmi_config=*/kGnmiConfigWithBadIntervals)),
                      Return(grpc::Status::OK)));
  EXPECT_THAT(GetBadIntervalsCounter("Ethernet1/4/1", stub), IsOkAndHolds(1));
}

TEST(GetBadIntervalsCounter, FailWithMissingField) {
  // No bad-intervals field.
  static constexpr absl::string_view kGnmiConfigWithoutBadIntervals = R"json(
{
  "pins-interfaces:blackhole": {
  }
})json";
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub,
      Get(_,
          EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                           path {
                             elem { name: "interfaces" }
                             elem {
                               name: "interface"
                               key { key: "name" value: "Ethernet1/4/1" }
                             }
                             elem { name: "state" }
                             elem { name: "pins-interfaces:blackhole" }
                           }
                           type: STATE
                           encoding: JSON_IETF)pb"),
          _))
      .WillOnce(DoAll(SetArgPointee<2>(ConstructResponse(
                          /*oc_path=*/"pins-interfaces:blackhole",
                          /*gnmi_config=*/kGnmiConfigWithoutBadIntervals)),
                      Return(grpc::Status::OK)));
  EXPECT_THAT(GetBadIntervalsCounter("Ethernet1/4/1", stub),
              StatusIs(absl::StatusCode::kNotFound,
                       HasSubstr("bad-intervals not found in")));
}


TEST(GetBlackholePortCounters, Success) {
  static constexpr absl::string_view kCountersJson = R"json(
{
  "pins-interfaces:blackhole": {
    "fec-not-correctable-events": "1",
    "in-discard-events": "2",
    "in-error-events": "3",
    "out-discard-events": "4"
  }
})json";
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub,
      Get(_,
          EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                           path {
                             elem { name: "interfaces" }
                             elem {
                               name: "interface"
                               key { key: "name" value: "Ethernet1/4/1" }
                             }
                             elem { name: "state" }
                             elem { name: "pins-interfaces:blackhole" }
                           }
                           type: STATE
                           encoding: JSON_IETF)pb"),
          _))
      .WillOnce(DoAll(SetArgPointee<2>(ConstructResponse(
                          /*oc_path=*/"pins-interfaces:blackhole",
                          /*gnmi_config=*/kCountersJson)),
                      Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(BlackholePortCounters counters,
                       GetBlackholePortCounters("Ethernet1/4/1", stub));
  EXPECT_EQ(counters.fec_not_correctable_events, 1);
  EXPECT_EQ(counters.in_discard_events, 2);
  EXPECT_EQ(counters.in_error_events, 3);
  EXPECT_EQ(counters.out_discard_events, 4);
}

TEST(GetBlackholePortCounters, FailWithMissingField) {
  static constexpr absl::string_view kCountersJson = R"json(
{
  "pins-interfaces:blackhole": {
    "fec-not-correctable-events": "1",
    "in-discard-events": "2",
    "in-error-events": "3"
  }
})json";
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub,
      Get(_,
          EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                           path {
                             elem { name: "interfaces" }
                             elem {
                               name: "interface"
                               key { key: "name" value: "Ethernet1/4/1" }
                             }
                             elem { name: "state" }
                             elem { name: "pins-interfaces:blackhole" }
                           }
                           type: STATE
                           encoding: JSON_IETF)pb"),
          _))
      .WillOnce(DoAll(SetArgPointee<2>(ConstructResponse(
                          /*oc_path=*/"pins-interfaces:blackhole",
                          /*gnmi_config=*/kCountersJson)),
                      Return(grpc::Status::OK)));
  EXPECT_THAT(GetBlackholePortCounters("Ethernet1/4/1", stub),
              StatusIs(absl::StatusCode::kNotFound,
                       HasSubstr("out-discard-events not found in")));
}

TEST(GetBlackholeSwitchCounters, Success) {
  static constexpr absl::string_view kCountersJson = R"json(
{
  "openconfig-platform:state": {
    "pins-platform:blackhole": {
      "blackhole-events": "1",
      "fec-not-correctable-events": "2",
      "in-discard-events": "3",
      "in-error-events": "4",
      "lpm-miss-events": "5",
      "memory-error-events": "6",
      "out-discard-events": "7"
    },
    "pins-platform:congestion": {
      "congestion-events": "0"
    },
    "openconfig-p4rt:node-id": "2795043031"
  }
})json";
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub,
      Get(_,
          EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                           path {
                             elem { name: "components" }
                             elem {
                               name: "component"
                               key { key: "name" value: "integrated_circuit0" }
                             }
                             elem { name: "integrated-circuit" }
                             elem { name: "state" }
                           }
                           type: STATE
                           encoding: JSON_IETF)pb"),
          _))
      .WillOnce(DoAll(SetArgPointee<2>(ConstructResponse(
                          /*oc_path=*/"openconfig-platform:state",
                          /*gnmi_config=*/kCountersJson)),
                      Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(BlackholeSwitchCounters counters,
                       GetBlackholeSwitchCounters(stub));
  EXPECT_EQ(counters.blackhole_events, 1);
  EXPECT_EQ(counters.fec_not_correctable_events, 2);
  EXPECT_EQ(counters.in_discard_events, 3);
  EXPECT_EQ(counters.in_error_events, 4);
  EXPECT_EQ(counters.lpm_miss_events, 5);
  EXPECT_EQ(counters.memory_error_events, 6);
  EXPECT_EQ(counters.out_discard_events, 7);
}

TEST(GetBlackholeSwitchCounters, FailWithMissingField) {
  static constexpr absl::string_view kCountersJson = R"json(
{
  "openconfig-platform:state": {
    "pins-platform:blackhole": {
      "blackhole-events": "1",
      "fec-not-correctable-events": "2",
      "in-discard-events": "3",
      "in-error-events": "4",
      "lpm-miss-events": "5",
      "memory-error-events": "6"
    },
    "pins-platform:congestion": {
      "congestion-events": "0"
    },
    "openconfig-p4rt:node-id": "2795043031"
  }
})json";
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub,
      Get(_,
          EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                           path {
                             elem { name: "components" }
                             elem {
                               name: "component"
                               key { key: "name" value: "integrated_circuit0" }
                             }
                             elem { name: "integrated-circuit" }
                             elem { name: "state" }
                           }
                           type: STATE
                           encoding: JSON_IETF)pb"),
          _))
      .WillOnce(DoAll(SetArgPointee<2>(ConstructResponse(
                          /*oc_path=*/"openconfig-platform:state",
                          /*gnmi_config=*/kCountersJson)),
                      Return(grpc::Status::OK)));
  EXPECT_THAT(GetBlackholeSwitchCounters(stub),
              StatusIs(absl::StatusCode::kNotFound,
                       HasSubstr("out-discard-events not found in")));
}

TEST(GetCongestionQueueCounter, Success) {
  static constexpr absl::string_view kQueueStateJson = R"json(
{
  "openconfig-qos:state": {
    "dropped-pkts": "208223",
    "pins-qos:diag": {
      "dropped-packet-events": "1"
    },
    "pins-qos:max-periodic-queue-len": "0",
    "max-queue-len": "27552650",
    "name": "NC1",
    "openconfig-qos-ext:dropped-octets": "315249622",
    "openconfig-qos-ext:traffic-type": "UC",
    "openconfig-qos-ext:watermark": "27552650",
    "queue-management-profile": "staggered_queue",
    "transmit-octets": "4339189102",
    "transmit-pkts": "2866043"
  }
})json";
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub, Get(_,
                EqualsProto(
                    R"pb(prefix { origin: "openconfig" target: "chassis" }
                         path {
                           elem { name: "qos" }
                           elem { name: "interfaces" }
                           elem {
                             name: "interface"
                             key { key: "interface-id" value: "Ethernet1/4/1" }
                           }
                           elem { name: "output" }
                           elem { name: "queues" }
                           elem {
                             name: "queue"
                             key { key: "name" value: "NC1" }
                           }
                           elem { name: "state" }
                         }
                         type: STATE
                         encoding: JSON_IETF)pb"),
                _))
      .WillOnce(DoAll(SetArgPointee<2>(ConstructResponse(
                          /*oc_path=*/"openconfig-qos:state",
                          /*gnmi_config=*/kQueueStateJson)),
                      Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(uint64_t queue_dropped_packet_events,
                       GetCongestionQueueCounter("Ethernet1/4/1", "NC1", stub));
  EXPECT_EQ(queue_dropped_packet_events, 1);
}

TEST(GetCongestionSwitchCounter, Success) {
  static constexpr absl::string_view kCountersJson = R"json(
{
  "openconfig-platform:state": {
    "pins-platform:blackhole": {
      "blackhole-events": "1",
      "fec-not-correctable-events": "2",
      "in-discard-events": "3",
      "in-error-events": "4",
      "lpm-miss-events": "5",
      "memory-error-events": "6",
      "out-discard-events": "7"
    },
    "pins-platform:congestion": {
      "congestion-events": "8"
    },
    "openconfig-p4rt:node-id": "2795043031"
  }
})json";
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub,
      Get(_,
          EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                           path {
                             elem { name: "components" }
                             elem {
                               name: "component"
                               key { key: "name" value: "integrated_circuit0" }
                             }
                             elem { name: "integrated-circuit" }
                             elem { name: "state" }
                           }
                           type: STATE
                           encoding: JSON_IETF)pb"),
          _))
      .WillOnce(DoAll(SetArgPointee<2>(ConstructResponse(
                          /*oc_path=*/"openconfig-platform:state",
                          /*gnmi_config=*/kCountersJson)),
                      Return(grpc::Status::OK)));
  ASSERT_OK_AND_ASSIGN(uint64_t congestion_switch_counter,
                       GetCongestionSwitchCounter(stub));
  EXPECT_EQ(congestion_switch_counter, 8);
}

TEST(GetGnmiStateLeafValue, ReturnsStateValue) {
  gnmi::MockgNMIStub stub;
  gnmi::GetResponse response;
  response.add_notification()->add_update()->mutable_val()->set_json_ietf_val(
      R"json({"boot-time":"12345678"})json");
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "system" }
                                elem { name: "state" }
                                elem { name: "boot-time" }
                              }
                              type: STATE
                              encoding: JSON_IETF)pb"),
          _))
      .WillOnce(DoAll(SetArgPointee<2>(response), Return(grpc::Status::OK)));
  EXPECT_THAT(GetGnmiStateLeafValue(&stub, "system/state/boot-time"),
              IsOkAndHolds("12345678"));
}

TEST(GetGnmiStateLeafValue, ReturnsErrorForMalformedStateValue) {
  gnmi::MockgNMIStub stub;
  gnmi::GetResponse response;
  response.add_notification()->add_update()->mutable_val()->set_json_ietf_val(
      R"json({\"boot-time":"12345678"})json");
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "system" }
                                elem { name: "state" }
                                elem { name: "boot-time" }
                              }
                              type: STATE
                              encoding: JSON_IETF)pb"),
          _))
      .WillOnce(DoAll(SetArgPointee<2>(response), Return(grpc::Status::OK)));
  EXPECT_THAT(GetGnmiStateLeafValue(&stub, "system/state/boot-time"),
              Not(IsOk()));
}

TEST(GetGnmiStateLeafValue, ReturnsErrorForGetRpcFailure) {
  gnmi::MockgNMIStub stub;
  gnmi::GetResponse response;
  response.add_notification()->add_update()->mutable_val()->set_json_ietf_val(
      R"json({\"boot-time":"12345678"})json");
  EXPECT_CALL(stub, Get).WillOnce(Return(GrpcUnknownError("")));
  EXPECT_THAT(GetGnmiStateLeafValue(&stub, "system/state/boot-time"),
              Not(IsOk()));
}

TEST(UpdateGnmiConfigLeaf, SendsGnmiUpdate) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub, Set(_,
                EqualsProto(
                    R"pb(prefix { origin: "openconfig" target: "chassis" }
                         update {
                           path {
                             elem { name: "system" }
                             elem { name: "config" }
                             elem { name: "boot-time" }
                           }
                           val { json_ietf_val: "{\"boot-time\":\"12345678\"}" }
                         })pb"),
                _))
      .WillOnce(Return(grpc::Status::OK));
  EXPECT_OK(UpdateGnmiConfigLeaf(&stub, "system/config/boot-time", "12345678"));
}

TEST(UpdateGnmiConfigLeaf, ReturnsErrorForNonConfigPath) {
  gnmi::MockgNMIStub stub;
  EXPECT_THAT(UpdateGnmiConfigLeaf(&stub, "system/state/boot-time", "12345678"),
              Not(IsOk()));
}

TEST(UpdateGnmiConfigLeaf, ReturnsErrorForSetRpcFailure) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Set).WillOnce(Return(GrpcUnknownError("")));
  EXPECT_THAT(
      UpdateGnmiConfigLeaf(&stub, "system/config/boot-time", "12345678"),
      Not(IsOk()));
}

TEST(UpdateAndVerifyGnmiConfigLeaf, UpdatesAndVerifiesConfigLeaf) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub, Set(_,
                EqualsProto(
                    R"pb(prefix { origin: "openconfig" target: "chassis" }
                         update {
                           path {
                             elem { name: "system" }
                             elem { name: "config" }
                             elem { name: "boot-time" }
                           }
                           val { json_ietf_val: "{\"boot-time\":\"12345678\"}" }
                         })pb"),
                _))
      .WillOnce(Return(grpc::Status::OK));
  gnmi::GetResponse response;
  response.add_notification()->add_update()->mutable_val()->set_json_ietf_val(
      R"json({"boot-time":"12345678"})json");
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "system" }
                                elem { name: "state" }
                                elem { name: "boot-time" }
                              }
                              type: STATE
                              encoding: JSON_IETF)pb"),
          _))
      .WillOnce(DoAll(SetArgPointee<2>(response), Return(grpc::Status::OK)));
  EXPECT_OK(UpdateAndVerifyGnmiConfigLeaf(&stub, "system/config/boot-time",
                                          "12345678"));
}

TEST(UpdateAndVerifyGnmiConfigLeaf, WaitsForStatePathConvergence) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Set).WillOnce(Return(grpc::Status::OK));
  gnmi::GetResponse response, bad_response;
  response.add_notification()->add_update()->mutable_val()->set_json_ietf_val(
      R"json({"boot-time":"12345678"})json");
  bad_response.add_notification()
      ->add_update()
      ->mutable_val()
      ->set_json_ietf_val(R"json({"boot-time":"12"})json");
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "system" }
                                elem { name: "state" }
                                elem { name: "boot-time" }
                              }
                              type: STATE
                              encoding: JSON_IETF)pb"),
          _))
      .WillOnce(Return(GrpcUnknownError("")))
      .WillOnce(DoAll(SetArgPointee<2>(bad_response), Return(grpc::Status::OK)))
      .WillOnce(DoAll(SetArgPointee<2>(response), Return(grpc::Status::OK)));
  EXPECT_OK(UpdateAndVerifyGnmiConfigLeaf(&stub, "system/config/boot-time",
                                          "12345678"));
}

TEST(UpdateAndVerifyGnmiConfigLeaf, ReturnsErrorWhenStatePathDoesNotConverge) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Set).WillOnce(Return(grpc::Status::OK));
  EXPECT_CALL(stub, Get).WillRepeatedly(Return(grpc::Status::OK));
  EXPECT_THAT(UpdateAndVerifyGnmiConfigLeaf(&stub, "system/config/boot-time",
                                            "12345678", absl::ZeroDuration()),
              Not(IsOk()));
}

TEST(UpdateAndVerifyGnmiConfigLeaf, ReturnsErrorForNonConfigPath) {
  gnmi::MockgNMIStub stub;
  EXPECT_THAT(UpdateAndVerifyGnmiConfigLeaf(&stub, "system/state/boot-time",
                                            "12345678"),
              Not(IsOk()));
}

TEST(UpdateAndVerifyGnmiConfigLeaf, ReturnsErrorForSetRpcFailure) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(stub, Set).WillOnce(Return(GrpcUnknownError("")));
  EXPECT_THAT(UpdateAndVerifyGnmiConfigLeaf(&stub, "system/config/boot-time",
                                            "12345678"),
              Not(IsOk()));
}

// Test with different whitespace combinations.
TEST(ParseJsonValue, ReturnsJsonValue) {
  EXPECT_THAT(ParseJsonValue("{\"name\":\"value\"}"), IsOkAndHolds("value"));
  EXPECT_THAT(ParseJsonValue("{\"name\":\"value\" }"), IsOkAndHolds("value"));
  EXPECT_THAT(ParseJsonValue("{\"name\": \"value\"}"), IsOkAndHolds("value"));
  EXPECT_THAT(ParseJsonValue("{\"name\": \"value\" }"), IsOkAndHolds("value"));
  EXPECT_THAT(ParseJsonValue("{\"name\" :\"value\"}"), IsOkAndHolds("value"));
  EXPECT_THAT(ParseJsonValue("{\"name\" :\"value\" }"), IsOkAndHolds("value"));
  EXPECT_THAT(ParseJsonValue("{\"name\" : \"value\"}"), IsOkAndHolds("value"));
  EXPECT_THAT(ParseJsonValue("{\"name\" : \"value\" }"), IsOkAndHolds("value"));
  EXPECT_THAT(ParseJsonValue("{ \"name\":\"value\"}"), IsOkAndHolds("value"));
  EXPECT_THAT(ParseJsonValue("{ \"name\":\"value\" }"), IsOkAndHolds("value"));
  EXPECT_THAT(ParseJsonValue("{ \"name\": \"value\"}"), IsOkAndHolds("value"));
  EXPECT_THAT(ParseJsonValue("{ \"name\": \"value\" }"), IsOkAndHolds("value"));
  EXPECT_THAT(ParseJsonValue("{ \"name\" :\"value\"}"), IsOkAndHolds("value"));
  EXPECT_THAT(ParseJsonValue("{ \"name\" :\"value\" }"), IsOkAndHolds("value"));
  EXPECT_THAT(ParseJsonValue("{ \"name\" : \"value\"}"), IsOkAndHolds("value"));
  EXPECT_THAT(ParseJsonValue("{ \"name\" : \"value\" }"),
              IsOkAndHolds("value"));
}

TEST(GetGnmiSystemUpTime, FailedRPCReturnsError) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "system" }
                                elem { name: "state" }
                                elem { name: "up-time" }
                              }
                              type: STATE
                              encoding: JSON_IETF)pb"),
          _))
      .WillOnce(Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  EXPECT_THAT(GetGnmiSystemUpTime(stub),
              StatusIs(absl::StatusCode::kDeadlineExceeded));
}

TEST(GetGnmiSystemUpTime, InvalidResponsesFail) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "system" }
                                elem { name: "state" }
                                elem { name: "up-time" }
                              }
                              type: STATE
                              encoding: JSON_IETF)pb"),
          _))
      // More than one notification.
      .WillOnce(
          DoAll(SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
                    R"pb(notification {
                           timestamp: 1619721040593669829
                           prefix { origin: "openconfig" target: "chassis" }
                           update {
                             path {
                               elem { name: "system" }
                               elem { name: "state" }
                               elem { name: "up-time" }
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
                           prefix { origin: "openconfig" target: "chassis" }
                           update {
                             path {
                               elem { name: "system" }
                               elem { name: "state" }
                               elem { name: "up-time" }
                             }
                             val { json_ietf_val: "{}" }
                           }
                           update {}
                         })pb")),
                Return(grpc::Status::OK)));
  EXPECT_THAT(
      GetGnmiSystemUpTime(stub),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr("openconfig-system:up-time not present in JSON")));
  EXPECT_THAT(GetGnmiSystemUpTime(stub), StatusIs(absl::StatusCode::kInternal));
}

TEST(GetGnmiSystemUpTime, EmptySubtreeReturnsNoUpTime) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "system" }
                                elem { name: "state" }
                                elem { name: "up-time" }
                              }
                              type: STATE
                              encoding: JSON_IETF)pb"),
          _))
      .WillOnce(
          DoAll(SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
                    R"pb(notification {
                           timestamp: 1619721040593669829
                           prefix { origin: "openconfig" target: "chassis" }
                           update {
                             path {
                               elem { name: "system" }
                               elem { name: "state" }
                               elem { name: "up-time" }
                             }
                             val { json_ietf_val: "{}" }
                           }
                         })pb")),
                Return(grpc::Status::OK)));
  EXPECT_THAT(
      GetGnmiSystemUpTime(stub),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr("openconfig-system:up-time not present in JSON")));
}

TEST(GetGnmiSystemUpTime, ReturnsNoUpTime) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "system" }
                                elem { name: "state" }
                                elem { name: "up-time" }
                              }
                              type: STATE
                              encoding: JSON_IETF)pb"),
          _))
      .WillOnce(DoAll(
          SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
              R"pb(notification {
                     timestamp: 1619721040593669829
                     prefix { origin: "openconfig" target: "chassis" }
                     update {
                       path {
                         elem { name: "system" }
                         elem { name: "state" }
                         elem { name: "up-time" }
                       }
                       val {
                         json_ietf_val: "{\"openconfig-system:up-time\":\"\"}"
                       }
                     }
                   })pb")),
          Return(grpc::Status::OK)));
  EXPECT_THAT(GetGnmiSystemUpTime(stub),
              StatusIs(absl::StatusCode::kInternal,
                       HasSubstr("Unable to parse up-time")));
}

TEST(GetGnmiSystemUpTime, UpTimeSuccess) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "system" }
                                elem { name: "state" }
                                elem { name: "up-time" }
                              }
                              type: STATE
                              encoding: JSON_IETF)pb"),
          _))
      .WillOnce(DoAll(
          SetArgPointee<
              2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(absl::Substitute(
              R"pb(notification {
                     timestamp: 1619721040593669829
                     prefix { origin: "openconfig" target: "chassis" }
                     update {
                       path {
                         elem { name: "system" }
                         elem { name: "state" }
                         elem { name: "up-time" }
                       }
                       val {
                         json_ietf_val: "{\"openconfig-system:up-time\":\"145274000000000\"}"
                       }
                     }
                   })pb"))),
          Return(grpc::Status::OK)));
  EXPECT_THAT(GetGnmiSystemUpTime(stub), IsOkAndHolds(145274000000000));
}

TEST(GetOcOsNetworkStackGnmiStatePathInfo, FailedRPCReturnsError) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "components" }
                                elem {
                                  name: "component"
                                  key { key: "name" value: "network_stack0" }
                                }
                                elem { name: "state" }
                                elem { name: "name" }
                              }
                              type: STATE
                              encoding: JSON_IETF)pb"),
          _))
      .WillOnce(Return(grpc::Status(grpc::StatusCode::DEADLINE_EXCEEDED, "")));
  EXPECT_THAT(
      GetOcOsNetworkStackGnmiStatePathInfo(stub, "network_stack0", "name"),
      StatusIs(absl::StatusCode::kDeadlineExceeded));
}

TEST(GetOcOsNetworkStackGnmiStatePathInfo, InvalidResponsesFail) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "components" }
                                elem {
                                  name: "component"
                                  key { key: "name" value: "network_stack0" }
                                }
                                elem { name: "state" }
                                elem { name: "name" }
                              }
                              type: STATE
                              encoding: JSON_IETF)pb"),
          _))
      // More than one notification.
      .WillOnce(
          DoAll(SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
                    R"pb(notification {
                           timestamp: 1619721040593669829
                           prefix { origin: "openconfig" target: "chassis" }
                           update {
                             path {
                               elem { name: "components" }
                               elem {
                                 name: "component"
                                 key { key: "name" value: "network_stack0" }
                               }
                               elem { name: "state" }
                               elem { name: "name" }
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
                           prefix { origin: "openconfig" target: "chassis" }
                           update {
                             path {
                               elem { name: "components" }
                               elem {
                                 name: "component"
                                 key { key: "name" value: "network_stack0" }
                               }
                               elem { name: "state" }
                               elem { name: "name" }
                             }
                             val { json_ietf_val: "{}" }
                           }
                           update {}
                         })pb")),
                Return(grpc::Status::OK)));
  EXPECT_THAT(
      GetOcOsNetworkStackGnmiStatePathInfo(stub, "network_stack0", "name"),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr("openconfig-platform:name not present in JSON")));
  EXPECT_THAT(
      GetOcOsNetworkStackGnmiStatePathInfo(stub, "network_stack0", "name"),
      StatusIs(absl::StatusCode::kInternal));
}

TEST(GetOcOsNetworkStackGnmiStatePathInfo,
     EmptySubtreeReturnsNoNetworkStackName) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "components" }
                                elem {
                                  name: "component"
                                  key { key: "name" value: "network_stack0" }
                                }
                                elem { name: "state" }
                                elem { name: "name" }
                              }
                              type: STATE
                              encoding: JSON_IETF)pb"),
          _))
      .WillOnce(
          DoAll(SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
                    R"pb(notification {
                           timestamp: 1619721040593669829
                           prefix { origin: "openconfig" target: "chassis" }
                           update {
                             path {
                               elem { name: "components" }
                               elem {
                                 name: "component"
                                 key { key: "name" value: "network_stack0" }
                               }
                               elem { name: "state" }
                               elem { name: "name" }
                             }
                             val { json_ietf_val: "{}" }
                           }
                         })pb")),
                Return(grpc::Status::OK)));
  EXPECT_THAT(
      GetOcOsNetworkStackGnmiStatePathInfo(stub, "network_stack0", "name"),
      StatusIs(absl::StatusCode::kInternal,
               HasSubstr("openconfig-platform:name not present in JSON")));
}

TEST(GetOcOsNetworkStackGnmiStatePathInfo, ReturnsNoNetworkStackName) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "components" }
                                elem {
                                  name: "component"
                                  key { key: "name" value: "network_stack0" }
                                }
                                elem { name: "state" }
                                elem { name: "name" }
                              }
                              type: STATE
                              encoding: JSON_IETF)pb"),
          _))
      .WillOnce(DoAll(
          SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
              R"pb(notification {
                     timestamp: 1619721040593669829
                     prefix { origin: "openconfig" target: "chassis" }
                     update {
                       path {
                         elem { name: "components" }
                         elem {
                           name: "component"
                           key { key: "name" value: "network_stack0" }
                         }
                         elem { name: "state" }
                         elem { name: "name" }
                       }
                       val {
                         json_ietf_val: "{\"openconfig-platform:name\":\"\"}"
                       }
                     }
                   })pb")),
          Return(grpc::Status::OK)));
  EXPECT_THAT(
      GetOcOsNetworkStackGnmiStatePathInfo(stub, "network_stack0", "name"),
      IsOkAndHolds("\"\""));
}

TEST(GetOcOsNetworkStackGnmiStatePathInfo, NetworkStackNameSuccess) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub,
      Get(_, EqualsProto(R"pb(prefix { origin: "openconfig" target: "chassis" }
                              path {
                                elem { name: "components" }
                                elem {
                                  name: "component"
                                  key { key: "name" value: "network_stack0" }
                                }
                                elem { name: "state" }
                                elem { name: "name" }
                              }
                              type: STATE
                              encoding: JSON_IETF)pb"),
          _))
      .WillOnce(DoAll(
          SetArgPointee<
              2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(absl::Substitute(
              R"pb(notification {
                     timestamp: 1619721040593669829
                     prefix { origin: "openconfig" target: "chassis" }
                     update {
                       path {
                         elem { name: "components" }
                         elem {
                           name: "component"
                           key { key: "name" value: "network_stack0" }
                         }
                         elem { name: "state" }
                         elem { name: "name" }
                       }
                       val {
                         json_ietf_val: "{\"openconfig-platform:name\":\"network_stack0\"}"
                       }
                     }
                   })pb"))),
          Return(grpc::Status::OK)));
  EXPECT_THAT(
      GetOcOsNetworkStackGnmiStatePathInfo(stub, "network_stack0", "name"),
      IsOkAndHolds("\"network_stack0\""));
}

TEST(SetPortPfcRxEnableValue, SetPfcRxEnableValueSuccess) {
  gnmi::MockgNMIStub stub;
  EXPECT_CALL(
      stub,
      Set(_,
          EqualsProto(
              R"pb(prefix { origin: "openconfig" target: "chassis" }
                   update {
                     path {
                       elem { name: "interfaces" }
                       elem {
                         name: "interface"
                         key { key: "name" value: "Ethernet8" }
                       }
                       elem { name: "ethernet" }
                       elem { name: "config" }
                       elem { name: "enable-pfc-rx" }
                     }
                     val {
                       json_ietf_val: "{\"openconfig-interfaces:enable-pfc-rx\":true}"
                     }
                   })pb"),
          _))
      .WillOnce(Return(grpc::Status::OK));
  EXPECT_OK(SetPortPfcRxEnable("Ethernet8", "true", stub));
}

TEST(GetPortPfcRxEnableValue, ReturnsPfcRxEnableValue) {
  gnmi::GetResponse response;
  constexpr char RxEnableValue[] =
      R"({"openconfig-interfaces:enable-pfc-rx":"true"})";
  gnmi::Notification *notification = response.add_notification();
  gnmi::Update *update = notification->add_update();

  *update->mutable_path() = ConvertOCStringToPath(
      "interfaces/interface[name=Ethernet8]/config/enable-pfc-rx");
  update->mutable_val()->set_json_ietf_val(RxEnableValue);
  LOG(INFO) << "response: " << response.DebugString();
  EXPECT_THAT(
      ParseGnmiGetResponse(response, "openconfig-interfaces:enable-pfc-rx"),
      IsOkAndHolds(HasSubstr("true")));
}

TEST(GetPortPfcRxEnableValue, ReturnsErrorForMalformedPfcRxEnableValue) {
  gnmi::GetResponse response;
  constexpr char RxEnableValue[] =
      R"({"openconfig-interfaces:enable-pfc-rx":"TESTERROR"})";
  gnmi::Notification *notification = response.add_notification();
  gnmi::Update *update = notification->add_update();

  *update->mutable_path() = ConvertOCStringToPath(
      "interfaces/interface[name=Ethernet8]/config/enable-pfc-rx");
  update->mutable_val()->set_json_ietf_val(RxEnableValue);
  LOG(INFO) << "response: " << response.DebugString();
  EXPECT_THAT(
      ParseGnmiGetResponse(response, "openconfig-interfaces:enable-pfc-rx"),
      IsOkAndHolds(Not(HasSubstr("true"))));
}

class MalformedJson : public testing::TestWithParam<std::string> {};

const absl::btree_map<std::string /*name*/, std::string /*text*/> &
MalformedJsonTests() {
  static const auto *const kTestCases =
      new absl::btree_map<std::string, std::string>({
          {"UnquotedName", "{name : \"value\"}"},
          {"HalfQuotedName", "{\"name : \"value\"}"},
          {"UnquotedValue", "{\"name\" : value}"},
          {"HalfQuotedValue", "{\"name\" : \"value}"},
          {"MissingSeparator", "{\"name\"\"value\"}"},
          {"MissingBraces", "\"name\":\"value\""},
          {"MissingLeftBrace", "{\"name\":\"value\""},
          {"MissingRightBrace", "\"name\":\"value\"}"},
      });
  return *kTestCases;
}

absl::btree_set<std::string> MalformedJsonTestNames() {
  absl::btree_set<std::string> test_names;
  for (const auto &[name, text] : MalformedJsonTests()) test_names.insert(name);
  return test_names;
}

TEST_P(MalformedJson, ReturnsError) {
  EXPECT_THAT(ParseJsonValue(MalformedJsonTests().at(GetParam())),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

INSTANTIATE_TEST_SUITE_P(ParseJsonNalue, MalformedJson,
                         testing::ValuesIn(MalformedJsonTestNames()),
                         [](const testing::TestParamInfo<std::string> &info) {
                           return info.param;
                         });

TEST(SetPortLoopbackMode, TestSetLoopback) {
  gnmi::MockgNMIStub stub;
  EXPECT_OK(SetPortLoopbackMode(true, "Ethernet1/1/1", stub));
  EXPECT_OK(SetPortLoopbackMode(false, "Ethernet1/1/1", stub));
}

}  // namespace
}  // namespace pins_test
