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

#include "lib/utils/generic_testbed_utils.h"

#include <memory>
#include <string>
#include <tuple>
#include <type_traits>
#include <utility>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/memory/memory.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "grpcpp/support/status.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "proto/gnmi/gnmi.pb.h"
#include "proto/gnmi/gnmi_mock.grpc.pb.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/mock_generic_testbed.h"
#include "thinkit/mock_switch.h"
#include "thinkit/proto/generic_testbed.pb.h"

namespace pins_test {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::testing::_;
using ::testing::DoAll;
using ::testing::Return;
using ::testing::ReturnRef;
using ::testing::SetArgPointee;
using ::testing::UnorderedElementsAre;

const auto& GetSutInterfaceInfo() {
  static const auto* const kSutInterfaceInfo =
      new absl::flat_hash_map<std::string, thinkit::InterfaceInfo>(
          {{"Ethernet0",
            thinkit::InterfaceInfo{.interface_mode = thinkit::DISCONNECTED}},
           {"Ethernet8",
            thinkit::InterfaceInfo{.interface_mode = thinkit::LOOPBACK}},
           {"Ethernet16",
            thinkit::InterfaceInfo{.interface_mode = thinkit::CONTROL_INTERFACE,
                                   .peer_interface_name = "eth-1/1"}},
           {"Ethernet24",
            thinkit::InterfaceInfo{
                .interface_mode = thinkit::TRAFFIC_GENERATOR,
                .peer_interface_name = "ixia.google.com/1/1"}},
           {"Ethernet32", thinkit::InterfaceInfo{
                              .interface_mode = thinkit::TRAFFIC_GENERATOR,
                              .peer_interface_name = "ixia.google.com/1/2"}}});
  return *kSutInterfaceInfo;
}

TEST(GenericTestbedUtils, GetAllControlInterfaces) {
  EXPECT_THAT(GetAllControlInterfaces(GetSutInterfaceInfo()),
              UnorderedElementsAre(InterfacePair{.sut_interface = "Ethernet16",
                                                 .peer_interface = "eth-1/1"}));
}

TEST(GenericTestbedUtils, GetSutInterfacesFromAllControlInterfaces) {
  EXPECT_THAT(GetSutInterfaces(GetAllControlInterfaces(GetSutInterfaceInfo())),
              UnorderedElementsAre("Ethernet16"));
}

TEST(GenericTestbedUtils, GetPeerInterfacesFromAllControlInterfaces) {
  EXPECT_THAT(GetPeerInterfaces(GetAllControlInterfaces(GetSutInterfaceInfo())),
              UnorderedElementsAre("eth-1/1"));
}

TEST(GenericTestbedUtils, GetAllTrafficGeneratorInterfaces) {
  EXPECT_THAT(GetAllTrafficGeneratorInterfaces(GetSutInterfaceInfo()),
              UnorderedElementsAre(
                  InterfacePair{.sut_interface = "Ethernet24",
                                .peer_interface = "ixia.google.com/1/1"},
                  InterfacePair{.sut_interface = "Ethernet32",
                                .peer_interface = "ixia.google.com/1/2"}));
}

TEST(GenericTestbedUtils, GetAllLoopbackInterfaces) {
  EXPECT_THAT(GetAllLoopbackInterfaces(GetSutInterfaceInfo()),
              UnorderedElementsAre("Ethernet8"));
}

TEST(GenericTestbedUtils, GetAllConnectedInterfaces) {
  EXPECT_THAT(GetAllConnectedInterfaces(GetSutInterfaceInfo()),
              UnorderedElementsAre("Ethernet8", "Ethernet16", "Ethernet24",
                                   "Ethernet32"));
}

TEST(GenericTestbedUtils, FromTestbed) {
  thinkit::MockGenericTestbed testbed;
  EXPECT_CALL(testbed, GetSutInterfaceInfo())
      .WillOnce(Return(GetSutInterfaceInfo()));
  EXPECT_THAT(FromTestbed(GetAllConnectedInterfaces, testbed),
              UnorderedElementsAre("Ethernet8", "Ethernet16", "Ethernet24",
                                   "Ethernet32"));
}

constexpr absl::string_view kInterfaceUpResponse =
    R"pb(notification {
           timestamp: 1620348032128305716
           prefix { origin: "openconfig" }
           update {
             path {
               elem { name: "interfaces" }
               elem {
                 name: "interface"
                 key { key: "name" value: "EthernetN" }
               }
               elem { name: "state" }
               elem { name: "oper-status" }
             }
             val {
               json_ietf_val: "{\"openconfig-interfaces:oper-status\":{\"oper-status\":\"UP\"}}"
             }
           }
         })pb";

constexpr absl::string_view kInterfaceDownResponse =
    R"pb(notification {
           timestamp: 1620348032128305716
           prefix { origin: "openconfig" }
           update {
             path {
               elem { name: "interfaces" }
               elem {
                 name: "interface"
                 key { key: "name" value: "EthernetN" }
               }
               elem { name: "state" }
               elem { name: "oper-status" }
             }
             val {
               json_ietf_val: "{\"openconfig-interfaces:oper-status\":{\"oper-status\":\"DOWN\"}}"
             }
           }
         })pb";

TEST(GenericTestbedUtils, GetUpInterfaces) {
  thinkit::MockGenericTestbed testbed;
  EXPECT_CALL(testbed, GetSutInterfaceInfo())
      .WillOnce(Return(GetSutInterfaceInfo()));
  thinkit::MockSwitch sut;
  EXPECT_CALL(testbed, Sut()).WillOnce(ReturnRef(sut));
  EXPECT_CALL(sut, CreateGnmiStub())
      .WillOnce(
          []() -> absl::StatusOr<std::unique_ptr<gnmi::gNMI::StubInterface>> {
            auto gnmi_stub = absl::make_unique<gnmi::MockgNMIStub>();
            // By default most interfaces are up.
            ON_CALL(*gnmi_stub, Get(_, _, _))
                .WillByDefault(DoAll(
                    SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
                        kInterfaceUpResponse)),
                    Return(grpc::Status::OK)));
            // Have Ethernet32 be down.
            ON_CALL(*gnmi_stub,
                    Get(_,
                        EqualsProto(
                            R"pb(type: STATE
                                 prefix { origin: "openconfig" }
                                 path {
                                   elem { name: "interfaces" }
                                   elem {
                                     name: "interface"
                                     key { key: "name" value: "Ethernet32" }
                                   }
                                   elem { name: "state" }
                                   elem { name: "oper-status" }
                                 }
                            )pb"),
                        _))
                .WillByDefault(DoAll(
                    SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
                        kInterfaceDownResponse)),
                    Return(grpc::Status::OK)));
            return std::move(gnmi_stub);
          });

  // GetAllConnectedInterfaces will return Ethernet8, Ethernet16, Ethernet24,
  // and Ethernet32, but since Ethernet32 is down, it shouldn't be present.
  EXPECT_THAT(GetUpInterfaces(GetAllConnectedInterfaces, testbed),
              IsOkAndHolds(UnorderedElementsAre("Ethernet8", "Ethernet16",
                                                "Ethernet24")));
}

TEST(GenericTestbedUtils, GetUpInterfacePairs) {
  thinkit::MockGenericTestbed testbed;
  EXPECT_CALL(testbed, GetSutInterfaceInfo())
      .WillOnce(Return(GetSutInterfaceInfo()));
  thinkit::MockSwitch sut;
  EXPECT_CALL(testbed, Sut()).WillOnce(ReturnRef(sut));
  EXPECT_CALL(sut, CreateGnmiStub())
      .WillOnce(
          []() -> absl::StatusOr<std::unique_ptr<gnmi::gNMI::StubInterface>> {
            auto gnmi_stub = absl::make_unique<gnmi::MockgNMIStub>();
            // By default most interfaces are up.
            ON_CALL(*gnmi_stub, Get(_, _, _))
                .WillByDefault(DoAll(
                    SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
                        kInterfaceUpResponse)),
                    Return(grpc::Status::OK)));
            // Have Ethernet32 be down.
            ON_CALL(*gnmi_stub,
                    Get(_,
                        EqualsProto(
                            R"pb(type: STATE
                                 prefix { origin: "openconfig" }
                                 path {
                                   elem { name: "interfaces" }
                                   elem {
                                     name: "interface"
                                     key { key: "name" value: "Ethernet32" }
                                   }
                                   elem { name: "state" }
                                   elem { name: "oper-status" }
                                 }
                            )pb"),
                        _))
                .WillByDefault(DoAll(
                    SetArgPointee<2>(gutil::ParseProtoOrDie<gnmi::GetResponse>(
                        kInterfaceDownResponse)),
                    Return(grpc::Status::OK)));
            return std::move(gnmi_stub);
          });

  // GetAllTrafficGeneratorInterfaces will return Ethernet24 and Ethernet32, but
  // since Ethernet32 is down, it shouldn't be present.
  EXPECT_THAT(GetUpInterfacePairs(GetAllTrafficGeneratorInterfaces, testbed),
              IsOkAndHolds(UnorderedElementsAre(
                  InterfacePair{.sut_interface = "Ethernet24",
                                .peer_interface = "ixia.google.com/1/1"})));
}

}  // namespace
}  // namespace pins_test
