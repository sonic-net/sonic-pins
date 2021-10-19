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

#include <string>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/proto/generic_testbed.pb.h"

namespace pins_test {
namespace {

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
           {"Ethernet24", thinkit::InterfaceInfo{
                              .interface_mode = thinkit::TRAFFIC_GENERATOR,
                              .peer_interface_name = "ixia.google.com/1/1"}}});
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
                                .peer_interface = "ixia.google.com/1/1"}));
}

TEST(GenericTestbedUtils, GetAllLoopbackInterfaces) {
  EXPECT_THAT(GetAllLoopbackInterfaces(GetSutInterfaceInfo()),
              UnorderedElementsAre("Ethernet8"));
}
TEST(GenericTestbedUtils, GetAllConnectedInterfaces) {
  EXPECT_THAT(GetAllConnectedInterfaces(GetSutInterfaceInfo()),
              UnorderedElementsAre("Ethernet8", "Ethernet16", "Ethernet24"));
}

}  // namespace
}  // namespace pins_test
