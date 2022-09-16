// Copyright 2024 Google LLC
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

#ifndef GOOGLE_LIB_UTILS_GENERIC_TESTBED_UTILS_H_
#define GOOGLE_LIB_UTILS_GENERIC_TESTBED_UTILS_H_

#include <string>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/status/statusor.h"
#include "absl/types/span.h"
#include "thinkit/generic_testbed.h"

namespace pins_test {

struct InterfaceLink {
  std::string sut_interface;
  std::string peer_interface;

  bool operator==(const InterfaceLink& other) const {
    return sut_interface == other.sut_interface &&
           peer_interface == other.peer_interface;
  }
};

// Returns all the SUT interfaces in a list of interface `links`.
std::vector<std::string> GetSutInterfaces(
    absl::Span<const InterfaceLink> links);

// Returns all the peer interfaces in a list of interface `links`.
std::vector<std::string> GetPeerInterfaces(
    absl::Span<const InterfaceLink> links);

// Returns all interface links connected to a control device.
std::vector<InterfaceLink> GetAllControlLinks(
    const absl::flat_hash_map<std::string, thinkit::InterfaceInfo>&
        sut_interface_info);

// Returns all interface links connected to a traffic generator.
std::vector<InterfaceLink> GetAllTrafficGeneratorLinks(
    const absl::flat_hash_map<std::string, thinkit::InterfaceInfo>&
        sut_interface_info);

// Returns all SUT interfaces with loopbacks.
std::vector<std::string> GetAllLoopbackInterfaces(
    const absl::flat_hash_map<std::string, thinkit::InterfaceInfo>&
        sut_interface_info);

// Returns all SUT interfaces that are connected to something.
std::vector<std::string> GetAllConnectedInterfaces(
    const absl::flat_hash_map<std::string, thinkit::InterfaceInfo>&
        sut_interface_info);

// Returns the interfaces using the SUT interface info from a `GenericTestbed`.
// Pass in one of the above GetAll* functions as the first parameter.
// e.g. FromTestbed(GetAllConnectedInterfaces, testbed);
template <class InterfaceGetter>
auto FromTestbed(InterfaceGetter get_interfaces,
                 thinkit::GenericTestbed& testbed) {
  return get_interfaces(testbed.GetSutInterfaceInfo());
}

// Returns the subset of interfaces that are up on the SUT. Pass in one of the
// above GetAll* functions as the first parameter.
// e.g. GetUpInterfaces(GetAllConnectedInterfaces, testbed);
absl::StatusOr<std::vector<std::string>> GetUpInterfaces(
    decltype(GetAllConnectedInterfaces) get_interfaces,
    thinkit::GenericTestbed& testbed);

// Returns the subset of interface links that are up on the SUT. Pass in one of
// the above GetAll* functions as the first parameter.
// e.g. GetUpLinks(GetAllControlLinks, testbed);
absl::StatusOr<std::vector<InterfaceLink>> GetUpLinks(
    decltype(GetAllControlLinks) get_links, thinkit::GenericTestbed& testbed);

// Checks whether all connected ports of SUT and connected Control Switch
// interfaces are up.
absl::Status ValidateTestbedPortsUp(thinkit::GenericTestbed& testbed);

}  // namespace pins_test

#endif  // GOOGLE_LIB_UTILS_GENERIC_TESTBED_UTILS_H_
