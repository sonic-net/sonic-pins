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
#include "absl/types/span.h"
#include "thinkit/generic_testbed.h"

namespace pins_test {

struct InterfacePair {
  std::string sut_interface;
  std::string peer_interface;

  bool operator==(const InterfacePair& other) const {
    return sut_interface == other.sut_interface &&
           peer_interface == other.peer_interface;
  }
};

std::vector<std::string> GetSutInterfaces(
    absl::Span<const InterfacePair> interface_pairs);

std::vector<std::string> GetPeerInterfaces(
    absl::Span<const InterfacePair> interface_pairs);

std::vector<InterfacePair> GetAllControlInterfaces(
    const absl::flat_hash_map<std::string, thinkit::InterfaceInfo>&
        sut_interface_info);

std::vector<InterfacePair> GetAllTrafficGeneratorInterfaces(
    const absl::flat_hash_map<std::string, thinkit::InterfaceInfo>&
        sut_interface_info);

std::vector<std::string> GetAllLoopbackInterfaces(
    const absl::flat_hash_map<std::string, thinkit::InterfaceInfo>&
        sut_interface_info);

std::vector<std::string> GetAllConnectedInterfaces(
    const absl::flat_hash_map<std::string, thinkit::InterfaceInfo>&
        sut_interface_info);

}  // namespace pins_test

#endif  // GOOGLE_LIB_UTILS_GENERIC_TESTBED_UTILS_H_
