// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#ifndef GOOGLE_TESTS_THINKIT_GNMI_INTERFACE_TESTS_H_
#define GOOGLE_TESTS_THINKIT_GNMI_INTERFACE_TESTS_H_

#include "absl/container/flat_hash_map.h"
#include "absl/strings/string_view.h"
#include "thinkit/ssh_client.h"
#include "thinkit/switch.h"

namespace pins_test {

// Test port admin_status related GNMI config and state paths.
void TestGnmiInterfaceConfigSetAdminStatus(thinkit::Switch& sut,
                                           absl::string_view if_name);

// Test GNMI component config and state paths.
void TestGnmiPortComponentPaths(
    thinkit::SSHClient& ssh_client, thinkit::Switch& sut,
    absl::flat_hash_map<std::string, std::string>& expected_port_index_map);

// Test port-speed GNMI config and state paths.
// The test expects that auto-negotiation has been disabled for the given port.
void TestGnmiInterfaceConfigSetPortSpeed(
    thinkit::Switch& sut, absl::string_view if_name,
    const std::vector<int>& supported_speeds);

// Test port Id GNMI config and state paths.
void TestGnmiInterfaceConfigSetId(thinkit::Switch& sut,
                                  absl::string_view if_name, const int id);
}  // namespace pins_test

#endif  // GOOGLE_TESTS_THINKIT_GNMI_INTERFACE_TESTS_H_
