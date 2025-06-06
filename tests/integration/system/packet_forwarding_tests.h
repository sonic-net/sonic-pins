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

#ifndef PINS_TESTS_INTEGRATION_SYSTEM_PACKET_FORWARDING_TESTS_H_
#define PINS_TESTS_INTEGRATION_SYSTEM_PACKET_FORWARDING_TESTS_H_

#include <optional>

#include "p4/config/v1/p4info.pb.h"
#include "thinkit/generic_testbed_fixture.h"

namespace pins_test {

// Parameters for the PacketForwardingTestFixture.
struct PacketForwardingTestParams {
  // For access to the SUTs.
  thinkit::GenericTestbedInterface* testbed_interface;
  // If true, push the P4Info to the SUT.
  bool push_p4_info;
  std::optional<p4::config::v1::P4Info> p4_info;
};

class PacketForwardingTestFixture
    : public thinkit::GenericTestbedFixture<PacketForwardingTestParams> {};

} // namespace pins_test

#endif // PINS_TESTS_INTEGRATION_SYSTEM_PACKET_FORWARDING_TESTS_H_
