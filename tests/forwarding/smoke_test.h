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

#ifndef PINS_TESTS_FORWARDING_SMOKE_TEST_H_
#define PINS_TESTS_FORWARDING_SMOKE_TEST_H_

#include <optional>

#include "tests/forwarding/mirror_blackbox_test_fixture.h"
#include "thinkit/mirror_testbed_fixture.h"

namespace pins_test {

struct SmokeTestParams {
  // Using a shared_ptr because parameterized tests require objects to be
  // copyable.
  std::shared_ptr<thinkit::MirrorTestbedInterface> mirror_testbed;
  // The test assumes that the switch is pre-configured if no `gnmi_config` is
  // given (default), or otherwise pushes the given config before starting.
  std::optional<std::string> gnmi_config;
  std::optional<p4::config::v1::P4Info> p4info;
  // Use on platforms that don't support GRE tunnels to avoid using them in
  // tests.
  bool does_not_support_gre_tunnels;
  // Use on platforms that don't support IPv6 entries with multicast destination
  // IP address.
  bool does_not_support_ipv6_entries_multicast_dest_ip;
};

class SmokeTestFixture : public testing::TestWithParam<SmokeTestParams> {
 public:
  void SetUp() override { GetParam().mirror_testbed->SetUp(); }
  void TearDown() override { GetParam().mirror_testbed->TearDown(); }
};

}  // namespace pins_test

#endif // PINS_TESTS_FORWARDING_SMOKE_TEST_H_
